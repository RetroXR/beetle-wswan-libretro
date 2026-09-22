/* Mednafen - Multi-system Emulator
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

/* WonderSwan serial port emulation, ported from upstream comm.cpp.
 *
 * Upstream's optional WonderFence child-process bridge is left out (it is
 * unix-only and non-deterministic). In its place the port joins the link bus a
 * frontend hosts through RETRO_ENVIRONMENT_GET_LINK_INTERFACE
 * (libretro/RetroArch#19454), which is how two WonderSwans in one process are
 * joined by a Communication Cable.
 *
 * WHAT CROSSES. The EXT port is a plain UART, 8N1 at 9600 or 38400 baud, and
 * both ends are the same hardware: no master, no shared clock, each unit shifts
 * its own bytes out at its own rate. So there is one message, a byte, stamped
 * with the tick its stop bit leaves the wire, and the far end latches it when
 * its own clock reaches that tick. A byte is 10 bit times: 3200 CPU cycles at
 * 9600 baud, 800 at 38400.
 *
 * Nothing cabled behaves exactly as before: a transmitted byte completes
 * immediately and raises the serial-send interrupt, and nothing is received.
 *
 * TIME. The link clock is the CPU's 3.072 MHz counted as 256 cycles a scanline,
 * not read from v30mz_timestamp, which restarts every frame and overruns a line
 * by its last instruction. The port is serviced once a line, so a line is the
 * only clock this code has to agree with, and counting lines makes it the same
 * on every peer replaying the same inputs. */

#include <string.h>

#include "wswan.h"
#include "interrupt.h"
#include "comm.h"
#include "link_interface.h"
#include <libretro.h>

#include "../state_inline.h"

#define LINK_PROTOCOL   "ws-sio-1"
#define LINK_CLOCK      3072000
#define LINE_CYCLES     256
#define BYTE_SLOW       3200  /* 10 bits at 9600 baud */
#define BYTE_FAST       800   /* 10 bits at 38400 baud */

/* The horizon this port promises, and how far it asks to run between
 * rendezvous. Both are the shortest byte: anything this unit originates lands
 * at least a byte-time after its transmit starts, so the promise is free and
 * delays nothing at either rate. */
#define LINK_HORIZON    BYTE_FAST
#define LINK_GRAIN      BYTE_FAST

#define PENDING_MAX     32

extern retro_log_printf_t log_cb;

static uint8 Control;
static uint8 SendBuf, RecvBuf;
static bool SendLatched, RecvLatched;
static bool Overrun;

/* A byte on its way out, and the tick its stop bit leaves. */
static bool Sending;
static uint64 SendDone;

static const struct retro_link_interface *link_if;
static retro_link_port_t *link_handle;
static uint64 link_now;
static uint64 link_grant;
static uint64 link_safe;
static bool link_paired;

/* Bytes that crossed since the cable was last seated, for the WARN lines that
 * say so (the frontend drops anything quieter). Logged at 1, 10, 100, ... so a
 * long session costs a handful of lines. */
static uint32 link_rx, link_tx, link_rx_next, link_tx_next;
static uint32 link_ovr, link_ovr_next, link_drop, link_drop_next;

/* Bytes from the far end, held until this unit's clock reaches the tick each
 * was stamped with. WHEN one arrives is a wall-clock accident; when its tick
 * comes round is not, and acting on the second is what makes a replay agree. */
static struct
{
   uint64 tick;
   uint8 byte;
} pending[PENDING_MAX];
static unsigned pending_count;

static uint64 ByteTicks(void)
{
   return (Control & 0x40) ? BYTE_FAST : BYTE_SLOW;
}

static void RefreshPeers(void)
{
   unsigned count = 0;
   int self = link_if->peers(link_handle, &count);

   /* The Communication Cable joins two units. A bus of three is not a cable
    * that exists, so it carries nothing rather than something no real pair of
    * machines could produce. */
   bool paired = self >= 0 && count == 2;

   if (paired != link_paired)
   {
      link_rx = link_tx = 0;
      link_rx_next = link_tx_next = 1;
      link_ovr = link_drop = 0;
      link_ovr_next = link_drop_next = 1;
      if (log_cb)
         log_cb(RETRO_LOG_WARN, "[ws-sio] %s (bus of %u)\n",
               paired ? "cabled" : "uncabled", count);
   }
   link_paired = paired;
}

static void Count(uint32 *n, uint32 *next, const char *what)
{
   if (++*n == *next)
   {
      if (log_cb)
         log_cb(RETRO_LOG_WARN, "[ws-sio] %u bytes %s\n", *n, what);
      *next *= 10;
   }
}

static void Pump(void)
{
   uint8 buf[4];
   uint64_t tick;
   unsigned from;
   size_t len = sizeof(buf);

   while (link_if->recv(link_handle, &tick, &from, buf, &len))
   {
      if (len >= 1 && pending_count >= PENDING_MAX)
         Count(&link_drop, &link_drop_next, "DROPPED, queue full");
      if (len >= 1 && pending_count < PENDING_MAX)
      {
         unsigned i = pending_count++;
         while (i > 0 && pending[i - 1].tick > tick)
         {
            pending[i] = pending[i - 1];
            i--;
         }
         pending[i].tick = tick;
         pending[i].byte = buf[0];
      }
      len = sizeof(buf);
   }
}

static void Rendezvous(void)
{
   for (;;)
   {
      uint32_t wake = 0;
      uint64 got;
      uint64 safe = link_now + LINK_HORIZON;

      if (safe < link_safe)
         safe = link_safe;
      link_safe = safe;

      got = link_if->advance(link_handle, link_now, safe,
            link_now + LINK_GRAIN, &wake);

      if (wake & (RETRO_LINK_WAKE_TOPOLOGY | RETRO_LINK_WAKE_DETACHED))
         RefreshPeers();
      if (wake & RETRO_LINK_WAKE_MESSAGE)
         Pump();

      if (got == RETRO_LINK_UNBOUNDED)
      {
         /* Nothing bounds this unit. Look again a grain from now, so a cable
          * seated later is noticed within a few lines. */
         link_grant = link_now + LINK_GRAIN;
         return;
      }
      if (got > link_now)
      {
         link_grant = got;
         return;
      }
      /* A wake that granted no clock: ask again at once. */
   }
}

/* The send line is a level: asserted while the port is on and its buffer is
 * empty. */
static void SendLevel(void)
{
   WSwan_InterruptAssert(WSINT_SERIAL_SEND, (Control & 0x80) && !SendLatched);
}

static void Receive(uint8 byte)
{
   if (!(Control & 0x80))
      return;

   if (RecvLatched)
   {
      /* The byte in the buffer is kept; the one behind it is lost. */
      Overrun = true;
      Count(&link_ovr, &link_ovr_next, "lost to overrun");
      return;
   }

   Count(&link_rx, &link_rx_next, "received");
   RecvBuf = byte;
   RecvLatched = true;
   WSwan_InterruptAssert(WSINT_SERIAL_RECV, RecvLatched);
}

void Comm_SetLinkInterface(const struct retro_link_interface *link)
{
   link_if = link;
}

void Comm_LinkStart(void)
{
   if (!link_if || link_handle)
      return;

   link_handle = link_if->attach(0, LINK_PROTOCOL, LINK_CLOCK);
   link_grant = link_now;
   link_safe = link_now;
   link_paired = false;
   pending_count = 0;
   if (link_handle)
      RefreshPeers();
}

void Comm_LinkStop(void)
{
   if (link_handle)
      link_if->detach(link_handle);
   link_handle = NULL;
   link_paired = false;
   pending_count = 0;
}

void Comm_Reset(void)
{
   SendBuf = 0x00;
   RecvBuf = 0x00;

   SendLatched = false;
   RecvLatched = false;
   Overrun = false;
   Sending = false;

   Control = 0x00;
   SendLevel();

   /* link_now is NOT reset: the bus reads a clock going backwards as a peer
    * that ran away, and a reset machine is still on the same cable. */

   WSwan_InterruptAssert(WSINT_SERIAL_RECV, RecvLatched);
}

/* Called once per scanline from wsExecuteLine(), after the line has run. */
void Comm_Process(void)
{
   link_now += LINE_CYCLES;

   if (link_handle)
   {
      if (link_now >= link_grant)
         Rendezvous();
      Pump();

      while (pending_count > 0 && pending[0].tick <= link_now)
      {
         uint8 byte = pending[0].byte;
         pending_count--;
         memmove(&pending[0], &pending[1], pending_count * sizeof(pending[0]));
         if (link_paired)
            Receive(byte);
      }
   }

   if (!(Control & 0x80))
      return;

   if (SendLatched && !Sending)
   {
      if (!link_paired)
      {
         /* No cable; the byte leaves the shift register immediately. */
         SendLatched = false;
         SendLevel();
         return;
      }

      Sending = true;
      SendDone = link_now + ByteTicks();
      if (SendDone < link_safe)
         SendDone = link_safe;
      link_if->send(link_handle, SendDone, RETRO_LINK_BROADCAST, &SendBuf, 1);
      Count(&link_tx, &link_tx_next, "sent");
   }

   if (Sending && link_now >= SendDone)
   {
      Sending = false;
      SendLatched = false;
      SendLevel();
   }
}

uint8 Comm_Read(uint8 A)
{
   if(A == 0xB1)
   {
      RecvLatched = false;
      WSwan_InterruptAssert(WSINT_SERIAL_RECV, RecvLatched);

      return(RecvBuf);
   }
   else if(A == 0xB3)
   {
      uint8 ret = Control & 0xF0;

      if((Control & 0x80) && !SendLatched)
         ret |= 0x4;

      if(Overrun)
         ret |= 0x2;

      if(RecvLatched)
         ret |= 0x1;

      return(ret);
   }

   return(0x00);
}

void Comm_Write(uint8 A, uint8 V)
{
   if(A == 0xB1)
   {
      if((Control & 0x80) && !SendLatched)
      {
         SendBuf = V;
         SendLatched = true;
         SendLevel();
      }
   }
   else if(A == 0xB3)
   {
      /* Bit 5 clears the overrun flag. */
      if(V & 0x20)
         Overrun = false;
      /* Switching the port off empties it. Games reset the port to flush it
       * before a handshake, and a byte left over from before the reset is read
       * as the answer to the next one. */
      if(!(V & 0x80))
      {
         RecvLatched = false;
         Overrun = false;
         WSwan_InterruptAssert(WSINT_SERIAL_RECV, RecvLatched);
      }
      Control = V & 0xF0;
      SendLevel();
   }
}

int Comm_StateAction(StateMem *sm, int load, int data_only)
{
   /* A byte in flight is saved as how long it has left, never as a tick: the
    * link clock belongs to this session, and a state is loaded into another. */
   uint32 SendLeft = (Sending && SendDone > link_now) ? (uint32)(SendDone - link_now) : 0;

   SFORMAT StateRegs[] =
   {
      SFVARN(SendBuf, "SendBuf"),
      SFVARN(RecvBuf, "RecvBuf"),

      SFVARN_BOOL(SendLatched, "SendLatched"),
      SFVARN_BOOL(RecvLatched, "RecvLatched"),

      SFVARN(Control, "Control"),

      SFVARN_BOOL(Overrun, "Overrun"),
      SFVARN_BOOL(Sending, "Sending"),
      SFVARN(SendLeft, "SendLeft"),
      { 0, 0, 0, 0 }
   };

   if(!MDFNSS_StateAction(sm, load, data_only, StateRegs, "COMM", false))
      return 0;

   if(load)
   {
      SendDone = link_now + SendLeft;
      WSwan_InterruptAssert(WSINT_SERIAL_RECV, RecvLatched);
      SendLevel();
   }

   return 1;
}
