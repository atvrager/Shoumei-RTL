// Shoumei Codegen V2 Primitive Helpers
// Hand-written infrastructure for generated Chisel code.

package shoumei

import chisel3._

/** DFF with async reset to zero. Thin wrapper around RegInit. */
object ShoumeiReg {

  /** Multi-bit register (returns plain UInt). */
  def apply(width: Int, clock: Clock, reset: AsyncReset): UInt =
    withClockAndReset(clock, reset)(RegInit(0.U(width.W)))

  /** Single-bit register (returns Bool). */
  def bool(clock: Clock, reset: AsyncReset): Bool =
    withClockAndReset(clock, reset)(RegInit(false.B))
}

/** DFF with async reset to a custom init value. Used for DFF_SET bits. */
object ShoumeiRegInit {

  /** Multi-bit register with custom init value (returns plain UInt). */
  def apply(width: Int, initVal: BigInt, clock: Clock, reset: AsyncReset): UInt =
    withClockAndReset(clock, reset)(RegInit(initVal.U(width.W)))

  /** Single-bit register with init to 1 (returns Bool). */
  def bool(clock: Clock, reset: AsyncReset): Bool =
    withClockAndReset(clock, reset)(RegInit(true.B))
}

/** Memory primitives. */
object ShoumeiMem {

  /** Async-read memory (register file, small arrays). */
  def apply(depth: Int, width: Int): Mem[UInt] =
    Mem(depth, UInt(width.W))

  /** Sync-read memory (SRAM, block RAM). */
  def syncRead(depth: Int, width: Int): SyncReadMem[UInt] =
    SyncReadMem(depth, UInt(width.W))
}
