/-
Peripherals/UARTProofs.lean - Structural proofs for UART
-/

import Shoumei.Peripherals.UART

namespace Shoumei.Peripherals

open Shoumei

theorem uart_name : uartCircuit.name = "UART" := by rfl

theorem uart_instances : uartCircuit.instances.length = 3 := by native_decide

theorem uart_inputs_positive : uartCircuit.inputs.length > 0 := by native_decide

theorem uart_outputs_positive : uartCircuit.outputs.length > 0 := by native_decide

theorem uart_gates_positive : uartCircuit.gates.length > 0 := by native_decide

end Shoumei.Peripherals
