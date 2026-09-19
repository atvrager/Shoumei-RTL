/-
Peripherals/GPIOProofs.lean - Structural proofs for GPIO
-/

import Shoumei.Peripherals.GPIO

namespace Shoumei.Peripherals

open Shoumei

theorem gpio_name : gpioCircuit.name = "GPIO" := by rfl

theorem gpio_instances : gpioCircuit.instances.length = 3 := by native_decide

theorem gpio_inputs_positive : gpioCircuit.inputs.length > 0 := by native_decide

theorem gpio_outputs_positive : gpioCircuit.outputs.length > 0 := by native_decide

theorem gpio_gates_positive : gpioCircuit.gates.length > 0 := by native_decide

end Shoumei.Peripherals
