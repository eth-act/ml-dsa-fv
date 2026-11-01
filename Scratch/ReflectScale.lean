import Scratch.Reflection
namespace ReflectPrototype
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def repeated (n : Nat) : List Op := (List.replicate n program).flatten
def nested : Nat → Term
  | 0 => .var 0
  | n + 1 => delta (nested n) (.var 6)

-- Stress the representation with repeated copies of the actual delta-swap
-- instruction pattern. This is NOT an additional real artifact block.
set_option trace.profiler true in
theorem six : run (repeated 6) input = some (nested 6 :: input.tail) := by
  decide +kernel

set_option trace.profiler true in
theorem twelve : run (repeated 12) input = some (nested 12 :: input.tail) := by
  decide +kernel

set_option trace.profiler true in
theorem twentyEight : run (repeated 28) input = some (nested 28 :: input.tail) := by
  decide +kernel

-- Negative controls: a changed mask index and stack underflow must not verify.
example : run program input ≠ some (delta (.var 0) (.var 7) :: input.tail) := by
  decide +kernel
example : run [.bin .xor] [.var 0] = none := by decide +kernel

-- Exact capacity boundary: maximum pre-instruction prefix depth is 13.
example : Safe 1010 program input := by
  simp [Safe, program, input, step, List.range_succ]
example : ¬ Safe 1011 program input := by
  simp [Safe, program, input, step, List.range_succ]
end ReflectPrototype
