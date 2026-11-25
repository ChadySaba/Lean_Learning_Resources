import Mathlib
-- ▶ Block 399 · Chapter 23: Metaprogramming · Level 1: notation · page 186 (French edition: page 194)
open Filter Topology

notation:50 f " ⇝ " l => Tendsto f atTop (𝓝 l)

example : (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) ⇝ 0 :=
  tendsto_one_div_add_atTop_nhds_zero_nat

#check (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) ⇝ 0
-- (fun n ↦ 1 / (↑n + 1)) ⇝ 0 : Prop
