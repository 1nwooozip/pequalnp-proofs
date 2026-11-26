import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22769 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1947503 : ℕ).testBit (6 * u.val + v.val)) 14) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[
    ⟨.or, [7, 9]⟩,
    ⟨.and, [0, 10]⟩,
    ⟨.or, [1, 2]⟩,
    ⟨.or, [8, 7]⟩,
    ⟨.and, [12, 13]⟩,
    ⟨.or, [0, 3]⟩,
    ⟨.or, [1, 15]⟩,
    ⟨.and, [16, 6]⟩,
    ⟨.or, [2, 15]⟩,
    ⟨.and, [18, 5]⟩,
    ⟨.or, [19, 14]⟩,
    ⟨.or, [4, 17]⟩,
    ⟨.or, [11, 20]⟩,
    ⟨.or, [21, 22]⟩], 23⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, C]
  · decide
