import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.ReadTwo

theorem PEqualNP.Outside.R_meta_8145_2
    (trace : ∀ (n : ℕ) (C : Circuit) (x : Fin n → Bool),
    Monotone2 C → ReadsBack n C →
    (∃ j : Fin C.gates.length, (C.gates.get j).op = GateOp.and ∧
      (C.wires (List.ofFn x)).getD (n + j.val) false = true) →
    ∃ j : Fin C.gates.length, (C.gates.get j).op = GateOp.and ∧
      ∀ w ∈ (C.gates.get j).inputs, ∃ k : Fin n, x k = true ∧ orp C n k.val w)
    (geometry : let offsets : Finset (Fin 13) := {0, 1, 3, 9}
    let correct := fun C : Circuit => Monotone2 C ∧ ReadsBack 26 C ∧
      ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 13, p - l ∈ offsets ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
    ∀ C : Circuit, correct C → (∀ D : Circuit, correct D → C.size ≤ D.size) →
      (∃ j : Fin C.gates.length, (C.gates.get j).op = GateOp.and ∧
        ∀ w ∈ (C.gates.get j).inputs, orp C 26 0 w ∨ orp C 26 1 w) → 64 ≤ C.size) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : (Fin (26 : ℕ) → Bool) → Prop := fun (x2 : Fin (26 : ℕ) → Bool) => ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x3 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x3 ∧ ∀ (x4 : Fin (26 : ℕ) → Bool), x3.eval (List.ofFn x4) = Bool.true ↔ x2 x4; have x4 : Fin (26 : ℕ) → Fin (26 : ℕ) → Fin (26 : ℕ) → Bool := fun (x4 x5 x6 : Fin (26 : ℕ)) => Decidable.decide (x6 = x4 ∨ x6 = x5); have x5 : PEqualNP.CircuitLowerBounds.Circuit → Fin (26 : ℕ) → Fin (26 : ℕ) → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 x7 : Fin (26 : ℕ)) => ∃ (x8 : Fin x5.gates.length), (x5.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x5.wires (List.ofFn (x4 x6 x7))).getD ((26 : ℕ) + ↑x8) Bool.false = Bool.true; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), x3 x6 → (∀ (x8 : PEqualNP.CircuitLowerBounds.Circuit), x3 x8 → x6.size ≤ x8.size) → x5 x6 (0 : Fin (26 : ℕ)) (1 : Fin (26 : ℕ)) → (64 : ℕ) ≤ x6.size := by
  intro offsets target correct pair fires C hC least lit
  apply @geometry C hC least
  obtain ⟨j, hop, paths⟩ := trace 26 C (pair 0 1) hC.1 hC.2.1 lit
  refine ⟨j, hop, ?_⟩
  intro w hw
  obtain ⟨k, hk, path⟩ := paths w hw
  change decide (k = 0 ∨ k = 1) = true at hk
  rcases of_decide_eq_true hk with rfl | rfl
  · exact Or.inl path
  · exact Or.inr path
