import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.Girth

theorem PEqualNP.Outside.R_meta_6698_2 :
  (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj]
      (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),
    have x6 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate :=
      fun (x6 : Fin x1) =>
        List.filter (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) =>
          (List.take (bif x7.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x7.inputs).contains ↑x6) x5.gates;
    (∀ (x7 : Fin x1), x2.degree x7 = if x7 ∈ x4 then (0 : ℕ) else (3 : ℕ)) →
    x2 ≠ ⊥ →
    PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 →
    PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 →
    (9 * x4ᶜ.card ≤ 4 * ∑ v ∈ x4ᶜ, (x6 v).length) →
    ∃ x14 ∉ x4, ∃ (x15 : ℕ), x15 + (4 : ℕ) ≤ x5.size ∧
      PEqualNP.MetaComplexity.HasCircuitSize x1
        (fun (x16 : Fin x1 → Bool) => PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 (Function.update x16 x14 Bool.false)) x15) →
  (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj]
      (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),
    have x6 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate :=
      fun (x6 : Fin x1) =>
        List.filter (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) =>
          (List.take (bif x7.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x7.inputs).contains ↑x6) x5.gates;
    (∀ (x7 : Fin x1), x2.degree x7 = if x7 ∈ x4 then (0 : ℕ) else (3 : ℕ)) →
    (7 : ℕ∞) ≤ x2.egirth →
    x2 ≠ ⊥ →
    PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 →
    PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 →
    (∀ x12 ∉ x4, (x6 x12).length ≤ (3 : ℕ) ∧ ((x6 x12).length = (3 : ℕ) → ∀ x15 ∈ x6 x12, x15.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →
    (∀ x13 ∉ x4, ∀ (x15 x16 : Finset (Fin x1)), (x15 ∪ x16).card ≤ (2 : ℕ) → x13 ∉ x15 ∪ x16 → x2.IsIndepSet ↑x15 → Disjoint x4 x15 → Disjoint x15 x16 → ¬∀ x22 ∈ x6 x13, ∃ (x24 : Fin x1), ↑x24 ∈ x22.inputs ∧ (x24 ∈ x15 ∧ x22.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ x24 ∈ x16 ∧ x22.op = PEqualNP.CircuitLowerBounds.GateOp.and)) →
    (4 * ∑ v ∈ x4ᶜ, (x6 v).length < 9 * x4ᶜ.card) →
    ∃ x14 ∉ x4, ∃ (x15 : ℕ), x15 + (4 : ℕ) ≤ x5.size ∧
      PEqualNP.MetaComplexity.HasCircuitSize x1
        (fun (x16 : Fin x1 → Bool) => PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 (Function.update x16 x14 Bool.false)) x15) →
  ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj]
      (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),
    have x6 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate :=
      fun (x6 : Fin x1) =>
        List.filter (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) =>
          (List.take (bif x7.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x7.inputs).contains ↑x6) x5.gates;
    (∀ (x7 : Fin x1), x2.degree x7 = if x7 ∈ x4 then (0 : ℕ) else (3 : ℕ)) →
    (7 : ℕ∞) ≤ x2.egirth →
    x2 ≠ ⊥ →
    PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 →
    PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 →
    (∀ x12 ∉ x4, (x6 x12).length ≤ (3 : ℕ) ∧ ((x6 x12).length = (3 : ℕ) → ∀ x15 ∈ x6 x12, x15.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →
    (∀ x13 ∉ x4, ∀ (x15 x16 : Finset (Fin x1)), (x15 ∪ x16).card ≤ (2 : ℕ) → x13 ∉ x15 ∪ x16 → x2.IsIndepSet ↑x15 → Disjoint x4 x15 → Disjoint x15 x16 → ¬∀ x22 ∈ x6 x13, ∃ (x24 : Fin x1), ↑x24 ∈ x22.inputs ∧ (x24 ∈ x15 ∧ x22.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ x24 ∈ x16 ∧ x22.op = PEqualNP.CircuitLowerBounds.GateOp.and)) →
    ∃ x14 ∉ x4, ∃ (x15 : ℕ), x15 + (4 : ℕ) ≤ x5.size ∧
      PEqualNP.MetaComplexity.HasCircuitSize x1
        (fun (x16 : Fin x1 → Bool) => PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 (Function.update x16 x14 Bool.false)) x15 := by
  intro dense sparse n G inst A C
  dsimp only
  intro deg girth nonempty minC computes readers unmaskable
  let direct (v : Fin n) := C.gates.filter fun g =>
    (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
  by_cases high : 9 * Aᶜ.card ≤ 4 * ∑ v ∈ Aᶜ, (direct v).length
  · exact dense n G A C deg nonempty minC computes high
  · exact sparse n G A C deg girth nonempty minC computes readers unmaskable (Nat.lt_of_not_ge high)
