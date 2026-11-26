import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18617_aux

open PEqualNP.CircuitLowerBounds

def g (o : GateOp) (a b : ℕ) : Gate := ⟨o, [a, b]⟩

def C : Circuit := ⟨[g .or 13 24, g .or 27 18, g .and 28 1,
  g .or 15 25, g .or 30 19, g .and 31 2,
  g .or 17 16, g .or 33 21, g .and 34 4,
  g .or 23 22, g .or 36 20, g .and 37 10,
  g .or 29 32, g .or 39 35, g .or 40 38], 41⟩

theorem ev (x : Fin 26 → Bool) : C.eval (List.ofFn x ++ [x 1 || x 2]) =
    ((x 13 || x 24 || x 18) && x 1 || (x 15 || x 25 || x 19) && x 2 ||
      (x 17 || x 16 || x 21) && x 4 || (x 23 || x 22 || x 20) && x 10) := by
  simp [C, g, Circuit.eval, Circuit.wires, GateOp.eval, List.ofFn_succ]

end PEqualNP.Outside.L_meta_18617_aux

theorem PEqualNP.Outside.L_meta_18617 : ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (15 : ℕ) ∧ (27 : ℕ) ≤ x1.output ∧ x1.output < (27 : ℕ) + x1.size ∧ PEqualNP.TopForm.IsAO2 (27 : ℕ) x1 ∧ (∀ x2 ∈ x1.gates, x2.inputs.Nodup) ∧ ∀ (x2 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x2 ++ [x2 (1 : Fin (26 : ℕ)) || x2 (2 : Fin (26 : ℕ))]) = Bool.true ↔ ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x3 ∈ [(1 : Fin (13 : ℕ)), (2 : Fin (13 : ℕ)), (4 : Fin (13 : ℕ)), (10 : Fin (13 : ℕ))] ∧ x4 ≠ (1 : Fin (13 : ℕ)) ∧ (x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ))) ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true := by
  refine ⟨PEqualNP.Outside.L_meta_18617_aux.C, by decide, by decide, by decide, by decide, by decide, ?_⟩
  intro x
  rw [PEqualNP.Outside.L_meta_18617_aux.ev]
  constructor
  · intro h
    simp only [Bool.or_eq_true, Bool.and_eq_true, or_assoc] at h
    rcases h with ⟨(h | h | h), hp⟩ | ⟨(h | h | h), hp⟩ | ⟨(h | h | h), hp⟩ | ⟨(h | h | h), hp⟩
    · exact ⟨1, 0, by decide, by decide, by decide, hp, h⟩
    · exact ⟨1, 11, by decide, by decide, by decide, hp, h⟩
    · exact ⟨1, 5, by decide, by decide, by decide, hp, h⟩
    · exact ⟨2, 2, by decide, by decide, by decide, hp, h⟩
    · exact ⟨2, 12, by decide, by decide, by decide, hp, h⟩
    · exact ⟨2, 6, by decide, by decide, by decide, hp, h⟩
    · exact ⟨4, 4, by decide, by decide, by decide, hp, h⟩
    · exact ⟨4, 3, by decide, by decide, by decide, hp, h⟩
    · exact ⟨4, 8, by decide, by decide, by decide, hp, h⟩
    · exact ⟨10, 10, by decide, by decide, by decide, hp, h⟩
    · exact ⟨10, 9, by decide, by decide, by decide, hp, h⟩
    · exact ⟨10, 7, by decide, by decide, by decide, hp, h⟩
  · rintro ⟨p, l, hp, hl, hpl, h1, h2⟩
    fin_cases p <;> fin_cases l <;> simp_all (config := {decide := true})
