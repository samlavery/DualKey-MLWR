/-
  CRT Projection Independence - Standalone for Aristotle

  This proves that the cyclic and negacyclic projections from
  Z_q^{2n} to Z_q^n form a bijection when 2 is invertible.

  Key insight: if cyc[i] = s[i] + s[i+n] and neg[i] = s[i] - s[i+n],
  then s[i] = (cyc[i] + neg[i])/2 and s[i+n] = (cyc[i] - neg[i])/2.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Ring.Invertible

namespace CRTSecurity

variable (q : ℕ) [NeZero q] (n : ℕ) [NeZero n]

abbrev MasterRing := Fin (2 * n) → ZMod q
abbrev ComponentRing := Fin n → ZMod q

def cyclicProj (s : MasterRing q n) : ComponentRing q n :=
  fun i => s ⟨i.val, by omega⟩ + s ⟨i.val + n, by omega⟩

def negacyclicProj (s : MasterRing q n) : ComponentRing q n :=
  fun i => s ⟨i.val, by omega⟩ - s ⟨i.val + n, by omega⟩

def fromComponents [Invertible (2 : ZMod q)]
    (cyc neg : ComponentRing q n) : MasterRing q n :=
  fun i =>
    if h : i.val < n then
      (⅟ 2 : ZMod q) * (cyc ⟨i.val, h⟩ + neg ⟨i.val, h⟩)
    else
      (⅟ 2 : ZMod q) * (cyc ⟨i.val - n, by omega⟩ - neg ⟨i.val - n, by omega⟩)

theorem cyclicProj_fromComponents [Invertible (2 : ZMod q)]
    (cyc neg : ComponentRing q n) :
    cyclicProj q n (fromComponents q n cyc neg) = cyc := by
  funext i
  simp only [cyclicProj, fromComponents]
  have h1 : i.val < n := i.isLt
  have h2 : ¬(i.val + n < n) := by omega
  simp only [dif_pos h1, dif_neg h2]
  have hsub : i.val + n - n = i.val := by omega
  simp only [hsub]
  have h2inv : (⅟ 2 : ZMod q) * 2 = 1 := invOf_mul_self (2 : ZMod q)
  calc ⅟ 2 * (cyc ⟨i.val, h1⟩ + neg ⟨i.val, h1⟩) + ⅟ 2 * (cyc ⟨i.val, h1⟩ - neg ⟨i.val, h1⟩)
      = ⅟ 2 * 2 * cyc ⟨i.val, h1⟩ := by ring
    _ = 1 * cyc ⟨i.val, h1⟩ := by rw [h2inv]
    _ = cyc i := by simp [Fin.ext_iff]

theorem negacyclicProj_fromComponents [Invertible (2 : ZMod q)]
    (cyc neg : ComponentRing q n) :
    negacyclicProj q n (fromComponents q n cyc neg) = neg := by
  funext i
  simp only [negacyclicProj, fromComponents]
  have h1 : i.val < n := i.isLt
  have h2 : ¬(i.val + n < n) := by omega
  simp only [dif_pos h1, dif_neg h2]
  have hsub : i.val + n - n = i.val := by omega
  simp only [hsub]
  have h2inv : (⅟ 2 : ZMod q) * 2 = 1 := invOf_mul_self (2 : ZMod q)
  calc ⅟ 2 * (cyc ⟨i.val, h1⟩ + neg ⟨i.val, h1⟩) - ⅟ 2 * (cyc ⟨i.val, h1⟩ - neg ⟨i.val, h1⟩)
      = ⅟ 2 * 2 * neg ⟨i.val, h1⟩ := by ring
    _ = 1 * neg ⟨i.val, h1⟩ := by rw [h2inv]
    _ = neg i := by simp [Fin.ext_iff]

theorem proj_injective [Invertible (2 : ZMod q)] (s₁ s₂ : MasterRing q n) :
    cyclicProj q n s₁ = cyclicProj q n s₂ →
    negacyclicProj q n s₁ = negacyclicProj q n s₂ →
    s₁ = s₂ := by
  intro h_cyc h_neg
  have h2inv : (⅟ 2 : ZMod q) * 2 = 1 := invOf_mul_self (2 : ZMod q)
  funext i
  by_cases hi : i.val < n
  · -- Case i < n
    have hcyc := congrFun h_cyc ⟨i.val, hi⟩
    have hneg := congrFun h_neg ⟨i.val, hi⟩
    simp only [cyclicProj, negacyclicProj] at hcyc hneg
    have heq : 2 * s₁ ⟨i.val, by omega⟩ = 2 * s₂ ⟨i.val, by omega⟩ := by
      have ha : (s₁ ⟨i.val, by omega⟩ + s₁ ⟨i.val + n, by omega⟩) +
                (s₁ ⟨i.val, by omega⟩ - s₁ ⟨i.val + n, by omega⟩) =
                (s₂ ⟨i.val, by omega⟩ + s₂ ⟨i.val + n, by omega⟩) +
                (s₂ ⟨i.val, by omega⟩ - s₂ ⟨i.val + n, by omega⟩) := by
        rw [hcyc, hneg]
      calc 2 * s₁ ⟨i.val, _⟩
          = (s₁ ⟨i.val, _⟩ + s₁ ⟨i.val + n, _⟩) + (s₁ ⟨i.val, _⟩ - s₁ ⟨i.val + n, _⟩) := by ring
        _ = (s₂ ⟨i.val, _⟩ + s₂ ⟨i.val + n, _⟩) + (s₂ ⟨i.val, _⟩ - s₂ ⟨i.val + n, _⟩) := ha
        _ = 2 * s₂ ⟨i.val, _⟩ := by ring
    have result : s₁ ⟨i.val, by omega⟩ = s₂ ⟨i.val, by omega⟩ := by
      calc s₁ ⟨i.val, _⟩ = 1 * s₁ ⟨i.val, _⟩ := by ring
        _ = (⅟ 2 * 2) * s₁ ⟨i.val, _⟩ := by rw [h2inv]
        _ = ⅟ 2 * (2 * s₁ ⟨i.val, _⟩) := by ring
        _ = ⅟ 2 * (2 * s₂ ⟨i.val, _⟩) := by rw [heq]
        _ = (⅟ 2 * 2) * s₂ ⟨i.val, _⟩ := by ring
        _ = 1 * s₂ ⟨i.val, _⟩ := by rw [h2inv]
        _ = s₂ ⟨i.val, _⟩ := by ring
    convert result using 2 <;> ext <;> rfl
  · -- Case i >= n
    push_neg at hi
    have hj : i.val - n < n := by omega
    have hcyc := congrFun h_cyc ⟨i.val - n, hj⟩
    have hneg := congrFun h_neg ⟨i.val - n, hj⟩
    simp only [cyclicProj, negacyclicProj] at hcyc hneg
    have heq : 2 * s₁ ⟨i.val - n + n, by omega⟩ = 2 * s₂ ⟨i.val - n + n, by omega⟩ := by
      have ha : (s₁ ⟨i.val - n, by omega⟩ + s₁ ⟨i.val - n + n, by omega⟩) -
                (s₁ ⟨i.val - n, by omega⟩ - s₁ ⟨i.val - n + n, by omega⟩) =
                (s₂ ⟨i.val - n, by omega⟩ + s₂ ⟨i.val - n + n, by omega⟩) -
                (s₂ ⟨i.val - n, by omega⟩ - s₂ ⟨i.val - n + n, by omega⟩) := by
        rw [hcyc, hneg]
      calc 2 * s₁ ⟨i.val - n + n, _⟩
          = (s₁ ⟨i.val - n, _⟩ + s₁ ⟨i.val - n + n, _⟩) - (s₁ ⟨i.val - n, _⟩ - s₁ ⟨i.val - n + n, _⟩) := by ring
        _ = (s₂ ⟨i.val - n, _⟩ + s₂ ⟨i.val - n + n, _⟩) - (s₂ ⟨i.val - n, _⟩ - s₂ ⟨i.val - n + n, _⟩) := ha
        _ = 2 * s₂ ⟨i.val - n + n, _⟩ := by ring
    have result : s₁ ⟨i.val - n + n, by omega⟩ = s₂ ⟨i.val - n + n, by omega⟩ := by
      calc s₁ ⟨i.val - n + n, _⟩
          = (⅟ 2 * 2) * s₁ ⟨i.val - n + n, _⟩ := by rw [h2inv]; ring
        _ = ⅟ 2 * (2 * s₁ ⟨i.val - n + n, _⟩) := by ring
        _ = ⅟ 2 * (2 * s₂ ⟨i.val - n + n, _⟩) := by rw [heq]
        _ = (⅟ 2 * 2) * s₂ ⟨i.val - n + n, _⟩ := by ring
        _ = s₂ ⟨i.val - n + n, _⟩ := by rw [h2inv]; ring
    convert result using 2
    · ext; simp only [Nat.sub_add_cancel hi]
    · ext; simp only [Nat.sub_add_cancel hi]

theorem crt_bijection [Invertible (2 : ZMod q)] :
    Function.Bijective (fun s : MasterRing q n => (cyclicProj q n s, negacyclicProj q n s)) := by
  constructor
  · intro s₁ s₂ h
    simp only [Prod.mk.injEq] at h
    exact proj_injective q n s₁ s₂ h.1 h.2
  · intro p
    use fromComponents q n p.1 p.2
    ext
    · exact congrFun (cyclicProj_fromComponents q n p.1 p.2) _
    · exact congrFun (negacyclicProj_fromComponents q n p.1 p.2) _

theorem unique_preimage [Invertible (2 : ZMod q)]
    (c neg : ComponentRing q n) :
    ∃! s : MasterRing q n, cyclicProj q n s = c ∧ negacyclicProj q n s = neg := by
  use fromComponents q n c neg
  constructor
  · exact ⟨cyclicProj_fromComponents q n c neg, negacyclicProj_fromComponents q n c neg⟩
  · intro s hs
    have h1 : cyclicProj q n s = cyclicProj q n (fromComponents q n c neg) := by
      rw [hs.1, cyclicProj_fromComponents]
    have h2 : negacyclicProj q n s = negacyclicProj q n (fromComponents q n c neg) := by
      rw [hs.2, negacyclicProj_fromComponents]
    exact proj_injective q n s (fromComponents q n c neg) h1 h2

end CRTSecurity

-- Check axioms
#print axioms CRTSecurity.crt_bijection
#print axioms CRTSecurity.unique_preimage
