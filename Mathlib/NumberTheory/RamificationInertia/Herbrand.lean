/-
Copyright (c) 2026 Slava Kaiku. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Slava Kaiku
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.RingTheory.Ideal.RamificationGroup

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.IntermediateValue

/-!
# The Herbrand function and the upper numbering

Let a finite group `G` act by ring automorphisms on a commutative ring `B`, and let `P` be an
ideal of `B`, with ramification groups `G_i = Ideal.ramificationGroup G P i` in the lower
numbering. Following [serre1968], Chapter IV, §3, we index them by real numbers `u` through
`G_u = G_{⌈u⌉}` and define the **Herbrand function**

`φ(u) = ∫_0^u dt / [G_0 : G_t]` for `u ≥ -1`.

The integrand is `#G_t / #G_0`, which equals `1` on `(-1, 0]`, so `φ(u) = u` for `-1 ≤ u ≤ 0`.
We assume `G` finite, as in [serre1968]. The integrand is positive and decreasing, so `φ` is a
continuous, strictly increasing, concave bijection of `[-1, ∞)` onto itself. We package it as an
order isomorphism of `Set.Ici (-1 : ℝ)`; its inverse is the inverse Herbrand function `ψ`. The
**upper numbering** is `G^v = G_{ψ(v)}`, so that `G^{φ(u)} = G_u`.

For a finite Galois extension `L/K` of complete discretely valued fields with separable residue
field extension, `G = Gal(L/K)` acting on the valuation ring of `L` and `P` its maximal ideal,
these are the functions `φ_{L/K}`, `ψ_{L/K}` and the groups `G^v` of [serre1968], Chapter IV, §3.

## Main definitions

* `Ideal.ramificationGroupReal G P u`: the ramification group `G_{⌈u⌉}`, for `u : ℝ`.
* `Ideal.herbrandOrderIso G P`: the Herbrand function as an order automorphism of `[-1, ∞)`.
* `Ideal.herbrand G P`, `Ideal.inverseHerbrand G P`: its forward map `φ` and its inverse `ψ`.
* `Ideal.upperRamificationGroup G P v`: the ramification group `G^v = G_{ψ(v)}` in the upper
  numbering.

## Main results

* `Ideal.coe_herbrand`: the integral formula defining `φ`.
* `Ideal.coe_herbrand_of_mem_Icc`: for `m : ℕ` and `m ≤ u ≤ m + 1`,
  `φ(u) = (#G_1 + ⋯ + #G_m + (u - m) #G_{m+1}) / #G_0`.
* `Ideal.herbrand_of_coe_le_zero`, `Ideal.inverseHerbrand_of_coe_le_zero`: `φ` and `ψ` are the
  identity on `[-1, 0]`.
* `Ideal.herbrand_slope_anti_adjacent`: `φ` is concave.
* `Ideal.upperRamificationGroup_herbrand`: `G^{φ(u)} = G_u`.
* `Ideal.exists_upperRamificationGroup_eq_bot`: `G^v = 1` for all large `v`.

## References

* [J.-P. Serre, *Corps locaux*][serre1968], Chapter IV, §3

## Provenance

The definitions and most statements and proofs are adapted from the Tau Ceti library
(https://github.com/TauCetiProject/TauCeti, commit `396c3bd971e9722aa8656231760e710fe641d8cf`,
files `TauCeti/NumberTheory/LocalField/Herbrand/Basic.lean` and
`TauCeti/RingTheory/LocalRing/RamificationGroup.lean`; Copyright (c) 2026 The Tau Ceti
contributors; released under the Apache 2.0 license). Changes: the setting is a finite group
acting on a ring with an ideal instead of a finite Galois extension of nonarchimedean local fields
(no `IsGalois` hypothesis); the domain `[-1, ∞)` is `Set.Ici (-1 : ℝ)` instead of Tau Ceti's
`RamificationIndexDomain`; normality of `G^v` is the hypothesis-guarded
`Ideal.normal_upperRamificationGroup_of_forall_smul_eq` plus an instance for local rings; only a
selection of the statements is included (in particular the inverse Herbrand function at natural
numbers is not); `Ideal.coe_herbrand_le` and `Ideal.le_coe_inverseHerbrand` are new, and
`Ideal.exists_upperRamificationGroup_eq_bot` is a real-index analogue of Tau Ceti's
`exists_forall_upperRamificationGroup_natCast_eq_bot` with a different proof.

## Tags

ramification group, upper numbering, Herbrand function
-/

@[expose] public section

noncomputable section

open MeasureTheory Set intervalIntegral
open scoped Pointwise

namespace Ideal

variable (G : Type*) [Group G] {B : Type*} [CommRing B] [MulSemiringAction G B] (P : Ideal B)

/-! ### The real indexing -/

/-- The ramification groups indexed by a real number `u` through `G_u = G_{⌈u⌉}`. -/
def ramificationGroupReal (u : ℝ) : Subgroup G :=
  P.ramificationGroup G ⌈u⌉

variable {G P}

@[simp]
theorem ramificationGroupReal_intCast (i : ℤ) :
    P.ramificationGroupReal G i = P.ramificationGroup G i := by
  rw [ramificationGroupReal, Int.ceil_intCast]

/-- The real indexing is constant on each interval `(i - 1, i]`. -/
theorem ramificationGroupReal_eq_of_sub_one_lt_of_le {i : ℤ} {u : ℝ} (h₁ : (i : ℝ) - 1 < u)
    (h₂ : u ≤ i) : P.ramificationGroupReal G u = P.ramificationGroup G i := by
  rw [ramificationGroupReal, Int.ceil_eq_iff.2 ⟨h₁, h₂⟩]

theorem ramificationGroupReal_antitone : Antitone (P.ramificationGroupReal G) :=
  fun _ _ huv ↦ ramificationGroup_antitone (Int.ceil_mono huv)

/-! ### The Herbrand function -/

variable (G P) [Finite G]

/-- The integrand `1 / [G_0 : G_t] = #G_t / #G_0` of the Herbrand function. -/
private def herbrandDensity (t : ℝ) : ℝ :=
  Nat.card (P.ramificationGroupReal G t) / Nat.card (P.ramificationGroup G 0)

private theorem natCard_ramificationGroup_pos (i : ℤ) :
    0 < Nat.card (P.ramificationGroup G i) :=
  Nat.card_pos

private theorem herbrandDensity_antitone : Antitone (herbrandDensity G P) := fun s t hst ↦ by
  unfold herbrandDensity
  gcongr
  exact Subgroup.card_le_of_le (ramificationGroupReal_antitone (G := G) (P := P) hst)

private theorem intervalIntegrable_herbrandDensity (a b : ℝ) :
    IntervalIntegrable (herbrandDensity G P) volume a b :=
  (herbrandDensity_antitone G P).intervalIntegrable

private theorem inv_le_herbrandDensity (t : ℝ) :
    (Nat.card (P.ramificationGroup G 0) : ℝ)⁻¹ ≤ herbrandDensity G P t := by
  rw [herbrandDensity, div_eq_mul_inv]
  refine le_mul_of_one_le_left (by positivity) ?_
  rw [ramificationGroupReal]
  exact_mod_cast natCard_ramificationGroup_pos G P _

/-- The Herbrand function on the whole real line, as the primitive of `herbrandDensity`; only its
values on `[-1, ∞)` are meaningful, and only those are exported through `herbrandOrderIso`. -/
private def herbrandReal (u : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..u, herbrandDensity G P t

omit [Finite G] in
private theorem herbrandReal_def (u : ℝ) :
    herbrandReal G P u = ∫ t in (0 : ℝ)..u,
      (Nat.card (P.ramificationGroupReal G t) : ℝ) / Nat.card (P.ramificationGroup G 0) :=
  rfl

omit [Finite G] in
private theorem herbrandReal_zero : herbrandReal G P 0 = 0 :=
  integral_same

private theorem herbrandReal_sub (a b : ℝ) :
    herbrandReal G P b - herbrandReal G P a = ∫ t in a..b, herbrandDensity G P t :=
  integral_interval_sub_left (intervalIntegrable_herbrandDensity G P 0 b)
    (intervalIntegrable_herbrandDensity G P 0 a)

/-- On an interval `[a, b]` over which the lower ramification filtration is constantly `H`, that
is `G_t = H` for every `a < t ≤ b`, the Herbrand function is affine of slope `#H / #G_0`. -/
private theorem herbrandReal_sub_of_forall_eq {a b : ℝ} (hab : a ≤ b) {H : Subgroup G}
    (h : ∀ t : ℝ, a < t → t ≤ b → P.ramificationGroupReal G t = H) :
    herbrandReal G P b - herbrandReal G P a =
      (b - a) * (Nat.card H / Nat.card (P.ramificationGroup G 0)) := by
  rw [herbrandReal_sub, ← smul_eq_mul, ← intervalIntegral.integral_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t ht ↦ ?_)
  rw [uIoc_of_le hab] at ht
  rw [herbrandDensity, h t ht.1 ht.2]

/-- On an interval `[a, b] ⊆ [i - 1, i]` the Herbrand function is affine of slope
`#G_i / #G_0`. -/
private theorem herbrandReal_sub_of_le {i : ℤ} {a b : ℝ}
    (ha : (i : ℝ) - 1 ≤ a) (hab : a ≤ b) (hb : b ≤ i) :
    herbrandReal G P b - herbrandReal G P a =
      (b - a) * (Nat.card (P.ramificationGroup G i) /
        Nat.card (P.ramificationGroup G 0)) :=
  herbrandReal_sub_of_forall_eq G P hab fun _ ht₁ ht₂ ↦
    ramificationGroupReal_eq_of_sub_one_lt_of_le (G := G) (P := P) (ha.trans_lt ht₁)
      (ht₂.trans hb)

private theorem div_sub_le_herbrandReal_sub {a b : ℝ} (hab : a ≤ b) :
    (b - a) / Nat.card (P.ramificationGroup G 0) ≤
      herbrandReal G P b - herbrandReal G P a := by
  rw [herbrandReal_sub, div_eq_mul_inv, ← smul_eq_mul, ← intervalIntegral.integral_const]
  exact integral_mono_on hab intervalIntegrable_const (intervalIntegrable_herbrandDensity G P a b)
    fun t _ ↦ inv_le_herbrandDensity G P t

private theorem herbrandReal_sub_le_mul {a b : ℝ} (hab : a ≤ b) :
    herbrandReal G P b - herbrandReal G P a ≤ (b - a) * herbrandDensity G P a := by
  rw [herbrandReal_sub, ← smul_eq_mul, ← intervalIntegral.integral_const]
  exact integral_mono_on hab (intervalIntegrable_herbrandDensity G P a b) intervalIntegrable_const
    fun t ht ↦ herbrandDensity_antitone G P ht.1

private theorem mul_le_herbrandReal_sub {a b : ℝ} (hab : a ≤ b) :
    (b - a) * herbrandDensity G P b ≤ herbrandReal G P b - herbrandReal G P a := by
  rw [herbrandReal_sub, ← smul_eq_mul, ← intervalIntegral.integral_const]
  exact integral_mono_on hab intervalIntegrable_const (intervalIntegrable_herbrandDensity G P a b)
    fun t ht ↦ herbrandDensity_antitone G P ht.2

private theorem herbrandReal_strictMono : StrictMono (herbrandReal G P) := fun a b hab ↦ by
  have h := div_sub_le_herbrandReal_sub G P hab.le
  have : 0 < (b - a) / Nat.card (P.ramificationGroup G 0) := by
    have := natCard_ramificationGroup_pos G P 0
    have : 0 < b - a := sub_pos.2 hab
    positivity
  linarith

private theorem herbrandReal_continuous : Continuous (herbrandReal G P) :=
  continuous_primitive (intervalIntegrable_herbrandDensity G P) 0

private theorem herbrandReal_of_le_zero {u : ℝ} (h₁ : -1 ≤ u) (h₀ : u ≤ 0) :
    herbrandReal G P u = u := by
  have h := herbrandReal_sub_of_le G P (i := 0) (by simpa using h₁) h₀ (by simp)
  have h0 : (Nat.card (P.ramificationGroup G 0) : ℝ) ≠ 0 := by
    exact_mod_cast (natCard_ramificationGroup_pos G P 0).ne'
  rw [div_self h0, herbrandReal_zero] at h
  linarith

private theorem neg_one_le_herbrandReal {u : ℝ} (hu : -1 ≤ u) : -1 ≤ herbrandReal G P u := by
  rw [← herbrandReal_of_le_zero G P le_rfl (by norm_num)]
  exact (herbrandReal_strictMono G P).monotone hu

private theorem exists_herbrandReal_eq {y : ℝ} (hy : -1 ≤ y) :
    ∃ u, -1 ≤ u ∧ herbrandReal G P u = y := by
  set g : ℝ := (Nat.card (P.ramificationGroup G 0) : ℝ)
  have hg : 1 ≤ g := Nat.one_le_cast.2 (natCard_ramificationGroup_pos G P 0)
  set b := -1 + (y + 1) * g
  have hb : -1 ≤ b := by nlinarith
  have hφb : y ≤ herbrandReal G P b := by
    have h := div_sub_le_herbrandReal_sub G P hb
    have hb_sub : b - -1 = (y + 1) * g := by
      dsimp [b]
      ring
    rw [herbrandReal_of_le_zero G P le_rfl (by norm_num),
      hb_sub, mul_div_cancel_right₀ _ (by positivity)] at h
    linarith
  obtain ⟨u, hu, rfl⟩ := intermediate_value_Icc hb (herbrandReal_continuous G P).continuousOn
    ⟨(herbrandReal_of_le_zero G P le_rfl (by norm_num)).trans_le hy, hφb⟩
  exact ⟨u, hu.1, rfl⟩

/-- The Herbrand function as a self-map of `[-1, ∞)`. -/
private def herbrandFun (u : Set.Ici (-1 : ℝ)) : Set.Ici (-1 : ℝ) :=
  ⟨herbrandReal G P u, mem_Ici.2 (neg_one_le_herbrandReal G P u.2)⟩

private theorem herbrandFun_strictMono : StrictMono (herbrandFun G P) :=
  fun _ _ h ↦ Subtype.mk_lt_mk.2 (herbrandReal_strictMono G P h)

private theorem herbrandFun_surjective : Function.Surjective (herbrandFun G P) := fun y ↦ by
  obtain ⟨u, hu, h⟩ := exists_herbrandReal_eq G P y.2
  exact ⟨⟨u, hu⟩, Subtype.ext h⟩

/-- The Herbrand function as an order automorphism of `[-1, ∞)`:
`φ(u) = ∫_0^u #G_t / #G_0 dt`, see `Ideal.coe_herbrand`. -/
@[no_expose]
def herbrandOrderIso : Set.Ici (-1 : ℝ) ≃o Set.Ici (-1 : ℝ) :=
  StrictMono.orderIsoOfSurjective (herbrandFun G P) (herbrandFun_strictMono G P)
    (herbrandFun_surjective G P)

/-- The **Herbrand function** `φ`, the forward map of `Ideal.herbrandOrderIso`. -/
def herbrand (u : Set.Ici (-1 : ℝ)) : Set.Ici (-1 : ℝ) :=
  P.herbrandOrderIso G u

/-- The **inverse Herbrand function** `ψ`, the inverse of `Ideal.herbrandOrderIso`. -/
def inverseHerbrand (v : Set.Ici (-1 : ℝ)) : Set.Ici (-1 : ℝ) :=
  (P.herbrandOrderIso G).symm v

@[simp]
theorem herbrandOrderIso_apply (u : Set.Ici (-1 : ℝ)) :
    P.herbrandOrderIso G u = P.herbrand G u :=
  rfl

@[simp]
theorem herbrandOrderIso_symm_apply (v : Set.Ici (-1 : ℝ)) :
    (P.herbrandOrderIso G).symm v = P.inverseHerbrand G v :=
  rfl

/-- The integral formula for the Herbrand function: `φ(u) = ∫_0^u #G_t / #G_0 dt`. -/
theorem coe_herbrand (u : Set.Ici (-1 : ℝ)) :
    (P.herbrand G u : ℝ) = ∫ t in (0 : ℝ)..u,
      (Nat.card (P.ramificationGroupReal G t) : ℝ) / Nat.card (P.ramificationGroup G 0) := by
  rw [← herbrandOrderIso_apply, herbrandOrderIso, StrictMono.coe_orderIsoOfSurjective]
  exact herbrandReal_def G P u

private theorem coe_herbrand_eq_herbrandReal (u : Set.Ici (-1 : ℝ)) :
    (P.herbrand G u : ℝ) = herbrandReal G P u :=
  (coe_herbrand G P u).trans (herbrandReal_def G P u).symm

@[simp]
theorem herbrand_inverseHerbrand (v : Set.Ici (-1 : ℝ)) :
    P.herbrand G (P.inverseHerbrand G v) = v :=
  (P.herbrandOrderIso G).apply_symm_apply v

@[simp]
theorem inverseHerbrand_herbrand (u : Set.Ici (-1 : ℝ)) :
    P.inverseHerbrand G (P.herbrand G u) = u :=
  (P.herbrandOrderIso G).symm_apply_apply u

theorem herbrand_strictMono : StrictMono (P.herbrand G) :=
  (P.herbrandOrderIso G).strictMono

theorem inverseHerbrand_strictMono : StrictMono (P.inverseHerbrand G) :=
  (P.herbrandOrderIso G).symm.strictMono

@[fun_prop]
theorem continuous_herbrand : Continuous (P.herbrand G) :=
  (P.herbrandOrderIso G).continuous

@[fun_prop]
theorem continuous_inverseHerbrand : Continuous (P.inverseHerbrand G) :=
  (P.herbrandOrderIso G).symm.continuous

/-- The Herbrand function is the identity on `[-1, 0]`. -/
@[simp]
theorem herbrand_of_coe_le_zero {u : Set.Ici (-1 : ℝ)} (hu : (u : ℝ) ≤ 0) :
    P.herbrand G u = u :=
  Subtype.ext
    ((coe_herbrand_eq_herbrandReal G P u).trans (herbrandReal_of_le_zero G P u.2 hu))

/-- The inverse Herbrand function is the identity on `[-1, 0]`. -/
@[simp]
theorem inverseHerbrand_of_coe_le_zero {v : Set.Ici (-1 : ℝ)} (hv : (v : ℝ) ≤ 0) :
    P.inverseHerbrand G v = v :=
  (P.herbrandOrderIso G).symm_apply_eq.2 (herbrand_of_coe_le_zero G P hv).symm

/-- `φ(u) ≤ u`. -/
theorem coe_herbrand_le (u : Set.Ici (-1 : ℝ)) : (P.herbrand G u : ℝ) ≤ u := by
  rw [coe_herbrand_eq_herbrandReal]
  by_cases hu : (u : ℝ) ≤ 0
  · rw [herbrandReal_of_le_zero G P u.2 hu]
  · have hu' : 0 ≤ (u : ℝ) := le_of_not_ge hu
    have h := herbrandReal_sub_le_mul G P (a := 0) (b := (u : ℝ)) hu'
    have h0card : (Nat.card (P.ramificationGroup G 0) : ℝ) ≠ 0 := by
      exact_mod_cast (natCard_ramificationGroup_pos G P 0).ne'
    have hsame : P.ramificationGroupReal G 0 = P.ramificationGroup G 0 := by
      norm_num [ramificationGroupReal]
    have h0 : herbrandDensity G P 0 = 1 := by
      rw [herbrandDensity, hsame]
      exact div_self h0card
    rw [herbrandReal_zero, h0] at h
    simpa using h

/-- `v ≤ ψ(v)`. -/
theorem le_coe_inverseHerbrand (v : Set.Ici (-1 : ℝ)) : (v : ℝ) ≤ P.inverseHerbrand G v := by
  have h := coe_herbrand_le G P (P.inverseHerbrand G v)
  rw [herbrand_inverseHerbrand] at h
  exact h

/-- The Herbrand function is **concave**: its slopes over two adjacent intervals decrease. -/
theorem herbrand_slope_anti_adjacent {u v w : Set.Ici (-1 : ℝ)} (huv : u < v) (hvw : v < w) :
    ((P.herbrand G w : ℝ) - P.herbrand G v) / ((w : ℝ) - v) ≤
      ((P.herbrand G v : ℝ) - P.herbrand G u) / ((v : ℝ) - u) := by
  have huv' : (u : ℝ) < v := huv
  have hvw' : (v : ℝ) < w := hvw
  simp only [coe_herbrand_eq_herbrandReal]
  calc (herbrandReal G P w - herbrandReal G P v) / ((w : ℝ) - v)
      ≤ herbrandDensity G P v :=
        (div_le_iff₀' (sub_pos.2 hvw')).2 (herbrandReal_sub_le_mul G P hvw'.le)
    _ ≤ (herbrandReal G P v - herbrandReal G P u) / ((v : ℝ) - u) :=
        (le_div_iff₀' (sub_pos.2 huv')).2 (mul_le_herbrandReal_sub G P huv'.le)

/-- On an interval `[a, b]` over which the ramification groups are constant, the Herbrand
function is affine of slope `#G_b / #G_0`. -/
theorem coe_herbrand_sub_coe_herbrand_of_forall_eq {a b : Set.Ici (-1 : ℝ)} (hab : a ≤ b)
    (h : ∀ t : ℝ, (a : ℝ) < t → t ≤ b → P.ramificationGroupReal G t = P.ramificationGroupReal G b) :
    (P.herbrand G b : ℝ) - P.herbrand G a =
      ((b : ℝ) - a) * (Nat.card (P.ramificationGroupReal G b) /
        Nat.card (P.ramificationGroup G 0)) := by
  rw [coe_herbrand_eq_herbrandReal, coe_herbrand_eq_herbrandReal]
  exact herbrandReal_sub_of_forall_eq G P (Subtype.coe_le_coe.2 hab) h

private theorem herbrandReal_of_mem_Icc (n : ℕ) {u : ℝ} (h₁ : (n : ℝ) ≤ u)
    (h₂ : u ≤ n + 1) :
    herbrandReal G P u =
      (∑ i ∈ Finset.Icc 1 n, (Nat.card (P.ramificationGroup G i) : ℝ) +
        (u - n) * Nat.card (P.ramificationGroup G (n + 1 : ℕ))) /
        Nat.card (P.ramificationGroup G 0) := by
  have hstep := herbrandReal_sub_of_le G P (i := (n + 1 : ℕ)) (by
      push_cast
      linarith) h₁ (by
      push_cast
      linarith)
  induction n generalizing u with
  | zero =>
    rw [Nat.cast_zero, herbrandReal_zero] at hstep
    rw [Finset.Icc_eq_empty (by norm_num), Finset.sum_empty]
    linear_combination hstep
  | succ m ih =>
    have hm := ih (u := (m + 1 : ℕ)) (by
        push_cast
        linarith) (by
        push_cast
        linarith)
      (herbrandReal_sub_of_le G P (i := (m + 1 : ℕ)) (by
        push_cast
        linarith) (by
        push_cast
        linarith) (by
        push_cast
        linarith))
    rw [Finset.sum_Icc_succ_top (by omega)]
    rw [hm] at hstep
    push_cast at hstep ⊢
    linear_combination hstep

/-- The finite-sum formula for the Herbrand function: for `m : ℕ` and `m ≤ u ≤ m + 1`,
`φ(u) = (#G_1 + ⋯ + #G_m + (u - m) #G_{m+1}) / #G_0`. -/
theorem coe_herbrand_of_mem_Icc (m : ℕ) {u : Set.Ici (-1 : ℝ)} (h₁ : (m : ℝ) ≤ u)
    (h₂ : (u : ℝ) ≤ m + 1) :
    (P.herbrand G u : ℝ) =
      (∑ i ∈ Finset.Icc 1 m, (Nat.card (P.ramificationGroup G i) : ℝ) +
        (u - m) * Nat.card (P.ramificationGroup G (m + 1 : ℕ))) /
        Nat.card (P.ramificationGroup G 0) :=
  (coe_herbrand_eq_herbrandReal G P u).trans (herbrandReal_of_mem_Icc G P m h₁ h₂)

/-! ### The upper numbering -/

/-- The ramification group `G^v = G_{ψ(v)}` in the upper numbering, for `v ≥ -1`. -/
def upperRamificationGroup (v : Set.Ici (-1 : ℝ)) : Subgroup G :=
  P.ramificationGroupReal G (P.inverseHerbrand G v)

/-- The upper and lower numberings are related by `G^{φ(u)} = G_u`. -/
@[simp]
theorem upperRamificationGroup_herbrand (u : Set.Ici (-1 : ℝ)) :
    P.upperRamificationGroup G (P.herbrand G u) = P.ramificationGroupReal G u := by
  rw [upperRamificationGroup, inverseHerbrand_herbrand]

/-- On `[-1, 0]` the upper and lower numberings agree. -/
theorem upperRamificationGroup_of_coe_le_zero {v : Set.Ici (-1 : ℝ)} (hv : (v : ℝ) ≤ 0) :
    P.upperRamificationGroup G v = P.ramificationGroupReal G v := by
  rw [upperRamificationGroup, inverseHerbrand_of_coe_le_zero G P hv]

theorem upperRamificationGroup_antitone : Antitone (P.upperRamificationGroup G) :=
  fun _ _ h ↦ ramificationGroupReal_antitone ((inverseHerbrand_strictMono G P).monotone h)

variable {G P} in
/-- If every element of `G` fixes `P`, then the ramification groups in the upper numbering are
normal in `G`. -/
theorem normal_upperRamificationGroup_of_forall_smul_eq (h : ∀ g : G, g • P = P)
    (v : Set.Ici (-1 : ℝ)) : (P.upperRamificationGroup G v).Normal := by
  rw [upperRamificationGroup, ramificationGroupReal]
  exact Ideal.normal_ramificationGroup_of_forall_smul_eq (G := G) (P := P) h _

/-- If `G` acts faithfully and `⋂ₙ P ^ n = 0`, then `G^v = 1` for all large `v`. -/
theorem exists_upperRamificationGroup_eq_bot [FaithfulSMul G B] (hP : ⨅ n : ℕ, P ^ n = ⊥) :
    ∃ v₀ : ℝ, ∀ v : Set.Ici (-1 : ℝ), v₀ ≤ v → P.upperRamificationGroup G v = ⊥ := by
  obtain ⟨n, hn⟩ := exists_ramificationGroup_eq_bot (G := G) (P := P) hP
  refine ⟨(n : ℝ), fun v hv ↦ ?_⟩
  rw [upperRamificationGroup, ramificationGroupReal]
  apply hn
  have hnv : (n : ℝ) ≤ (P.inverseHerbrand G v : ℝ) :=
    hv.trans (le_coe_inverseHerbrand G P v)
  simpa only [Int.ceil_intCast] using Int.ceil_mono hnv

end Ideal

namespace IsLocalRing

variable {G : Type*} [Group G] {B : Type*} [CommRing B] [IsLocalRing B] [MulSemiringAction G B]
  [Finite G]

/-- The ramification groups in the upper numbering of the maximal ideal of a local ring are
normal. -/
instance (v : Set.Ici (-1 : ℝ)) : ((maximalIdeal B).upperRamificationGroup G v).Normal :=
  Ideal.normal_upperRamificationGroup_of_forall_smul_eq smul_maximalIdeal v

end IsLocalRing
