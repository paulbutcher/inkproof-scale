/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core.Axioms
import Inkproof.Scale.Affine
import Inkproof.Scale.Linear

namespace Inkproof.Scale

open Inkproof.Core


private theorem ratAbs_eq (a : Rat) : ratAbs a = a ∨ ratAbs a = -a := by
  unfold ratAbs; split <;> simp

private theorem ratAbs_nonneg (a : Rat) : 0 ≤ ratAbs a := by
  unfold ratAbs; split <;> grind

private theorem ratAbs_le_iff {a b : Rat} : ratAbs a ≤ b ↔ -b ≤ a ∧ a ≤ b := by
  unfold ratAbs; split <;> grind

private theorem ratAbs_add_le (a b : Rat) : ratAbs (a + b) ≤ ratAbs a + ratAbs b := by
  unfold ratAbs; repeat' split
  all_goals grind

private theorem ratAbs_mul (a b : Rat) : ratAbs (a * b) = ratAbs a * ratAbs b := by
  unfold ratAbs
  by_cases ha : a < 0 <;> by_cases hb : b < 0
  · have := Rat.mul_nonneg (a := -a) (b := -b) (by grind) (by grind)
    have : a * b = (-a) * (-b) := by grind
    grind
  · have := Rat.mul_nonneg (a := -a) (b := b) (by grind) (by grind)
    have : (-a) * b = -(a * b) := by grind
    grind
  · have := Rat.mul_nonneg (a := a) (b := -b) (by grind) (by grind)
    have : a * (-b) = -(a * b) := by grind
    grind
  · have := Rat.mul_nonneg (a := a) (b := b) (by grind) (by grind)
    grind

private theorem step (q p m d k : Rat) (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (h1 : ratAbs (p - m) ≤ ratAbs m * k)
    (h2 : ratAbs (q - (p + d)) ≤ ratAbs (p + d) * k) :
    ratAbs (q - (m + d)) ≤ 4 * (ratAbs m + ratAbs d) * k := by
  have a1 := ratAbs_add_le (q - (p + d)) (p - m)
  have a2 := ratAbs_add_le p d
  have a3 := ratAbs_add_le (p - m) m
  have n1 := ratAbs_nonneg m
  have n2 := ratAbs_nonneg d
  have e : q - (m + d) = (q - (p + d)) + (p - m) := by grind
  rw [e]
  have k1 : ratAbs m * k ≤ ratAbs m * 1 := Rat.mul_le_mul_of_nonneg_left hk1 n1
  have k2 : ratAbs (p + d) * k ≤ (3 * ratAbs m + ratAbs d) * k :=
    Rat.mul_le_mul_of_nonneg_right (by grind) hk0
  have := Rat.mul_nonneg n2 hk0
  grind

private theorem k_facts : (0 : Rat) ≤ (scaleTwoPow 1 53)⁻¹ ∧ (scaleTwoPow 1 53)⁻¹ ≤ 1 / 8 := by
  have h : scaleTwoPow 1 53 = 9007199254740992 := by
    rw [scaleTwoPow_of_nonneg _ (by decide)]; simp
  rw [h]; constructor <;> grind

private theorem approx_rel {z : Float} {r : Rat} (h : Float.Approximates z r) :
    ∃ q, Float.toRat z = some q ∧ ratAbs (q - r) ≤ ratAbs r * (scaleTwoPow 1 53)⁻¹ := by
  obtain ⟨q, hq, hb⟩ := h
  exact ⟨q, hq, by rwa [Rat.div_def] at hb⟩

private theorem mulAbs (a b c : Rat) {k : Rat} (h : ratAbs b ≤ ratAbs c * k) :
    ratAbs (a * b) ≤ ratAbs (a * c) * k := by
  rw [ratAbs_mul, ratAbs_mul]
  have := Rat.mul_le_mul_of_nonneg_left h (ratAbs_nonneg a)
  grind

private theorem rebased_core (a b w d xo po pm c' z k : Rat) (hk0 : 0 ≤ k) (hk1 : k ≤ 1 / 8)
    (e_po : ratAbs (po - a * w) ≤ ratAbs (a * w) * k)
    (e_c : ratAbs (c' - (po + d)) ≤ ratAbs (po + d) * k)
    (e_xo : ratAbs (xo - (b - w)) ≤ ratAbs (b - w) * k)
    (e_pm : ratAbs (pm - a * xo) ≤ ratAbs (a * xo) * k)
    (e_z : ratAbs (z - (pm + c')) ≤ ratAbs (pm + c') * k) :
    ratAbs (z - (a * b + d)) ≤ 8 * (ratAbs (a * (b - w)) + ratAbs (a * w) + ratAbs d) * k := by
  have hc := step c' po (a * w) d k hk0 (by grind) e_po e_c
  have hx := mulAbs a (xo - (b - w)) (b - w) e_xo
  have nU := ratAbs_nonneg (a * (b - w))
  have nW := ratAbs_nonneg (a * w)
  have nD := ratAbs_nonneg d
  have t1 := ratAbs_add_le (a * (b - w)) (a * (xo - (b - w)))
  have t2 := ratAbs_add_le (a * xo - a * (b - w)) (a * (b - w))
  have eq1 : a * xo = a * (b - w) + a * (xo - (b - w)) := by grind
  have eq2 : a * xo - a * (b - w) = a * (xo - (b - w)) := by grind
  have kU : ratAbs (a * (b - w)) * k ≤ ratAbs (a * (b - w)) * (1 / 8) :=
    Rat.mul_le_mul_of_nonneg_left hk1 nU
  have axo : ratAbs (a * xo) ≤ 2 * ratAbs (a * (b - w)) := by rw [eq1]; grind
  have m1 : ratAbs (a * xo) * k ≤ 2 * ratAbs (a * (b - w)) * k :=
    Rat.mul_le_mul_of_nonneg_right axo hk0
  have pm' := ratAbs_add_le (pm - a * xo) (a * xo)
  have pmb : ratAbs pm ≤ 4 * ratAbs (a * (b - w)) := by
    have : pm = (pm - a * xo) + a * xo := by grind
    rw [this]; have := Rat.mul_le_mul_of_nonneg_left hk1 (ratAbs_nonneg (a * xo)); grind
  have c1 := ratAbs_add_le (c' - (a * w + d)) (a * w + d)
  have c2 := ratAbs_add_le (a * w) d
  have kW : ratAbs (a * w) * k ≤ ratAbs (a * w) * (1 / 8) := Rat.mul_le_mul_of_nonneg_left hk1 nW
  have kD : ratAbs d * k ≤ ratAbs d * (1 / 8) := Rat.mul_le_mul_of_nonneg_left hk1 nD
  have cb : ratAbs c' ≤ 2 * (ratAbs (a * w) + ratAbs d) := by
    have : c' = (c' - (a * w + d)) + (a * w + d) := by grind
    rw [this]; grind
  have s1 := ratAbs_add_le pm c'
  have m2 : ratAbs (pm + c') * k ≤ (4 * ratAbs (a * (b - w)) + 2 * (ratAbs (a * w) + ratAbs d)) * k :=
    Rat.mul_le_mul_of_nonneg_right (by grind) hk0
  have f1 := ratAbs_add_le (z - (pm + c')) (pm - a * xo)
  have f2 := ratAbs_add_le (z - (pm + c') + (pm - a * xo)) (a * xo - a * (b - w))
  have f3 := ratAbs_add_le (z - (pm + c') + (pm - a * xo) + (a * xo - a * (b - w))) (c' - (a * w + d))
  have eq3 : z - (a * b + d) = z - (pm + c') + (pm - a * xo) + (a * xo - a * (b - w)) + (c' - (a * w + d)) := by
    grind
  rw [eq3]
  rw [eq2] at f2 f3
  have := Rat.mul_nonneg nU hk0
  have := Rat.mul_nonneg nW hk0
  have := Rat.mul_nonneg nD hk0
  grind


private theorem k_sixteen : 16 * (scaleTwoPow 1 53)⁻¹ = (scaleTwoPow 1 49)⁻¹ := by
  have h : scaleTwoPow 1 53 = 9007199254740992 := by
    rw [scaleTwoPow_of_nonneg _ (by decide)]; simp
  have h' : scaleTwoPow 1 49 = 562949953421312 := by
    rw [scaleTwoPow_of_nonneg _ (by decide)]; simp
  rw [h, h']; grind

private theorem k_eight : 8 * (scaleTwoPow 1 53)⁻¹ = (scaleTwoPow 1 50)⁻¹ := by
  have h : scaleTwoPow 1 53 = 9007199254740992 := by
    rw [scaleTwoPow_of_nonneg _ (by decide)]; simp
  have h' : scaleTwoPow 1 50 = 1125899906842624 := by
    rw [scaleTwoPow_of_nonneg _ (by decide)]; simp
  rw [h, h']; grind

private theorem mulLe {a b c d : Rat} (h1 : a ≤ c) (h2 : b ≤ d) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a * b ≤ c * d :=
  Rat.le_trans (Rat.mul_le_mul_of_nonneg_right h1 hb) (Rat.mul_le_mul_of_nonneg_left h2 hc)

private theorem mul_rel (x y a b c1 c2 : Rat) (hc1 : 0 ≤ c1)
    (h1 : ratAbs (x - a) ≤ ratAbs a * c1) (h2 : ratAbs (y - b) ≤ ratAbs b * c2) :
    ratAbs (x * y - a * b) ≤ ratAbs (a * b) * (c1 + c2 + c1 * c2) := by
  have e : x * y - a * b = (x - a) * (y - b) + (x - a) * b + a * (y - b) := by grind
  have t1 := ratAbs_add_le ((x - a) * (y - b) + (x - a) * b) (a * (y - b))
  have t2 := ratAbs_add_le ((x - a) * (y - b)) ((x - a) * b)
  have m1 : ratAbs ((x - a) * (y - b)) ≤ (ratAbs a * c1) * (ratAbs b * c2) := by
    rw [ratAbs_mul]
    exact mulLe h1 h2 (ratAbs_nonneg _) (Rat.mul_nonneg (ratAbs_nonneg _) hc1)
  have m2 : ratAbs ((x - a) * b) ≤ (ratAbs a * c1) * ratAbs b := by
    rw [ratAbs_mul]
    exact Rat.mul_le_mul_of_nonneg_right h1 (ratAbs_nonneg _)
  have m3 : ratAbs (a * (y - b)) ≤ ratAbs a * (ratAbs b * c2) := by
    rw [ratAbs_mul]
    exact Rat.mul_le_mul_of_nonneg_left h2 (ratAbs_nonneg _)
  rw [e, ratAbs_mul a b]
  grind

private theorem round_rel (z x r c k : Rat) (hk : 0 ≤ k)
    (h1 : ratAbs (x - r) ≤ ratAbs r * c) (h2 : ratAbs (z - x) ≤ ratAbs x * k) :
    ratAbs (z - r) ≤ ratAbs r * (c + k + c * k) := by
  have t := ratAbs_add_le (z - x) (x - r)
  have t' := ratAbs_add_le (x - r) r
  have e : z - r = (z - x) + (x - r) := by grind
  have m := Rat.mul_le_mul_of_nonneg_right (show ratAbs x ≤ ratAbs r + ratAbs r * c by grind) hk
  rw [e]
  grind

private theorem div_rel (t4 t3 v A B C u c4 k c : Rat) (hk1 : k < 1)
    (hC : C ≠ 0) (hu : u * C = A * B)
    (h4 : ratAbs (t4 - A * B) ≤ ratAbs (A * B) * c4) (h3 : ratAbs (t3 - C) ≤ ratAbs C * k)
    (hv : v * t3 = t4) (hc : c4 + k ≤ c * (1 - k)) :
    ratAbs (v - u) ≤ ratAbs u * c := by
  have hCpos : 0 < ratAbs C := by
    unfold ratAbs; split <;> grind
  have e : (v - u) * t3 = (t4 - A * B) + u * (C - t3) := by grind
  have lhs : ratAbs ((v - u) * t3) = ratAbs (v - u) * ratAbs t3 := ratAbs_mul _ _
  have t := ratAbs_add_le (t4 - A * B) (u * (C - t3))
  have hAB : ratAbs (A * B) = ratAbs u * ratAbs C := by rw [← hu, ratAbs_mul]
  have hCt : ratAbs (C - t3) = ratAbs (t3 - C) := by
    unfold ratAbs; split <;> split <;> grind
  have m1 : ratAbs (u * (C - t3)) ≤ ratAbs u * (ratAbs C * k) := by
    rw [ratAbs_mul, hCt]
    exact Rat.mul_le_mul_of_nonneg_left h3 (ratAbs_nonneg _)
  have t3b : ratAbs C * (1 - k) ≤ ratAbs t3 := by
    have := ratAbs_add_le t3 (C - t3)
    have e3 : t3 + (C - t3) = C := by grind
    rw [e3] at this
    grind
  have nv := ratAbs_nonneg (v - u)
  have nu := ratAbs_nonneg u
  have hw : 0 < ratAbs C * (1 - k) := Rat.mul_pos hCpos (by grind)
  have step1 : ratAbs (v - u) * (ratAbs C * (1 - k)) ≤ ratAbs (v - u) * ratAbs t3 :=
    Rat.mul_le_mul_of_nonneg_left t3b nv
  have step2 : ratAbs (v - u) * ratAbs t3 ≤ ratAbs u * ratAbs C * (c4 + k) := by
    rw [← lhs, e]
    rw [hAB] at h4
    grind
  have step3 : ratAbs u * ratAbs C * (c4 + k) ≤ ratAbs u * ratAbs C * (c * (1 - k)) :=
    Rat.mul_le_mul_of_nonneg_left hc (Rat.mul_nonneg nu (ratAbs_nonneg _))
  have : ratAbs (v - u) * (ratAbs C * (1 - k)) ≤ (ratAbs u * c) * (ratAbs C * (1 - k)) := by
    grind
  exact Rat.le_of_mul_le_mul_right this hw

private theorem lin_core (X P Q R S t1 t2 t4 t3 t5 z k : Rat) (hk0 : 0 ≤ k) (hk1 : k ≤ 1 / 8)
    (hC : Q - P ≠ 0)
    (e1 : ratAbs (t1 - (X - P)) ≤ ratAbs (X - P) * k)
    (e2 : ratAbs (t2 - (S - R)) ≤ ratAbs (S - R) * k)
    (e4 : ratAbs (t4 - t1 * t2) ≤ ratAbs (t1 * t2) * k)
    (e3 : ratAbs (t3 - (Q - P)) ≤ ratAbs (Q - P) * k) (hne : t3 ≠ 0)
    (e5 : ratAbs (t5 - t4 / t3) ≤ ratAbs (t4 / t3) * k)
    (ez : ratAbs (z - (R + t5)) ≤ ratAbs (R + t5) * k) :
    ratAbs (z - (R + (X - P) * (S - R) / (Q - P))) ≤
      16 * (ratAbs ((X - P) * (S - R) / (Q - P)) + ratAbs R) * k := by
  have kk : k * k ≤ k * (1 / 8) := Rat.mul_le_mul_of_nonneg_left hk1 hk0
  have kkk : k * k * k ≤ k * k * (1 / 8) := Rat.mul_le_mul_of_nonneg_left hk1 (Rat.mul_nonneg hk0 hk0)
  have m := mul_rel t1 t2 (X - P) (S - R) k k hk0 e1 e2
  have r4 := round_rel t4 (t1 * t2) ((X - P) * (S - R)) (k + k + k * k) k hk0 m e4
  have hu : ((X - P) * (S - R) / (Q - P)) * (Q - P) = (X - P) * (S - R) := Rat.div_mul_cancel hC
  have hv : (t4 / t3) * t3 = t4 := Rat.div_mul_cancel hne
  have d := div_rel t4 t3 (t4 / t3) (X - P) (S - R) (Q - P) ((X - P) * (S - R) / (Q - P))
    (k + k + k * k + k + (k + k + k * k) * k) k (7 * k) (by grind) hC hu r4 e3 hv (by grind)
  have r5 := round_rel t5 (t4 / t3) _ (7 * k) k hk0 d e5
  generalize (X - P) * (S - R) / (Q - P) = u at *
  have nu := ratAbs_nonneg u
  have nR := ratAbs_nonneg R
  have t := ratAbs_add_le (z - (R + t5)) (t5 - u)
  have t' := ratAbs_add_le (t5 - u) u
  have t'' := ratAbs_add_le R t5
  have e : z - (R + u) = (z - (R + t5)) + (t5 - u) := by grind
  have a1 := Rat.mul_le_mul_of_nonneg_right (show ratAbs (R + t5) ≤ 3 * ratAbs u + ratAbs R by
    have : ratAbs u * (7 * k + k + 7 * k * k) ≤ ratAbs u * 2 :=
      Rat.mul_le_mul_of_nonneg_left (by grind) nu
    grind) hk0
  have a2 : ratAbs u * (7 * k + k + 7 * k * k) ≤ ratAbs u * (9 * k) :=
    Rat.mul_le_mul_of_nonneg_left (by grind) nu
  have p1 := Rat.mul_nonneg nu hk0
  have p2 := Rat.mul_nonneg nR hk0
  rw [e]
  grind

private theorem sens (X W P Q R S xo po qo k : Rat)
    (hC : Q - P ≠ 0)
    (exo : ratAbs (xo - (X - W)) ≤ ratAbs (X - W) * k)
    (epo : ratAbs (po - (P - W)) ≤ ratAbs (P - W) * k)
    (eqo : ratAbs (qo - (Q - W)) ≤ ratAbs (Q - W) * k)
    (stab : 2 * k * (ratAbs (Q - W) + ratAbs (P - W)) ≤ ratAbs (Q - P)) :
    qo - po ≠ 0 ∧
    ratAbs ((xo - po) * (S - R) / (qo - po) - (X - P) * (S - R) / (Q - P)) * ratAbs (Q - P) ≤
      2 * k * (ratAbs (S - R) * (ratAbs (X - W) + ratAbs (P - W)) +
        ratAbs ((X - P) * (S - R) / (Q - P)) * (ratAbs (Q - W) + ratAbs (P - W))) := by
  have hCpos : 0 < ratAbs (Q - P) := by unfold ratAbs; split <;> grind
  have nXW := ratAbs_nonneg (X - W)
  have nPW := ratAbs_nonneg (P - W)
  have nQW := ratAbs_nonneg (Q - W)
  have c1 := ratAbs_add_le (qo - (Q - W)) (-(po - (P - W)))
  have c1' : ratAbs (-(po - (P - W))) = ratAbs (po - (P - W)) := by
    unfold ratAbs; split <;> split <;> grind
  rw [c1'] at c1
  have dC : ratAbs ((qo - po) - (Q - P)) ≤ k * (ratAbs (Q - W) + ratAbs (P - W)) := by
    have e : (qo - po) - (Q - P) = (qo - (Q - W)) + -(po - (P - W)) := by grind
    rw [e]; grind
  have dA : ratAbs ((xo - po) - (X - P)) ≤ k * (ratAbs (X - W) + ratAbs (P - W)) := by
    have c := ratAbs_add_le (xo - (X - W)) (-(po - (P - W)))
    have c' : ratAbs (-(po - (P - W))) = ratAbs (po - (P - W)) := by
      unfold ratAbs; split <;> split <;> grind
    rw [c'] at c
    have e : (xo - po) - (X - P) = (xo - (X - W)) + -(po - (P - W)) := by grind
    rw [e]; grind
  have hC' : ratAbs (Q - P) ≤ ratAbs (qo - po) + ratAbs ((qo - po) - (Q - P)) := by
    have := ratAbs_add_le (qo - po) (-((qo - po) - (Q - P)))
    have h' : ratAbs (-((qo - po) - (Q - P))) = ratAbs ((qo - po) - (Q - P)) := by
      unfold ratAbs; split <;> split <;> grind
    have e : qo - po + -((qo - po) - (Q - P)) = Q - P := by grind
    rw [e, h'] at this; exact this
  have half : ratAbs (Q - P) ≤ 2 * ratAbs (qo - po) := by grind
  have hne : qo - po ≠ 0 := by
    intro h0
    rw [h0] at half
    have : ratAbs (0 : Rat) = 0 := by unfold ratAbs; simp
    grind
  refine ⟨hne, ?_⟩
  generalize hu : (X - P) * (S - R) / (Q - P) = u
  generalize hu' : (xo - po) * (S - R) / (qo - po) = u'
  have hu1 : u * (Q - P) = (X - P) * (S - R) := by rw [← hu]; exact Rat.div_mul_cancel hC
  have hu2 : u' * (qo - po) = (xo - po) * (S - R) := by rw [← hu']; exact Rat.div_mul_cancel hne
  have e : (u' - u) * (qo - po) = ((xo - po) - (X - P)) * (S - R) + u * ((Q - P) - (qo - po)) := by
    grind
  have lhs : ratAbs ((u' - u) * (qo - po)) = ratAbs (u' - u) * ratAbs (qo - po) := ratAbs_mul _ _
  have t := ratAbs_add_le (((xo - po) - (X - P)) * (S - R)) (u * ((Q - P) - (qo - po)))
  have hsw : ratAbs ((Q - P) - (qo - po)) = ratAbs ((qo - po) - (Q - P)) := by
    unfold ratAbs; split <;> split <;> grind
  have b1 : ratAbs (((xo - po) - (X - P)) * (S - R)) ≤
      (k * (ratAbs (X - W) + ratAbs (P - W))) * ratAbs (S - R) := by
    rw [ratAbs_mul]; exact Rat.mul_le_mul_of_nonneg_right dA (ratAbs_nonneg _)
  have b2 : ratAbs (u * ((Q - P) - (qo - po))) ≤
      ratAbs u * (k * (ratAbs (Q - W) + ratAbs (P - W))) := by
    rw [ratAbs_mul, hsw]; exact Rat.mul_le_mul_of_nonneg_left dC (ratAbs_nonneg _)
  have h2 : ratAbs (u' - u) * ratAbs (Q - P) ≤ ratAbs (u' - u) * (2 * ratAbs (qo - po)) :=
    Rat.mul_le_mul_of_nonneg_left half (ratAbs_nonneg _)
  rw [e] at lhs
  grind

/-- The Float rebased map, rebasing in floats and then applying to `x - origin`, is
within `(|slope * (x - origin)| + |slope * origin| + |offset|) / 2 ^ 50` of the exact value of the
unrebased map at `x`, given that no intermediate result overflows or falls into the subnormal
range. The rebased offset `slope * origin + offset` is computed in floats, so the bound includes
the magnitude of the pixel position of the origin, not only of the point. -/
theorem Affine.rebase_apply_float_error (t : Affine Float) (o x : Float) {a w b d : Rat}
    (hs : Float.toRat t.slope = some a) (ho : Float.toRat o = some w)
    (hx : Float.toRat x = some b) (hc : Float.toRat t.offset = some d)
    (n1 : NormalRange (a * w))
    (n2 : ∀ po, Float.toRat (t.slope * o) = some po → NormalRange (po + d))
    (n3 : NormalRange (b - w))
    (n4 : ∀ xo, Float.toRat (x - o) = some xo → NormalRange (a * xo))
    (n5 : ∀ pm c', Float.toRat (t.slope * (x - o)) = some pm →
      Float.toRat (t.slope * o + t.offset) = some c' → NormalRange (pm + c')) :
    ∃ q, Float.toRat ((t.rebase o).apply (x - o)) = some q ∧
      ratAbs (q - (a * b + d)) ≤
        (ratAbs (a * (b - w)) + ratAbs (a * w) + ratAbs d) / scaleTwoPow 1 50 := by
  obtain ⟨po, hpo, e_po⟩ := approx_rel (Float.approximates_mul hs ho n1)
  obtain ⟨c', hc', e_c⟩ := approx_rel (Float.approximates_add hpo hc (n2 po hpo))
  obtain ⟨xo, hxo, e_xo⟩ := approx_rel (Float.approximates_sub hx ho n3)
  obtain ⟨pm, hpm, e_pm⟩ := approx_rel (Float.approximates_mul hs hxo (n4 xo hxo))
  obtain ⟨z, hz, e_z⟩ := approx_rel (Float.approximates_add hpm hc' (n5 pm c' hpm hc'))
  refine ⟨z, ?_, ?_⟩
  · simpa [Affine.apply, Affine.rebase] using hz
  · have := rebased_core a b w d xo po pm c' z _ k_facts.1 k_facts.2 e_po e_c e_xo e_pm e_z
    rw [Rat.div_def, ← k_eight]
    grind

/-- That no intermediate result of `s.map x` overflows or falls into the subnormal range, for the
exact values of the inputs and of the intermediate floats. -/
def Linear.NormalSteps (s : Linear Float) (x : Float) : Prop :=
  ∀ X P Q R S : Rat, Float.toRat x = some X → Float.toRat s.domainStart = some P →
    Float.toRat s.domainEnd = some Q → Float.toRat s.rangeStart = some R →
    Float.toRat s.rangeEnd = some S →
    NormalRange (X - P) ∧ NormalRange (S - R) ∧ NormalRange (Q - P) ∧
    (∀ t1 t2, Float.toRat (x - s.domainStart) = some t1 →
      Float.toRat (s.rangeEnd - s.rangeStart) = some t2 → NormalRange (t1 * t2)) ∧
    (∀ t4 t3, Float.toRat ((x - s.domainStart) * (s.rangeEnd - s.rangeStart)) = some t4 →
      Float.toRat (s.domainEnd - s.domainStart) = some t3 → NormalRange (t4 / t3)) ∧
    (∀ t5, Float.toRat ((x - s.domainStart) * (s.rangeEnd - s.rangeStart) /
        (s.domainEnd - s.domainStart)) = some t5 → NormalRange (R + t5))

/-- The Float linear map is within `(|u| + |rangeStart|) / 2 ^ 49` of the exact map of the
exact values of its inputs, where `u` is the exact `(x - domainStart) * (rangeEnd - rangeStart) /
(domainEnd - domainStart)`, given a nondegenerate domain and that no intermediate result overflows
or falls into the subnormal range. -/
theorem Linear.map_float_error (s : Linear Float) (x : Float) {X P Q R S : Rat}
    (hx : Float.toRat x = some X) (hp : Float.toRat s.domainStart = some P)
    (hq : Float.toRat s.domainEnd = some Q) (hr : Float.toRat s.rangeStart = some R)
    (hs : Float.toRat s.rangeEnd = some S) (hC : Q - P ≠ 0) (hn : Linear.NormalSteps s x) :
    ∃ q, Float.toRat (s.map x) = some q ∧
      ratAbs (q - (R + (X - P) * (S - R) / (Q - P))) ≤
        (ratAbs ((X - P) * (S - R) / (Q - P)) + ratAbs R) / scaleTwoPow 1 49 := by
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hn X P Q R S hx hp hq hr hs
  obtain ⟨t1, h1, e1⟩ := approx_rel (Float.approximates_sub hx hp n1)
  obtain ⟨t2, h2, e2⟩ := approx_rel (Float.approximates_sub hs hr n2)
  obtain ⟨t4, h4, e4⟩ := approx_rel (Float.approximates_mul h1 h2 (n4 t1 t2 h1 h2))
  obtain ⟨t3, h3, e3⟩ := approx_rel (Float.approximates_sub hq hp n3)
  have hne : t3 ≠ 0 := by
    intro h0
    rw [h0] at e3
    have hpos : 0 < ratAbs (Q - P) := by unfold ratAbs; split <;> grind
    have := k_facts
    have := Rat.mul_le_mul_of_nonneg_left (show (scaleTwoPow 1 53)⁻¹ ≤ 1 / 8 from this.2) (Rat.le_of_lt hpos)
    have h' : ratAbs (0 - (Q - P)) = ratAbs (Q - P) := by
      unfold ratAbs; split <;> split <;> grind
    rw [h'] at e3
    grind
  obtain ⟨t5, h5, e5⟩ := approx_rel (Float.approximates_div h4 h3 hne (n5 t4 t3 h4 h3))
  obtain ⟨z, hz, ez⟩ := approx_rel (Float.approximates_add hr h5 (n6 t5 h5))
  refine ⟨z, hz, ?_⟩
  have := lin_core X P Q R S t1 t2 t4 t3 t5 z _ k_facts.1 k_facts.2 hC e1 e2 e4 e3 hne e5 ez
  rw [Rat.div_def _ (scaleTwoPow 1 49), ← k_sixteen]
  grind

/-- The Float rebased linear map at `x - origin`, with the domain rebased in floats,
is within `(|u| + |rangeStart| + t) / 2 ^ 49` of the exact value of the unrebased map at `x`, where
`u` is the exact `(x - domainStart) * (rangeEnd - rangeStart) / (domainEnd - domainStart)` and `t`
is `(|rangeEnd - rangeStart| * (|x - origin| + |domainStart - origin|) + |u| * (|domainEnd - origin|
+ |domainStart - origin|)) / |domainEnd - domainStart|`, the offsets of the point and domain from
the origin scaled to the range. The bound needs the domain to be wider than `2 ^ -52` of its
distance from the origin (`hstable`), and that no intermediate result overflows or falls into the
subnormal range. -/
theorem Linear.rebase_map_float_error (s : Linear Float) (o x : Float) {X W P Q R S : Rat}
    (hx : Float.toRat x = some X) (ho : Float.toRat o = some W)
    (hp : Float.toRat s.domainStart = some P) (hq : Float.toRat s.domainEnd = some Q)
    (hr : Float.toRat s.rangeStart = some R) (hs : Float.toRat s.rangeEnd = some S)
    (hC : Q - P ≠ 0) (n1 : NormalRange (X - W)) (n2 : NormalRange (P - W))
    (n3 : NormalRange (Q - W)) (hn : Linear.NormalSteps (s.rebase o) (x - o))
    (hstable : 2 * (ratAbs (Q - W) + ratAbs (P - W)) ≤ ratAbs (Q - P) * scaleTwoPow 1 53) :
    ∃ q, Float.toRat ((s.rebase o).map (x - o)) = some q ∧
      ratAbs (q - (R + (X - P) * (S - R) / (Q - P))) ≤
        (ratAbs ((X - P) * (S - R) / (Q - P)) + ratAbs R +
          (ratAbs (S - R) * (ratAbs (X - W) + ratAbs (P - W)) +
            ratAbs ((X - P) * (S - R) / (Q - P)) * (ratAbs (Q - W) + ratAbs (P - W))) /
            ratAbs (Q - P)) / scaleTwoPow 1 49 := by
  obtain ⟨xo, hxo, exo⟩ := approx_rel (Float.approximates_sub hx ho n1)
  obtain ⟨po, hpo, epo⟩ := approx_rel (Float.approximates_sub hp ho n2)
  obtain ⟨qo, hqo, eqo⟩ := approx_rel (Float.approximates_sub hq ho n3)
  have hk := k_facts
  have hsc : scaleTwoPow 1 53 * (scaleTwoPow 1 53)⁻¹ = 1 := by
    have h : scaleTwoPow 1 53 = 9007199254740992 := by
      rw [scaleTwoPow_of_nonneg _ (by decide)]; simp
    rw [h]; grind
  have stab : 2 * (scaleTwoPow 1 53)⁻¹ * (ratAbs (Q - W) + ratAbs (P - W)) ≤ ratAbs (Q - P) := by
    have := Rat.mul_le_mul_of_nonneg_right hstable hk.1
    rw [Rat.mul_assoc _ (scaleTwoPow 1 53), hsc, Rat.mul_one] at this
    grind
  obtain ⟨hne, hsens⟩ := sens X W P Q R S xo po qo _ hC exo epo eqo stab
  obtain ⟨q, hq', eq⟩ := Linear.map_float_error (s.rebase o) (x - o) (X := xo) (P := po)
    (Q := qo) (R := R) (S := S) hxo hpo hqo hr hs hne hn
  refine ⟨q, hq', ?_⟩
  generalize hu : (X - P) * (S - R) / (Q - P) = u at *
  generalize hu' : (xo - po) * (S - R) / (qo - po) = u' at *
  have hCpos : 0 < ratAbs (Q - P) := by unfold ratAbs; split <;> grind
  have hCne : ratAbs (Q - P) ≠ 0 := by grind
  have hnum : 0 ≤ ratAbs (S - R) * (ratAbs (X - W) + ratAbs (P - W)) +
      ratAbs u * (ratAbs (Q - W) + ratAbs (P - W)) :=
    Rat.add_nonneg
      (Rat.mul_nonneg (ratAbs_nonneg _) (Rat.add_nonneg (ratAbs_nonneg _) (ratAbs_nonneg _)))
      (Rat.mul_nonneg (ratAbs_nonneg _) (Rat.add_nonneg (ratAbs_nonneg _) (ratAbs_nonneg _)))
  generalize ratAbs (S - R) * (ratAbs (X - W) + ratAbs (P - W)) +
    ratAbs u * (ratAbs (Q - W) + ratAbs (P - W)) = num at *
  have hT : num / ratAbs (Q - P) * ratAbs (Q - P) = num := Rat.div_mul_cancel hCne
  generalize num / ratAbs (Q - P) = T at *
  have hd : ratAbs (u' - u) ≤ 2 * (scaleTwoPow 1 53)⁻¹ * T := by
    apply Rat.le_of_mul_le_mul_right _ hCpos
    have : 2 * (scaleTwoPow 1 53)⁻¹ * T * ratAbs (Q - P) = 2 * (scaleTwoPow 1 53)⁻¹ * num := by
      rw [Rat.mul_assoc, hT]
    rw [this]; exact hsens
  rw [Rat.div_def _ (scaleTwoPow 1 49), ← k_sixteen]
  rw [Rat.div_def _ (scaleTwoPow 1 49), ← k_sixteen] at eq
  have t := ratAbs_add_le (q - (R + u')) (u' - u)
  have t' := ratAbs_add_le (u' - u) u
  have e : q - (R + u) = (q - (R + u')) + (u' - u) := by grind
  rw [e]
  have nd := ratAbs_nonneg (u' - u)
  have nu := ratAbs_nonneg u
  have nR := ratAbs_nonneg R
  have a1 := Rat.mul_le_mul_of_nonneg_left hk.2 nd
  have a2 := Rat.mul_le_mul_of_nonneg_right
    (show ratAbs u' ≤ ratAbs u + ratAbs (u' - u) by
      have e' : u' = u + (u' - u) := by grind
      rw [e']; have := ratAbs_add_le u (u' - u); grind) (show (0:Rat) ≤ 16 * (scaleTwoPow 1 53)⁻¹ by grind)
  have ndT : 0 ≤ T := by
    by_cases h : T < 0
    · have := Rat.mul_pos (show 0 < -T by grind) hCpos
      grind
    · grind
  have a3 := Rat.mul_nonneg hk.1 ndT
  grind

end Inkproof.Scale
