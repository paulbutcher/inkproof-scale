/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Float.Axioms
import Inkproof.Scale.Affine
import Inkproof.Scale.Linear

namespace Inkproof.Scale

open Inkproof.Float


private theorem step (q p m d k : Rat) (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (h1 : (p - m).abs ≤ m.abs * k)
    (h2 : (q - (p + d)).abs ≤ (p + d).abs * k) :
    (q - (m + d)).abs ≤ 4 * (m.abs + d.abs) * k := by
  have a1 := rat_abs_add_le (q - (p + d)) (p - m)
  have a2 := rat_abs_add_le p d
  have a3 := rat_abs_add_le (p - m) m
  have n1 := (Rat.abs_nonneg (x := m))
  have n2 := (Rat.abs_nonneg (x := d))
  have e : q - (m + d) = (q - (p + d)) + (p - m) := by grind
  rw [e]
  have k1 : m.abs * k ≤ m.abs * 1 := Rat.mul_le_mul_of_nonneg_left hk1 n1
  have k2 : (p + d).abs * k ≤ (3 * m.abs + d.abs) * k :=
    Rat.mul_le_mul_of_nonneg_right (by grind) hk0
  have := Rat.mul_nonneg n2 hk0
  grind

private theorem k_facts : (0 : Rat) ≤ (scaleTwoPow 1 53)⁻¹ ∧ (scaleTwoPow 1 53)⁻¹ ≤ 1 / 8 := by
  have h : scaleTwoPow 1 53 = 9007199254740992 := by
    rw [scaleTwoPow_of_nonneg _ (by decide)]; simp
  rw [h]; constructor <;> grind

private theorem approx_rel {z : Float} {r : Rat} (h : Float.Approximates z r) :
    ∃ q, Float.toRat z = some q ∧ (q - r).abs ≤ r.abs * (scaleTwoPow 1 53)⁻¹ := by
  obtain ⟨q, δ, hq, hδ, e⟩ := h.rel
  refine ⟨q, hq, ?_⟩
  have : q - r = r * δ := by rw [e]; grind
  rw [this, rat_abs_mul, Rat.div_def, Rat.one_mul] at *
  exact Rat.mul_le_mul_of_nonneg_left hδ Rat.abs_nonneg

private theorem mulAbs (a b c : Rat) {k : Rat} (h : b.abs ≤ c.abs * k) :
    (a * b).abs ≤ (a * c).abs * k := by
  rw [rat_abs_mul, rat_abs_mul]
  have := Rat.mul_le_mul_of_nonneg_left h ((Rat.abs_nonneg (x := a)))
  grind

private theorem rebased_core (a b w d xo po pm c' z k : Rat) (hk0 : 0 ≤ k) (hk1 : k ≤ 1 / 8)
    (e_po : (po - a * w).abs ≤ (a * w).abs * k)
    (e_c : (c' - (po + d)).abs ≤ (po + d).abs * k)
    (e_xo : (xo - (b - w)).abs ≤ (b - w).abs * k)
    (e_pm : (pm - a * xo).abs ≤ (a * xo).abs * k)
    (e_z : (z - (pm + c')).abs ≤ (pm + c').abs * k) :
    (z - (a * b + d)).abs ≤ 8 * ((a * (b - w)).abs + (a * w).abs + d.abs) * k := by
  have hc := step c' po (a * w) d k hk0 (by grind) e_po e_c
  have hx := mulAbs a (xo - (b - w)) (b - w) e_xo
  have nU := (Rat.abs_nonneg (x := (a * (b - w))))
  have nW := (Rat.abs_nonneg (x := (a * w)))
  have nD := (Rat.abs_nonneg (x := d))
  have t1 := rat_abs_add_le (a * (b - w)) (a * (xo - (b - w)))
  have t2 := rat_abs_add_le (a * xo - a * (b - w)) (a * (b - w))
  have eq1 : a * xo = a * (b - w) + a * (xo - (b - w)) := by grind
  have eq2 : a * xo - a * (b - w) = a * (xo - (b - w)) := by grind
  have kU : (a * (b - w)).abs * k ≤ (a * (b - w)).abs * (1 / 8) :=
    Rat.mul_le_mul_of_nonneg_left hk1 nU
  have axo : (a * xo).abs ≤ 2 * (a * (b - w)).abs := by rw [eq1]; grind
  have m1 : (a * xo).abs * k ≤ 2 * (a * (b - w)).abs * k :=
    Rat.mul_le_mul_of_nonneg_right axo hk0
  have pm' := rat_abs_add_le (pm - a * xo) (a * xo)
  have pmb : pm.abs ≤ 4 * (a * (b - w)).abs := by
    have : pm = (pm - a * xo) + a * xo := by grind
    rw [this]; have := Rat.mul_le_mul_of_nonneg_left hk1 ((Rat.abs_nonneg (x := (a * xo)))); grind
  have c1 := rat_abs_add_le (c' - (a * w + d)) (a * w + d)
  have c2 := rat_abs_add_le (a * w) d
  have kW : (a * w).abs * k ≤ (a * w).abs * (1 / 8) := Rat.mul_le_mul_of_nonneg_left hk1 nW
  have kD : d.abs * k ≤ d.abs * (1 / 8) := Rat.mul_le_mul_of_nonneg_left hk1 nD
  have cb : c'.abs ≤ 2 * ((a * w).abs + d.abs) := by
    have : c' = (c' - (a * w + d)) + (a * w + d) := by grind
    rw [this]; grind
  have s1 := rat_abs_add_le pm c'
  have m2 : (pm + c').abs * k ≤ (4 * (a * (b - w)).abs + 2 * ((a * w).abs + d.abs)) * k :=
    Rat.mul_le_mul_of_nonneg_right (by grind) hk0
  have f1 := rat_abs_add_le (z - (pm + c')) (pm - a * xo)
  have f2 := rat_abs_add_le (z - (pm + c') + (pm - a * xo)) (a * xo - a * (b - w))
  have f3 := rat_abs_add_le (z - (pm + c') + (pm - a * xo) + (a * xo - a * (b - w))) (c' - (a * w + d))
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
    (h1 : (x - a).abs ≤ a.abs * c1) (h2 : (y - b).abs ≤ b.abs * c2) :
    (x * y - a * b).abs ≤ (a * b).abs * (c1 + c2 + c1 * c2) := by
  have e : x * y - a * b = (x - a) * (y - b) + (x - a) * b + a * (y - b) := by grind
  have t1 := rat_abs_add_le ((x - a) * (y - b) + (x - a) * b) (a * (y - b))
  have t2 := rat_abs_add_le ((x - a) * (y - b)) ((x - a) * b)
  have m1 : ((x - a) * (y - b)).abs ≤ (a.abs * c1) * (b.abs * c2) := by
    rw [rat_abs_mul]
    exact mulLe h1 h2 (Rat.abs_nonneg) (Rat.mul_nonneg (Rat.abs_nonneg) hc1)
  have m2 : ((x - a) * b).abs ≤ (a.abs * c1) * b.abs := by
    rw [rat_abs_mul]
    exact Rat.mul_le_mul_of_nonneg_right h1 (Rat.abs_nonneg)
  have m3 : (a * (y - b)).abs ≤ a.abs * (b.abs * c2) := by
    rw [rat_abs_mul]
    exact Rat.mul_le_mul_of_nonneg_left h2 (Rat.abs_nonneg)
  rw [e, rat_abs_mul a b]
  grind

private theorem round_rel (z x r c k : Rat) (hk : 0 ≤ k)
    (h1 : (x - r).abs ≤ r.abs * c) (h2 : (z - x).abs ≤ x.abs * k) :
    (z - r).abs ≤ r.abs * (c + k + c * k) := by
  have t := rat_abs_add_le (z - x) (x - r)
  have t' := rat_abs_add_le (x - r) r
  have e : z - r = (z - x) + (x - r) := by grind
  have m := Rat.mul_le_mul_of_nonneg_right (show x.abs ≤ r.abs + r.abs * c by grind) hk
  rw [e]
  grind

private theorem div_rel (t4 t3 v A B C u c4 k c : Rat) (hk1 : k < 1)
    (hC : C ≠ 0) (hu : u * C = A * B)
    (h4 : (t4 - A * B).abs ≤ (A * B).abs * c4) (h3 : (t3 - C).abs ≤ C.abs * k)
    (hv : v * t3 = t4) (hc : c4 + k ≤ c * (1 - k)) :
    (v - u).abs ≤ u.abs * c := by
  have hCpos : 0 < C.abs := by
    unfold Rat.abs; split <;> grind
  have e : (v - u) * t3 = (t4 - A * B) + u * (C - t3) := by grind
  have lhs : ((v - u) * t3).abs = (v - u).abs * t3.abs := rat_abs_mul _ _
  have t := rat_abs_add_le (t4 - A * B) (u * (C - t3))
  have hAB : (A * B).abs = u.abs * C.abs := by rw [← hu, rat_abs_mul]
  have hCt : (C - t3).abs = (t3 - C).abs := by
    unfold Rat.abs; split <;> split <;> grind
  have m1 : (u * (C - t3)).abs ≤ u.abs * (C.abs * k) := by
    rw [rat_abs_mul, hCt]
    exact Rat.mul_le_mul_of_nonneg_left h3 (Rat.abs_nonneg)
  have t3b : C.abs * (1 - k) ≤ t3.abs := by
    have := rat_abs_add_le t3 (C - t3)
    have e3 : t3 + (C - t3) = C := by grind
    rw [e3] at this
    grind
  have nv := (Rat.abs_nonneg (x := (v - u)))
  have nu := (Rat.abs_nonneg (x := u))
  have hw : 0 < C.abs * (1 - k) := Rat.mul_pos hCpos (by grind)
  have step1 : (v - u).abs * (C.abs * (1 - k)) ≤ (v - u).abs * t3.abs :=
    Rat.mul_le_mul_of_nonneg_left t3b nv
  have step2 : (v - u).abs * t3.abs ≤ u.abs * C.abs * (c4 + k) := by
    rw [← lhs, e]
    rw [hAB] at h4
    grind
  have step3 : u.abs * C.abs * (c4 + k) ≤ u.abs * C.abs * (c * (1 - k)) :=
    Rat.mul_le_mul_of_nonneg_left hc (Rat.mul_nonneg nu (Rat.abs_nonneg))
  have : (v - u).abs * (C.abs * (1 - k)) ≤ (u.abs * c) * (C.abs * (1 - k)) := by
    grind
  exact Rat.le_of_mul_le_mul_right this hw

private theorem lin_core (X P Q R S t1 t2 t4 t3 t5 z k : Rat) (hk0 : 0 ≤ k) (hk1 : k ≤ 1 / 8)
    (hC : Q - P ≠ 0)
    (e1 : (t1 - (X - P)).abs ≤ (X - P).abs * k)
    (e2 : (t2 - (S - R)).abs ≤ (S - R).abs * k)
    (e4 : (t4 - t1 * t2).abs ≤ (t1 * t2).abs * k)
    (e3 : (t3 - (Q - P)).abs ≤ (Q - P).abs * k) (hne : t3 ≠ 0)
    (e5 : (t5 - t4 / t3).abs ≤ (t4 / t3).abs * k)
    (ez : (z - (R + t5)).abs ≤ (R + t5).abs * k) :
    (z - (R + (X - P) * (S - R) / (Q - P))).abs ≤
      16 * (((X - P) * (S - R) / (Q - P)).abs + R.abs) * k := by
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
  have nu := (Rat.abs_nonneg (x := u))
  have nR := (Rat.abs_nonneg (x := R))
  have t := rat_abs_add_le (z - (R + t5)) (t5 - u)
  have t' := rat_abs_add_le (t5 - u) u
  have t'' := rat_abs_add_le R t5
  have e : z - (R + u) = (z - (R + t5)) + (t5 - u) := by grind
  have a1 := Rat.mul_le_mul_of_nonneg_right (show (R + t5).abs ≤ 3 * u.abs + R.abs by
    have : u.abs * (7 * k + k + 7 * k * k) ≤ u.abs * 2 :=
      Rat.mul_le_mul_of_nonneg_left (by grind) nu
    grind) hk0
  have a2 : u.abs * (7 * k + k + 7 * k * k) ≤ u.abs * (9 * k) :=
    Rat.mul_le_mul_of_nonneg_left (by grind) nu
  have p1 := Rat.mul_nonneg nu hk0
  have p2 := Rat.mul_nonneg nR hk0
  rw [e]
  grind

private theorem sens (X W P Q R S xo po qo k : Rat)
    (hC : Q - P ≠ 0)
    (exo : (xo - (X - W)).abs ≤ (X - W).abs * k)
    (epo : (po - (P - W)).abs ≤ (P - W).abs * k)
    (eqo : (qo - (Q - W)).abs ≤ (Q - W).abs * k)
    (stab : 2 * k * ((Q - W).abs + (P - W).abs) ≤ (Q - P).abs) :
    qo - po ≠ 0 ∧
    ((xo - po) * (S - R) / (qo - po) - (X - P) * (S - R) / (Q - P)).abs * (Q - P).abs ≤
      2 * k * ((S - R).abs * ((X - W).abs + (P - W).abs) +
        ((X - P) * (S - R) / (Q - P)).abs * ((Q - W).abs + (P - W).abs)) := by
  have hCpos : 0 < (Q - P).abs := by unfold Rat.abs; split <;> grind
  have nXW := (Rat.abs_nonneg (x := (X - W)))
  have nPW := (Rat.abs_nonneg (x := (P - W)))
  have nQW := (Rat.abs_nonneg (x := (Q - W)))
  have c1 := rat_abs_add_le (qo - (Q - W)) (-(po - (P - W)))
  have c1' : (-(po - (P - W))).abs = (po - (P - W)).abs := by
    unfold Rat.abs; split <;> split <;> grind
  rw [c1'] at c1
  have dC : ((qo - po) - (Q - P)).abs ≤ k * ((Q - W).abs + (P - W).abs) := by
    have e : (qo - po) - (Q - P) = (qo - (Q - W)) + -(po - (P - W)) := by grind
    rw [e]; grind
  have dA : ((xo - po) - (X - P)).abs ≤ k * ((X - W).abs + (P - W).abs) := by
    have c := rat_abs_add_le (xo - (X - W)) (-(po - (P - W)))
    have c' : (-(po - (P - W))).abs = (po - (P - W)).abs := by
      unfold Rat.abs; split <;> split <;> grind
    rw [c'] at c
    have e : (xo - po) - (X - P) = (xo - (X - W)) + -(po - (P - W)) := by grind
    rw [e]; grind
  have hC' : (Q - P).abs ≤ (qo - po).abs + ((qo - po) - (Q - P)).abs := by
    have := rat_abs_add_le (qo - po) (-((qo - po) - (Q - P)))
    have h' : (-((qo - po) - (Q - P))).abs = ((qo - po) - (Q - P)).abs := by
      unfold Rat.abs; split <;> split <;> grind
    have e : qo - po + -((qo - po) - (Q - P)) = Q - P := by grind
    rw [e, h'] at this; exact this
  have half : (Q - P).abs ≤ 2 * (qo - po).abs := by grind
  have hne : qo - po ≠ 0 := by
    intro h0
    rw [h0] at half
    have : (0 : Rat).abs = 0 := by unfold Rat.abs; simp
    grind
  refine ⟨hne, ?_⟩
  generalize hu : (X - P) * (S - R) / (Q - P) = u
  generalize hu' : (xo - po) * (S - R) / (qo - po) = u'
  have hu1 : u * (Q - P) = (X - P) * (S - R) := by rw [← hu]; exact Rat.div_mul_cancel hC
  have hu2 : u' * (qo - po) = (xo - po) * (S - R) := by rw [← hu']; exact Rat.div_mul_cancel hne
  have e : (u' - u) * (qo - po) = ((xo - po) - (X - P)) * (S - R) + u * ((Q - P) - (qo - po)) := by
    grind
  have lhs : ((u' - u) * (qo - po)).abs = (u' - u).abs * (qo - po).abs := rat_abs_mul _ _
  have t := rat_abs_add_le (((xo - po) - (X - P)) * (S - R)) (u * ((Q - P) - (qo - po)))
  have hsw : ((Q - P) - (qo - po)).abs = ((qo - po) - (Q - P)).abs := by
    unfold Rat.abs; split <;> split <;> grind
  have b1 : (((xo - po) - (X - P)) * (S - R)).abs ≤
      (k * ((X - W).abs + (P - W).abs)) * (S - R).abs := by
    rw [rat_abs_mul]; exact Rat.mul_le_mul_of_nonneg_right dA (Rat.abs_nonneg)
  have b2 : (u * ((Q - P) - (qo - po))).abs ≤
      u.abs * (k * ((Q - W).abs + (P - W).abs)) := by
    rw [rat_abs_mul, hsw]; exact Rat.mul_le_mul_of_nonneg_left dC (Rat.abs_nonneg)
  have h2 : (u' - u).abs * (Q - P).abs ≤ (u' - u).abs * (2 * (qo - po).abs) :=
    Rat.mul_le_mul_of_nonneg_left half (Rat.abs_nonneg)
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
      (q - (a * b + d)).abs ≤
        ((a * (b - w)).abs + (a * w).abs + d.abs) / scaleTwoPow 1 50 := by
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
      (q - (R + (X - P) * (S - R) / (Q - P))).abs ≤
        (((X - P) * (S - R) / (Q - P)).abs + R.abs) / scaleTwoPow 1 49 := by
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hn X P Q R S hx hp hq hr hs
  obtain ⟨t1, h1, e1⟩ := approx_rel (Float.approximates_sub hx hp n1)
  obtain ⟨t2, h2, e2⟩ := approx_rel (Float.approximates_sub hs hr n2)
  obtain ⟨t4, h4, e4⟩ := approx_rel (Float.approximates_mul h1 h2 (n4 t1 t2 h1 h2))
  obtain ⟨t3, h3, e3⟩ := approx_rel (Float.approximates_sub hq hp n3)
  have hne : t3 ≠ 0 := by
    intro h0
    rw [h0] at e3
    have hpos : 0 < (Q - P).abs := by unfold Rat.abs; split <;> grind
    have := k_facts
    have := Rat.mul_le_mul_of_nonneg_left (show (scaleTwoPow 1 53)⁻¹ ≤ 1 / 8 from this.2) (Rat.le_of_lt hpos)
    have h' : (0 - (Q - P)).abs = (Q - P).abs := by
      unfold Rat.abs; split <;> split <;> grind
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
    (hstable : 2 * ((Q - W).abs + (P - W).abs) ≤ (Q - P).abs * scaleTwoPow 1 53) :
    ∃ q, Float.toRat ((s.rebase o).map (x - o)) = some q ∧
      (q - (R + (X - P) * (S - R) / (Q - P))).abs ≤
        (((X - P) * (S - R) / (Q - P)).abs + R.abs +
          ((S - R).abs * ((X - W).abs + (P - W).abs) +
            ((X - P) * (S - R) / (Q - P)).abs * ((Q - W).abs + (P - W).abs)) /
            (Q - P).abs) / scaleTwoPow 1 49 := by
  obtain ⟨xo, hxo, exo⟩ := approx_rel (Float.approximates_sub hx ho n1)
  obtain ⟨po, hpo, epo⟩ := approx_rel (Float.approximates_sub hp ho n2)
  obtain ⟨qo, hqo, eqo⟩ := approx_rel (Float.approximates_sub hq ho n3)
  have hk := k_facts
  have hsc : scaleTwoPow 1 53 * (scaleTwoPow 1 53)⁻¹ = 1 := by
    have h : scaleTwoPow 1 53 = 9007199254740992 := by
      rw [scaleTwoPow_of_nonneg _ (by decide)]; simp
    rw [h]; grind
  have stab : 2 * (scaleTwoPow 1 53)⁻¹ * ((Q - W).abs + (P - W).abs) ≤ (Q - P).abs := by
    have := Rat.mul_le_mul_of_nonneg_right hstable hk.1
    rw [Rat.mul_assoc _ (scaleTwoPow 1 53), hsc, Rat.mul_one] at this
    grind
  obtain ⟨hne, hsens⟩ := sens X W P Q R S xo po qo _ hC exo epo eqo stab
  obtain ⟨q, hq', eq⟩ := Linear.map_float_error (s.rebase o) (x - o) (X := xo) (P := po)
    (Q := qo) (R := R) (S := S) hxo hpo hqo hr hs hne hn
  refine ⟨q, hq', ?_⟩
  generalize hu : (X - P) * (S - R) / (Q - P) = u at *
  generalize hu' : (xo - po) * (S - R) / (qo - po) = u' at *
  have hCpos : 0 < (Q - P).abs := by unfold Rat.abs; split <;> grind
  have hCne : (Q - P).abs ≠ 0 := by grind
  have hnum : 0 ≤ (S - R).abs * ((X - W).abs + (P - W).abs) +
      u.abs * ((Q - W).abs + (P - W).abs) :=
    Rat.add_nonneg
      (Rat.mul_nonneg (Rat.abs_nonneg) (Rat.add_nonneg (Rat.abs_nonneg) (Rat.abs_nonneg)))
      (Rat.mul_nonneg (Rat.abs_nonneg) (Rat.add_nonneg (Rat.abs_nonneg) (Rat.abs_nonneg)))
  generalize (S - R).abs * ((X - W).abs + (P - W).abs) +
    u.abs * ((Q - W).abs + (P - W).abs) = num at *
  have hT : num / (Q - P).abs * (Q - P).abs = num := Rat.div_mul_cancel hCne
  generalize num / (Q - P).abs = T at *
  have hd : (u' - u).abs ≤ 2 * (scaleTwoPow 1 53)⁻¹ * T := by
    apply Rat.le_of_mul_le_mul_right _ hCpos
    have : 2 * (scaleTwoPow 1 53)⁻¹ * T * (Q - P).abs = 2 * (scaleTwoPow 1 53)⁻¹ * num := by
      rw [Rat.mul_assoc, hT]
    rw [this]; exact hsens
  rw [Rat.div_def _ (scaleTwoPow 1 49), ← k_sixteen]
  rw [Rat.div_def _ (scaleTwoPow 1 49), ← k_sixteen] at eq
  have t := rat_abs_add_le (q - (R + u')) (u' - u)
  have t' := rat_abs_add_le (u' - u) u
  have e : q - (R + u) = (q - (R + u')) + (u' - u) := by grind
  rw [e]
  have nd := (Rat.abs_nonneg (x := (u' - u)))
  have nu := (Rat.abs_nonneg (x := u))
  have nR := (Rat.abs_nonneg (x := R))
  have a1 := Rat.mul_le_mul_of_nonneg_left hk.2 nd
  have a2 := Rat.mul_le_mul_of_nonneg_right
    (show u'.abs ≤ u.abs + (u' - u).abs by
      have e' : u' = u + (u' - u) := by grind
      rw [e']; have := rat_abs_add_le u (u' - u); grind) (show (0:Rat) ≤ 16 * (scaleTwoPow 1 53)⁻¹ by grind)
  have ndT : 0 ≤ T := by
    by_cases h : T < 0
    · have := Rat.mul_pos (show 0 < -T by grind) hCpos
      grind
    · grind
  have a3 := Rat.mul_nonneg hk.1 ndT
  grind

end Inkproof.Scale
