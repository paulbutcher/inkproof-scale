/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scale.Linear

universe u

namespace Inkproof.Scale

/-- A linear scale whose domain satisfies the consumer's constraint `P`, which takes `domainStart`
and `domainEnd`. The proof is erased at run time; a scale is built only by `Linear.check?` or
`withDomain?`, which test `P`, or from a proof. -/
structure Constrained (α : Type u) (P : α → α → Prop) where
  scale : Linear α
  holds : P scale.domainStart scale.domainEnd

/-- The domain from `a` to `b`, in either direction, contains `v`; for example `Includes 0` is "the
domain always includes zero". -/
def Includes {α : Type u} [LE α] (v a b : α) : Prop :=
  (a ≤ v ∧ v ≤ b) ∨ (b ≤ v ∧ v ≤ a)

instance {α : Type u} [LE α] [DecidableLE α] (v a b : α) : Decidable (Includes v a b) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The domain end points moved outward, if need be, until the domain contains `v`, keeping its
direction; see `widen_includes`, `widen_outward` and `widen_of_includes`. -/
def Includes.widen {α : Type u} [LE α] [DecidableLE α] (v a b : α) : α × α :=
  if a ≤ b then (if v ≤ a then v else a, if b ≤ v then v else b)
  else (if a ≤ v then v else a, if v ≤ b then v else b)

namespace Linear

variable {α : Type u}

/-- The scale with its constraint, if its domain meets `P`; see `check?_eq_some` and
`check?_eq_none`. -/
def check? (P : α → α → Prop) [∀ a b, Decidable (P a b)] (s : Linear α) :
    Option (Constrained α P) :=
  if h : P s.domainStart s.domainEnd then some ⟨s, h⟩ else none

end Linear

namespace Constrained

variable {α : Type u} {P : α → α → Prop}

/-- The scale with its domain replaced by `a` to `b`, if that still meets `P`; for a zoom or pan of
a constrained scale. -/
def withDomain? [∀ a b, Decidable (P a b)] (c : Constrained α P) (a b : α) :
    Option (Constrained α P) :=
  Linear.check? P { c.scale with domainStart := a, domainEnd := b }

end Constrained

end Inkproof.Scale
