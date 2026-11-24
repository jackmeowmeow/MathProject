import Mathlib
import Mathlib.Order.Filter.Germ.Basic

/-!
Proposed changings to Filter.Product

Proposed solution in Zulip:

instance : CoeSort (Filter α) (Type _) where coe f := f.sets
instance (f : Filter α) : CoeSort f (Type _) where coe s := s

def Filter.betterProductSetoid (l : Filter α) (ε : α → Type*) :
    Setoid ((s : l) × ((a : s) → ε a)) where
  r := fun ⟨s,f⟩ ⟨t,g⟩ => ∃ (u : l) (hs : u ≤ s) (ht : u ≤ t),
    ∀ x : u, f ⟨x, hs x.prop⟩ = g ⟨x, ht x.prop⟩
  iseqv := sorry

def Filter.betterProduct (l : Filter α) (ε : α → Type*) :=
    Quotient <| l.betterProductSetoid ε

-/
open Set Filter

namespace Product

-- Why the current product fails.
-- When one of the object is empty the whole product turns out to be empty
-- Let us define the fiber:

def A (i : ℕ) := Finset.range i

-- the first fiber here is empty
theorem zero_fiber_is_empty : IsEmpty (A 0) :=
  ⟨fun n => List.not_mem_nil n.property⟩

-- The current implementation collaps to the empty product
theorem mathlib_product_empty (F : Filter ℕ) :
    IsEmpty (Filter.Product F (fun i => (A i : Type))) := by
  constructor
  intro x
  unfold Filter.Product at x
  exact Quotient.inductionOn x
    (fun f => zero_fiber_is_empty.false (f 0))

/- This happens because there is a total function parsing every element of the index
 If we consider the \sim_F relation between two functions it asks for the set of index where the
 functions agree to be in the filter F.
 Basically the equivalence relation is defined almost everywhere but
 the representative are required to be defined everywhere.
 The goal is to generalize this construction to "almost every" index.
 So,let's consider the set $P_mathcal{F}(A) = {(D,f) : D ∈ mathcal{F}, f in prod_i∈D A_i}$
 Here the representative is a dependent function defined on some filter large subset of the set I
 So here we define the equivalence (D,f) ∼_F (E,g) iff
 {i ∈ D ∩ E : f(i)= g(i)} ∈ F

 On why it is often ignored:
 Source: https://mathoverflow.net/questions/55989/ultraproducts-and-the-empty-set-/


/- Define a partial function only on positive integers-/
def A_prime (i : {n : ℕ // n ≠ 0}) :=
  Finset.range (i : ℕ)

end Product
