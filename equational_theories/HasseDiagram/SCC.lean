import equational_theories.MagmaLaw
import equational_theories.Preorder

namespace Law

protected instance instEquivalence {α} : Equivalence (@MagmaLaw.iff α α) where
  refl := by simp [MagmaLaw.iff]
  trans := MagmaLaw.iff.trans
  symm := MagmaLaw.iff.symm

instance {α} : HasEquiv (MagmaLaw α) where
  Equiv := MagmaLaw.iff

def AllEquivalent {α} (laws : List (MagmaLaw α)) : Prop :=
  ∀ (l₁ l₂ : MagmaLaw α), l₁ ∈ laws → l₂ ∈ laws → l₁ ≈ l₂

structure SCC (α) where
  laws : List (MagmaLaw α)
  allEquivalent : AllEquivalent laws
  nonempty : laws ≠ [] := by decide

def SCC.representative {α} (scc : SCC α) : MagmaLaw α :=
 scc.laws.head scc.nonempty

end Law
