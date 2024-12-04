import equational_theories.HasseDiagram.SCC
import equational_theories.Equations.Basic

open Law

def scc1 : SCC Nat :=
  { laws := [Law1],
    allEquivalent := by
      intro l₁ l₂ h₁ h₂
      rw [List.mem_singleton] at *
      subst h₁; subst h₂
      apply Law.instEquivalence.refl
  }
