import Superposition.Preamble
/-- A domain: a nonempty, open, connected subset. (`IsConnected` includes nonemptiness.) -/
def IsOpenDomain {X : Type*} [TopologicalSpace X] (Ω : Set X) : Prop :=
  IsOpen Ω ∧ IsConnected Ω
