/- Run with `lake env lean Axioms.lean` after `lake build`.
Each main theorem should depend only on `propext`, `Classical.choice` and `Quot.sound`. -/
import Superposition

#print axioms infsuper_subsolution
#print axioms infsuper_supersolution
#print axioms infsuper_solution
#print axioms superposition_common_subsolution
#print axioms superposition_cone_above
#print axioms superposition_cone_below
#print axioms superposition_cone_both
