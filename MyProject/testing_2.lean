import MyProject.testing

lemma whatever2 (x y : PNat) : x + y + x + y = x + x + y + y := by
  refine (add_left_inj y).mpr ?_
  pnat_to_nat
  omega

#print whatever
#print Option
