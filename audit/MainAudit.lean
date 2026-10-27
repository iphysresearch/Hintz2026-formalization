import Hintz2026.MainTheorem

set_option autoImplicit false
set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option format.width 120

namespace Hintz2026

#check @main
#print axioms main
#check @main_pos
#print axioms main_pos
#check @main_neg
#print axioms main_neg
#check @main_pos_on_U
#print axioms main_pos_on_U
#check @main_neg_on_U
#print axioms main_neg_on_U

end Hintz2026

/- The audit is primarily checked while this file elaborates.  This empty
   executable entry lets Lake build it as a reproducible audit target. -/
def main : IO Unit := pure ()
