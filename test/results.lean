import classes.general.closure_properties.union
import classes.general.closure_properties.reverse
import classes.general.closure_properties.concatenation
import classes.general.closure_properties.star

import classes.context_free.closure_properties.union
import classes.context_free.closure_properties.reverse
import classes.context_free.closure_properties.concatenation
import classes.context_free.closure_properties.intersection
import classes.context_free.closure_properties.complement

import utilities.written_by_others.print_sorries

open grammars

section unrestricted

#check            T0_of_T0_u_T0
#print_sorries_in T0_of_T0_u_T0

#check            T0_of_reverse_T0
#print_sorries_in T0_of_reverse_T0

#check            T0_of_T0_c_T0
#print_sorries_in T0_of_T0_c_T0

#check            T0_of_star_T0
#print_sorries_in T0_of_star_T0

end unrestricted


section context_free

#check            CF_of_CF_u_CF
#print_sorries_in CF_of_CF_u_CF

#check            CF_of_reverse_CF
#print_sorries_in CF_of_reverse_CF

#check            CF_of_CF_c_CF
#print_sorries_in CF_of_CF_c_CF

#check            nnyCF_of_CF_i_CF
#print_sorries_in nnyCF_of_CF_i_CF

#check            nnyCF_of_complement_CF
#print_sorries_in nnyCF_of_complement_CF

end context_free
