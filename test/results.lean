import classes.unrestricted.closure_properties.binary.RE_union_RE
import classes.unrestricted.closure_properties.unary.reverse_RE
import classes.unrestricted.closure_properties.binary.RE_concatenation_RE
import classes.unrestricted.closure_properties.unary.star_RE

import classes.context_free.closure_properties.binary.CF_union_CF
import classes.context_free.closure_properties.unary.reverse_CF
import classes.context_free.closure_properties.binary.CF_concatenation_CF
import classes.context_free.closure_properties.binary.CF_intersection_CF
import classes.context_free.closure_properties.unary.complement_CF

import utilities.written_by_others.print_sorries


section unrestricted

#check            RE_of_RE_u_RE
#print_sorries_in RE_of_RE_u_RE

#check            RE_of_reverse_RE
#print_sorries_in RE_of_reverse_RE

#check            RE_of_RE_c_RE
#print_sorries_in RE_of_RE_c_RE

#check            RE_of_star_RE
#print_sorries_in RE_of_star_RE

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
