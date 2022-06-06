import context_free.closure_properties.unary.reverse_CF
import context_free.closure_properties.binary.CF_concatenation_CF
import context_free.closure_properties.binary.CF_union_CF
import context_free.closure_properties.binary.CF_intersection_CF
import context_free.closure_properties.unary.complement_CF

import unrestricted.closure_properties.unary.reverse_RE
import unrestricted.closure_properties.binary.RE_union_RE


section contextfree

#check        CF_of_reverse_CF
#print axioms CF_of_reverse_CF

#check        CF_of_CF_c_CF
#print axioms CF_of_CF_c_CF

#check        CF_of_CF_u_CF
#print axioms CF_of_CF_u_CF

#check        nnyCF_of_CF_i_CF
#print axioms nnyCF_of_CF_i_CF

#check        nnyCF_of_complement_CF
#print axioms nnyCF_of_complement_CF

end contextfree


section unrestricted

#check        RE_of_reverse_RE
#print axioms RE_of_reverse_RE

#check        RE_of_RE_u_RE
#print axioms RE_of_RE_u_RE

end unrestricted
