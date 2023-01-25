# Grammars formally in Lean

## Instructions

In order to install Lean 3, follow the [manual](https://leanprover-community.github.io/get_started.html).

In order to download this project, run `leanproject get madvorak/grammars` in your Unix-like command line.

In order to check that the proofs are correct, run `./mk` from the root directory of this project.\
The script will output `Result: SUCCESS` if everything builds successfully.

## Overview

Below you find what has been completed so far.

### Context-free grammars

[Definition](/src/classes/context_free/cfg.lean)

[Example](/test/cfg_demo.lean)

[Closure under union](/src/classes/context_free/closure_properties/binary/CF_union_CF.lean)

[Closure under reversal](/src/classes/context_free/closure_properties/unary/reverse_CF.lean)

[Closure under concatenation](/src/classes/context_free/closure_properties/binary/CF_concatenation_CF.lean)

[Non-closure under intersection](/src/classes/context_free/closure_properties/binary/CF_intersection_CF.lean) (\*)

[Non-closure under complement](/src/classes/context_free/closure_properties/unary/complement_CF.lean) (\*)

\* missing proof: [Context-free pumping lemma](/src/classes/context_free/cfgPumping.lean)

### Context-sensitive grammars

[Example](/test/csg_demo.lean)

### Unrestricted grammars

(a.k.a. general grammars, a.k.a. recursively-enumerable grammars, a.k.a. type-0 grammars, a.k.a. grammars)

[Definition](/src/classes/unrestricted/grammar.lean)

[Example](/test/grammar_demo.lean)

[Closure under union](/src/classes/unrestricted/closure_properties/binary/RE_union_RE.lean)

[Closure under reversal](/src/classes/unrestricted/closure_properties/unary/reverse_RE.lean)

[Closure under concatenation](/src/classes/unrestricted/closure_properties/binary/RE_concatenation_RE.lean)

[Closure under Kleene star](/src/classes/unrestricted/closure_properties/unary/star_RE.lean)
