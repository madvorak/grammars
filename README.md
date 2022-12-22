# Grammars formally in Lean

This version is for publication.

## Instructions

In order to install Lean 3, follow the [manual](https://leanprover-community.github.io/get_started.html).

In order to download this project, run `leanproject get madvorak/grammars` in your Unix-like command line.

In order to check that the proofs are correct, run `./mk` from the root directory of this project.\
The script will output `Result: SUCCESS` if everything builds successfully.

## Overview

Below you find what has been completed so far.

### Context-free grammars

[Definition](/src/context_free/cfg.lean)

[Example](/test/cfg_demo.lean)

[Closure under union](/src/context_free/closure_properties/binary/CF_union_CF.lean)

[Closure under concatenation](/src/context_free/closure_properties/binary/CF_concatenation_CF.lean)

[Closure under reversal](/src/context_free/closure_properties/unary/reverse_CF.lean)

[Non-closure under intersection](/src/context_free/closure_properties/binary/CF_intersection_CF.lean) (\*)

[Non-closure under complement](/src/context_free/closure_properties/unary/complement_CF.lean) (\*)

\* missing proof: [Context-free pumping lemma](/src/context_free/cfgPumping.lean)

### Unrestricted grammars

(a.k.a. general grammars, a.k.a. recursively-enumerable grammars, a.k.a. type-0 grammars, a.k.a. grammars)

[Definition](/src/unrestricted/grammar.lean)

[Example](/test/grammar_demo.lean)

[Closure under union](/src/unrestricted/closure_properties/binary/RE_union_RE.lean)

[Closure under concatenation](/src/unrestricted/closure_properties/binary/RE_concatenation_RE.lean)

[Closure under Kleene star](/src/unrestricted/closure_properties/unary/star_RE.lean)

[Closure under reversal](/src/unrestricted/closure_properties/unary/reverse_RE.lean)
