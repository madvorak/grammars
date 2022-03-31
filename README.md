# Formalization of formal grammars

I formalize formal grammars in Lean. I started with context-free grammars. Hopefully, this project will cover the whole Chomsky hierarchy in the future.

## Highlights of what has been done so far

[Main definition](https://github.com/madvorak/grammars/blob/70a1949204f153b1b6a094c0a37f81d9bd5f0a91/src/cfg.lean#L11) of a context-free grammar.

[Example proof](https://github.com/madvorak/grammars/blob/70a1949204f153b1b6a094c0a37f81d9bd5f0a91/test/cfg_demo.lean#L28) that a concrete word belongs to a language of a concrete grammar.

[Example proof](https://github.com/madvorak/grammars/blob/70a1949204f153b1b6a094c0a37f81d9bd5f0a91/test/cfg_demo.lean#L105) of a precise characterisation of a language generated by a concrete grammar.

[Completed proof](https://github.com/madvorak/grammars/blob/main/src/context_free/closure_properties/binary/CF_union_CF.lean) that the class of context-free languages is closed under union.

[Unfinished proof](https://github.com/madvorak/grammars/blob/main/src/context_free/closure_properties/binary/CF_intersection_CF.lean) that the class of context-free languages is not closed under intersection.

[Easy corollary](https://github.com/madvorak/grammars/blob/main/src/context_free/closure_properties/unary/complement_CF.lean) that the class of context-free languages is not closed under complement.