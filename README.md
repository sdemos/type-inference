Formalization of a type inference approach using rewriting semantics. The
formalizations cover STLC, UTLC, and the Hindley/Milner calculus.

For STLC, we have a proof that the rewriting inference is equivalent to the
typed expression, as well as preservation and the non-confluence of the
rewriting relation. 

For UTLC, we show that the type erasure that generated the UTLC expression from
the STLC one still allows for a rewriting relation for type inference, with a
proof for the soundness and completeness of the relation.

For the Hindley/Milner calculus, we prove that the rewriting rules are
equivalent to the result of the well known algorithm W.
