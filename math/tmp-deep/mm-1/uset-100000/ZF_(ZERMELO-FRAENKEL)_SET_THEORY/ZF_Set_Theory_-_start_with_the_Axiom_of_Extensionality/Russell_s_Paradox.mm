$[ turnstile_special_source.mm $]

$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/Conditional_equality_(experimental).mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                    Russell's Paradox

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(Russell's Paradox.  Proposition 4.14 of [TakeutiZaring] p. 14.

       In the late 1800s, Frege's Axiom of (unrestricted) Comprehension,
       expressed in our notation as ` A e. _V ` , asserted that any collection
       of sets ` A ` is a set i.e. belongs to the universe ` _V ` of all sets.
       In particular, by substituting ` { x | x e/ x } ` (the "Russell class")
       for ` A ` , it asserted ` { x | x e/ x } e. _V ` , meaning that the
       "collection of all sets which are not members of themselves" is a set.
       However, here we prove ` { x | x e/ x } e/ _V ` .  This contradiction
       was discovered by Russell in 1901 (published in 1903), invalidating the
       Comprehension Axiom and leading to the collapse of Frege's system.

       In 1908, Zermelo rectified this fatal flaw by replacing Comprehension
       with a weaker Subset (or Separation) Axiom ~ ssex asserting that ` A `
       is a set only when it is smaller than some other set ` B ` .  However,
       Zermelo was then faced with a "chicken and egg" problem of how to show
       ` B ` is a set, leading him to introduce the set-building axioms of Null
       Set ~ 0ex , Pairing ~ prex , Union ~ uniex , Power Set ~ pwex , and
       Infinity ~ omex to give him some starting sets to work with (all of
       which, before Russell's Paradox, were immediate consequences of Frege's
       Comprehension).  In 1922 Fraenkel strengthened the Subset Axiom with our
       present Replacement Axiom ~ funimaex (whose modern formalization is due
       to Skolem, also in 1922).  Thus, in a very real sense Russell's Paradox
       spawned the invention of ZF set theory and completely revised the
       foundations of mathematics!

       Another mainstream formalization of set theory, devised by von Neumann,
       Bernays, and Goedel, uses class variables rather than set variables as
       its primitives.  The axiom system NBG in [Mendelson] p. 225 is suitable
       for a Metamath encoding.  NBG is a conservative extension of ZF in that
       it proves exactly the same theorems as ZF that are expressible in the
       language of ZF. An advantage of NBG is that it is finitely axiomatizable
       - the Axiom of Replacement can be broken down into a finite set of
       formulas that eliminate its wff metavariable.  Finite axiomatizability
       is required by some proof languages (although not by Metamath).  There
       is a stronger version of NBG called Morse-Kelley (axiom system MK in
       [Mendelson] p. 287).

       Russell himself continued in a different direction, avoiding the paradox
       with his "theory of types."  Quine extended Russell's ideas to formulate
       his New Foundations set theory (axiom system NF of [Quine] p. 331).  In
       NF, the collection of all sets is a set, contradicting ZF and NBG set
       theories, and it has other bizarre consequences: when sets become too
       huge (beyond the size of those used in standard mathematics), the Axiom
       of Choice ~ ac4 and Cantor's Theorem ~ canth are provably false!  (See
       ~ ncanth for some intuition behind the latter.)  Recent results (as of
       2014) seem to show that NF is equiconsistent to Z (ZF in which ~ ax-sep
       replaces ~ ax-rep ) with ~ ax-sep restricted to only bounded
       quantifiers.  NF is finitely axiomatizable and can be encoded in
       Metamath using the axioms from T. Hailperin, "A set of axioms for
       logic," _J. Symb.  Logic_ 9:1-19 (1944).

       Under our ZF set theory, every set is a member of the Russell class by
       ~ elirrv (derived from the Axiom of Regularity), so for us the Russell
       class equals the universe ` _V ` (theorem ~ ruv ).  See ~ ruALT for an
       alternate proof of ~ ru derived from that fact.  (Contributed by NM,
       7-Aug-1994.) $)

${
	$v x  $.
	$d x y  $.
	f0_ru $f set x $.
	i0_ru $f set y $.
	p_ru $p |- { x | x e/ x } e/ _V $= i0_ru a_sup_set_class i0_ru a_sup_set_class a_wcel p_pm5.19 f0_ru a_sup_set_class i0_ru a_sup_set_class i0_ru a_sup_set_class p_eleq1 f0_ru a_sup_set_class f0_ru a_sup_set_class a_df-nel f0_ru a_sup_set_class i0_ru a_sup_set_class a_wceq p_id f0_ru a_sup_set_class i0_ru a_sup_set_class a_wceq p_id f0_ru a_sup_set_class i0_ru a_sup_set_class a_wceq f0_ru a_sup_set_class i0_ru a_sup_set_class f0_ru a_sup_set_class i0_ru a_sup_set_class p_eleq12d f0_ru a_sup_set_class i0_ru a_sup_set_class a_wceq f0_ru a_sup_set_class f0_ru a_sup_set_class a_wcel i0_ru a_sup_set_class i0_ru a_sup_set_class a_wcel p_notbid f0_ru a_sup_set_class f0_ru a_sup_set_class a_wnel f0_ru a_sup_set_class f0_ru a_sup_set_class a_wcel a_wn f0_ru a_sup_set_class i0_ru a_sup_set_class a_wceq i0_ru a_sup_set_class i0_ru a_sup_set_class a_wcel a_wn p_syl5bb f0_ru a_sup_set_class i0_ru a_sup_set_class a_wceq f0_ru a_sup_set_class i0_ru a_sup_set_class a_wcel i0_ru a_sup_set_class i0_ru a_sup_set_class a_wcel f0_ru a_sup_set_class f0_ru a_sup_set_class a_wnel i0_ru a_sup_set_class i0_ru a_sup_set_class a_wcel a_wn p_bibi12d f0_ru a_sup_set_class i0_ru a_sup_set_class a_wcel f0_ru a_sup_set_class f0_ru a_sup_set_class a_wnel a_wb i0_ru a_sup_set_class i0_ru a_sup_set_class a_wcel i0_ru a_sup_set_class i0_ru a_sup_set_class a_wcel a_wn a_wb f0_ru i0_ru p_spv f0_ru a_sup_set_class i0_ru a_sup_set_class a_wcel f0_ru a_sup_set_class f0_ru a_sup_set_class a_wnel a_wb f0_ru a_wal i0_ru a_sup_set_class i0_ru a_sup_set_class a_wcel i0_ru a_sup_set_class i0_ru a_sup_set_class a_wcel a_wn a_wb p_mto f0_ru a_sup_set_class f0_ru a_sup_set_class a_wnel f0_ru i0_ru a_sup_set_class p_abeq2 i0_ru a_sup_set_class f0_ru a_sup_set_class f0_ru a_sup_set_class a_wnel f0_ru a_cab a_wceq f0_ru a_sup_set_class i0_ru a_sup_set_class a_wcel f0_ru a_sup_set_class f0_ru a_sup_set_class a_wnel a_wb f0_ru a_wal p_mtbir i0_ru a_sup_set_class f0_ru a_sup_set_class f0_ru a_sup_set_class a_wnel f0_ru a_cab a_wceq i0_ru p_nex i0_ru f0_ru a_sup_set_class f0_ru a_sup_set_class a_wnel f0_ru a_cab p_isset f0_ru a_sup_set_class f0_ru a_sup_set_class a_wnel f0_ru a_cab a_cvv a_wcel i0_ru a_sup_set_class f0_ru a_sup_set_class f0_ru a_sup_set_class a_wnel f0_ru a_cab a_wceq i0_ru a_wex p_mtbir f0_ru a_sup_set_class f0_ru a_sup_set_class a_wnel f0_ru a_cab a_cvv a_df-nel f0_ru a_sup_set_class f0_ru a_sup_set_class a_wnel f0_ru a_cab a_cvv a_wnel f0_ru a_sup_set_class f0_ru a_sup_set_class a_wnel f0_ru a_cab a_cvv a_wcel a_wn p_mpbir $.
$}


