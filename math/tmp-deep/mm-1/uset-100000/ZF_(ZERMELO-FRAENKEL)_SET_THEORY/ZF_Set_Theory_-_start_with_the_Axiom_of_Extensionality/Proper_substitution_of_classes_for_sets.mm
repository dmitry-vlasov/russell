$[ turnstile_special_source.mm $]

$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/Russell_s_Paradox.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Proper substitution of classes for sets

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$c [. $.

$c ]. $.

$(Extend wff notation to include the proper substitution of a class for a
     set.  Read this notation as "the proper substitution of class ` A ` for
     set variable ` x ` in wff ` ph ` ." $)

${
	$v ph x A  $.
	f0_wsbc $f wff ph $.
	f1_wsbc $f set x $.
	f2_wsbc $f class A $.
	a_wsbc $a wff [. A / x ]. ph $.
$}

$(Define the proper substitution of a class for a set.

     When ` A ` is a proper class, our definition evaluates to false.  This is
     somewhat arbitrary: we could have, instead, chosen the conclusion of
     ~ sbc6 for our definition, which always evaluates to true for proper
     classes.

     Our definition also does not produce the same results as discussed in the
     proof of Theorem 6.6 of [Quine] p. 42 (although Theorem 6.6 itself does
     hold, as shown by ~ dfsbcq below).  For example, if ` A ` is a proper
     class, Quine's substitution of ` A ` for ` y ` in ` 0 e. y ` evaluates to
     ` 0 e. A ` rather than our falsehood.  (This can be seen by substituting
     ` A ` , ` y ` , and ` 0 ` for alpha, beta, and gamma in Subcase 1 of
     Quine's discussion on p. 42.)  Unfortunately, Quine's definition requires
     a recursive syntactical breakdown of ` ph ` , and it does not seem
     possible to express it with a single closed formula.

     If we did not want to commit to any specific proper class behavior, we
     could use this definition _only_ to prove theorem ~ dfsbcq , which holds
     for both our definition and Quine's, and from which we can derive a weaker
     version of ~ df-sbc in the form of ~ sbc8g .  However, the behavior of
     Quine's definition at proper classes is similarly arbitrary, and for
     practical reasons (to avoid having to prove sethood of ` A ` in every use
     of this definition) we allow direct reference to ~ df-sbc and assert that
     ` [. A / x ]. ph ` is always false when ` A ` is a proper class.

     The theorem ~ sbc2or shows the apparently "strongest" statement we can
     make regarding behavior at proper classes if we start from ~ dfsbcq .

     The related definition ~ df-csb defines proper substitution into a class
     variable (as opposed to a wff variable).  (Contributed by NM,
     14-Apr-1995.)  (Revised by NM, 25-Dec-2016.) $)

${
	$v ph x A  $.
	f0_df-sbc $f wff ph $.
	f1_df-sbc $f set x $.
	f2_df-sbc $f class A $.
	a_df-sbc $a |- ( [. A / x ]. ph <-> A e. { x | ph } ) $.
$}

$(--- Start of old code before overloading prevention patch. $)

$(@( Extend wff notation to include the proper substitution of a class for a
     set.  This definition "overloads" the previously defined variable
     substitution ~ wsb (where the first argument is a set variable rather
     than a class variable).  We take care to ensure that this new definition
     is a conservative extension.  Read this notation as "the proper
     substitution of class ` A ` for set variable ` x ` in wff ` ph ` ." @)
  wsbcSBC @a wff [ A / x ] ph @.
  $)

$(--- End of old code before overloading prevention patch. $)

$(This theorem, which is similar to Theorem 6.7 of [Quine] p. 42 and holds
     under both our definition and Quine's, provides us with a weak definition
     of the proper substitution of a class for a set.  Since our ~ df-sbc does
     not result in the same behavior as Quine's for proper classes, if we
     wished to avoid conflict with Quine's definition we could start with this
     theorem and ~ dfsbcq2 instead of ~ df-sbc .  ( ~ dfsbcq2 is needed because
     unlike Quine we do not overload the ~ df-sb syntax.)  As a consequence of
     these theorems, we can derive ~ sbc8g , which is a weaker version of
     ~ df-sbc that leaves substitution undefined when ` A ` is a proper class.

     However, it is often a nuisance to have to prove the sethood hypothesis of
     ~ sbc8g , so we will allow direct use of ~ df-sbc after theorem ~ sbc2or
     below.  Proper substiution with a proper class is rarely needed, and when
     it is, we can simply use the expansion of Quine's definition.
     (Contributed by NM, 14-Apr-1995.) $)

${
	$v ph x A B  $.
	f0_dfsbcq $f wff ph $.
	f1_dfsbcq $f set x $.
	f2_dfsbcq $f class A $.
	f3_dfsbcq $f class B $.
	p_dfsbcq $p |- ( A = B -> ( [. A / x ]. ph <-> [. B / x ]. ph ) ) $= f2_dfsbcq f3_dfsbcq f0_dfsbcq f1_dfsbcq a_cab p_eleq1 f0_dfsbcq f1_dfsbcq f2_dfsbcq a_df-sbc f0_dfsbcq f1_dfsbcq f3_dfsbcq a_df-sbc f2_dfsbcq f3_dfsbcq a_wceq f2_dfsbcq f0_dfsbcq f1_dfsbcq a_cab a_wcel f3_dfsbcq f0_dfsbcq f1_dfsbcq a_cab a_wcel f0_dfsbcq f1_dfsbcq f2_dfsbcq a_wsbc f0_dfsbcq f1_dfsbcq f3_dfsbcq a_wsbc p_3bitr4g $.
$}

$(This theorem, which is similar to Theorem 6.7 of [Quine] p. 42 and holds
     under both our definition and Quine's, relates logic substitution ~ df-sb
     and substitution for class variables ~ df-sbc .  Unlike Quine, we use a
     different syntax for each in order to avoid overloading it.  See remarks
     in ~ dfsbcq .  (Contributed by NM, 31-Dec-2016.) $)

${
	$v ph x y A  $.
	f0_dfsbcq2 $f wff ph $.
	f1_dfsbcq2 $f set x $.
	f2_dfsbcq2 $f set y $.
	f3_dfsbcq2 $f class A $.
	p_dfsbcq2 $p |- ( y = A -> ( [ y / x ] ph <-> [. A / x ]. ph ) ) $= f2_dfsbcq2 a_sup_set_class f3_dfsbcq2 f0_dfsbcq2 f1_dfsbcq2 a_cab p_eleq1 f0_dfsbcq2 f2_dfsbcq2 f1_dfsbcq2 a_df-clab f0_dfsbcq2 f1_dfsbcq2 f3_dfsbcq2 a_df-sbc f0_dfsbcq2 f1_dfsbcq2 f3_dfsbcq2 a_wsbc f3_dfsbcq2 f0_dfsbcq2 f1_dfsbcq2 a_cab a_wcel p_bicomi f2_dfsbcq2 a_sup_set_class f3_dfsbcq2 a_wceq f2_dfsbcq2 a_sup_set_class f0_dfsbcq2 f1_dfsbcq2 a_cab a_wcel f3_dfsbcq2 f0_dfsbcq2 f1_dfsbcq2 a_cab a_wcel f0_dfsbcq2 f1_dfsbcq2 f2_dfsbcq2 a_wsb f0_dfsbcq2 f1_dfsbcq2 f3_dfsbcq2 a_wsbc p_3bitr3g $.
$}

$(Show that ~ df-sb and ~ df-sbc are equivalent when the class term ` A ` in
     ~ df-sbc is a set variable.  This theorem lets us reuse theorems based on
     ~ df-sb for proofs involving ~ df-sbc .  (Contributed by NM,
     31-Dec-2016.)  (Proof modification is discouraged.) $)

${
	$v ph x y  $.
	f0_sbsbc $f wff ph $.
	f1_sbsbc $f set x $.
	f2_sbsbc $f set y $.
	p_sbsbc $p |- ( [ y / x ] ph <-> [. y / x ]. ph ) $= f2_sbsbc a_sup_set_class p_eqid f0_sbsbc f1_sbsbc f2_sbsbc f2_sbsbc a_sup_set_class p_dfsbcq2 f2_sbsbc a_sup_set_class f2_sbsbc a_sup_set_class a_wceq f0_sbsbc f1_sbsbc f2_sbsbc a_wsb f0_sbsbc f1_sbsbc f2_sbsbc a_sup_set_class a_wsbc a_wb a_ax-mp $.
$}

$(Equality theorem for class substitution.  (Contributed by Mario
       Carneiro, 9-Feb-2017.) $)

${
	$v ph x A B  $.
	f0_sbceq1d $f wff ph $.
	f1_sbceq1d $f set x $.
	f2_sbceq1d $f class A $.
	f3_sbceq1d $f class B $.
	e0_sbceq1d $e |- ( ph -> A = B ) $.
	p_sbceq1d $p |- ( ph -> ( [. A / x ]. ph <-> [. B / x ]. ph ) ) $= e0_sbceq1d f0_sbceq1d f1_sbceq1d f2_sbceq1d f3_sbceq1d p_dfsbcq f0_sbceq1d f2_sbceq1d f3_sbceq1d a_wceq f0_sbceq1d f1_sbceq1d f2_sbceq1d a_wsbc f0_sbceq1d f1_sbceq1d f3_sbceq1d a_wsbc a_wb p_syl $.
$}

$(Equality theorem for class substitution.  (Contributed by Mario
       Carneiro, 9-Feb-2017.) $)

${
	$v ph x A B  $.
	f0_sbceq1dd $f wff ph $.
	f1_sbceq1dd $f set x $.
	f2_sbceq1dd $f class A $.
	f3_sbceq1dd $f class B $.
	e0_sbceq1dd $e |- ( ph -> A = B ) $.
	e1_sbceq1dd $e |- ( ph -> [. A / x ]. ph ) $.
	p_sbceq1dd $p |- ( ph -> [. B / x ]. ph ) $= e1_sbceq1dd e0_sbceq1dd f0_sbceq1dd f1_sbceq1dd f2_sbceq1dd f3_sbceq1dd p_sbceq1d f0_sbceq1dd f0_sbceq1dd f1_sbceq1dd f2_sbceq1dd a_wsbc f0_sbceq1dd f1_sbceq1dd f3_sbceq1dd a_wsbc p_mpbid $.
$}

$(This is the closest we can get to ~ df-sbc if we start from ~ dfsbcq
       (see its comments) and ~ dfsbcq2 .  (Contributed by NM, 18-Nov-2008.)
       (Proof shortened by Andrew Salmon, 29-Jun-2011.)
       (Proof modification is discouraged.) $)

${
	$v ph x A V  $.
	$d y A  $.
	$d y ph  $.
	$d x y  $.
	f0_sbc8g $f wff ph $.
	f1_sbc8g $f set x $.
	f2_sbc8g $f class A $.
	f3_sbc8g $f class V $.
	i0_sbc8g $f set y $.
	p_sbc8g $p |- ( A e. V -> ( [. A / x ]. ph <-> A e. { x | ph } ) ) $= f0_sbc8g f1_sbc8g i0_sbc8g a_sup_set_class f2_sbc8g p_dfsbcq i0_sbc8g a_sup_set_class f2_sbc8g f0_sbc8g f1_sbc8g a_cab p_eleq1 f0_sbc8g i0_sbc8g f1_sbc8g a_df-clab i0_sbc8g p_equid f0_sbc8g f1_sbc8g i0_sbc8g i0_sbc8g a_sup_set_class p_dfsbcq2 i0_sbc8g a_sup_set_class i0_sbc8g a_sup_set_class a_wceq f0_sbc8g f1_sbc8g i0_sbc8g a_wsb f0_sbc8g f1_sbc8g i0_sbc8g a_sup_set_class a_wsbc a_wb a_ax-mp i0_sbc8g a_sup_set_class f0_sbc8g f1_sbc8g a_cab a_wcel f0_sbc8g f1_sbc8g i0_sbc8g a_wsb f0_sbc8g f1_sbc8g i0_sbc8g a_sup_set_class a_wsbc p_bitr2i f0_sbc8g f1_sbc8g i0_sbc8g a_sup_set_class a_wsbc i0_sbc8g a_sup_set_class f0_sbc8g f1_sbc8g a_cab a_wcel f0_sbc8g f1_sbc8g f2_sbc8g a_wsbc f2_sbc8g f0_sbc8g f1_sbc8g a_cab a_wcel i0_sbc8g f2_sbc8g f3_sbc8g p_vtoclbg $.
$}

$(The disjunction of two equivalences for class substitution does not
       require a class existence hypothesis.  This theorem tells us that there
       are only 2 possibilities for ` [ A / x ] ph ` behavior at proper
       classes, matching the ~ sbc5 (false) and ~ sbc6 (true) conclusions.
       This is interesting since ~ dfsbcq and ~ dfsbcq2 (from which it is
       derived) do not appear to say anything obvious about proper class
       behavior.  Note that this theorem doesn't tell us that it is always one
       or the other at proper classes; it could "flip" between false (the first
       disjunct) and true (the second disjunct) as a function of some other
       variable ` y ` that ` ph ` or ` A ` may contain.  (Contributed by NM,
       11-Oct-2004.)  (Proof modification is discouraged.) $)

${
	$v ph x A  $.
	$d x y A  $.
	$d y ph  $.
	f0_sbc2or $f wff ph $.
	f1_sbc2or $f set x $.
	f2_sbc2or $f class A $.
	i0_sbc2or $f set y $.
	p_sbc2or $p |- ( ( [. A / x ]. ph <-> E. x ( x = A /\ ph ) ) \/ ( [. A / x ]. ph <-> A. x ( x = A -> ph ) ) ) $= f0_sbc2or f1_sbc2or i0_sbc2or f2_sbc2or p_dfsbcq2 i0_sbc2or a_sup_set_class f2_sbc2or f1_sbc2or a_sup_set_class p_eqeq2 i0_sbc2or a_sup_set_class f2_sbc2or a_wceq f1_sbc2or a_sup_set_class i0_sbc2or a_sup_set_class a_wceq f1_sbc2or a_sup_set_class f2_sbc2or a_wceq f0_sbc2or p_anbi1d i0_sbc2or a_sup_set_class f2_sbc2or a_wceq f1_sbc2or a_sup_set_class i0_sbc2or a_sup_set_class a_wceq f0_sbc2or a_wa f1_sbc2or a_sup_set_class f2_sbc2or a_wceq f0_sbc2or a_wa f1_sbc2or p_exbidv f0_sbc2or f1_sbc2or i0_sbc2or p_sb5 f0_sbc2or f1_sbc2or i0_sbc2or a_wsb f1_sbc2or a_sup_set_class i0_sbc2or a_sup_set_class a_wceq f0_sbc2or a_wa f1_sbc2or a_wex f0_sbc2or f1_sbc2or f2_sbc2or a_wsbc f1_sbc2or a_sup_set_class f2_sbc2or a_wceq f0_sbc2or a_wa f1_sbc2or a_wex i0_sbc2or f2_sbc2or a_cvv p_vtoclbg f2_sbc2or a_cvv a_wcel f0_sbc2or f1_sbc2or f2_sbc2or a_wsbc f1_sbc2or a_sup_set_class f2_sbc2or a_wceq f0_sbc2or a_wa f1_sbc2or a_wex a_wb f0_sbc2or f1_sbc2or f2_sbc2or a_wsbc f1_sbc2or a_sup_set_class f2_sbc2or a_wceq f0_sbc2or a_wi f1_sbc2or a_wal a_wb p_orcd f0_sbc2or f1_sbc2or f2_sbc2or a_wsbc f1_sbc2or a_sup_set_class f2_sbc2or a_wceq f0_sbc2or a_wa f1_sbc2or a_wex p_pm5.15 f1_sbc2or p_vex f1_sbc2or a_sup_set_class f2_sbc2or a_cvv p_eleq1 f1_sbc2or a_sup_set_class f2_sbc2or a_wceq f1_sbc2or a_sup_set_class a_cvv a_wcel f2_sbc2or a_cvv a_wcel p_mpbii f1_sbc2or a_sup_set_class f2_sbc2or a_wceq f2_sbc2or a_cvv a_wcel f0_sbc2or p_adantr f1_sbc2or a_sup_set_class f2_sbc2or a_wceq f0_sbc2or a_wa f2_sbc2or a_cvv a_wcel p_con3i f2_sbc2or a_cvv a_wcel a_wn f1_sbc2or a_sup_set_class f2_sbc2or a_wceq f0_sbc2or a_wa f1_sbc2or p_nexdv f1_sbc2or p_vex f1_sbc2or a_sup_set_class f2_sbc2or a_cvv p_eleq1 f1_sbc2or a_sup_set_class f2_sbc2or a_wceq f1_sbc2or a_sup_set_class a_cvv a_wcel f2_sbc2or a_cvv a_wcel p_mpbii f1_sbc2or a_sup_set_class f2_sbc2or a_wceq f2_sbc2or a_cvv a_wcel p_con3i f2_sbc2or a_cvv a_wcel a_wn f1_sbc2or a_sup_set_class f2_sbc2or a_wceq f0_sbc2or p_pm2.21d f2_sbc2or a_cvv a_wcel a_wn f1_sbc2or a_sup_set_class f2_sbc2or a_wceq f0_sbc2or a_wi f1_sbc2or p_alrimiv f2_sbc2or a_cvv a_wcel a_wn f1_sbc2or a_sup_set_class f2_sbc2or a_wceq f0_sbc2or a_wa f1_sbc2or a_wex a_wn f1_sbc2or a_sup_set_class f2_sbc2or a_wceq f0_sbc2or a_wi f1_sbc2or a_wal p_2thd f2_sbc2or a_cvv a_wcel a_wn f1_sbc2or a_sup_set_class f2_sbc2or a_wceq f0_sbc2or a_wa f1_sbc2or a_wex a_wn f1_sbc2or a_sup_set_class f2_sbc2or a_wceq f0_sbc2or a_wi f1_sbc2or a_wal f0_sbc2or f1_sbc2or f2_sbc2or a_wsbc p_bibi2d f2_sbc2or a_cvv a_wcel a_wn f0_sbc2or f1_sbc2or f2_sbc2or a_wsbc f1_sbc2or a_sup_set_class f2_sbc2or a_wceq f0_sbc2or a_wa f1_sbc2or a_wex a_wn a_wb f0_sbc2or f1_sbc2or f2_sbc2or a_wsbc f1_sbc2or a_sup_set_class f2_sbc2or a_wceq f0_sbc2or a_wi f1_sbc2or a_wal a_wb f0_sbc2or f1_sbc2or f2_sbc2or a_wsbc f1_sbc2or a_sup_set_class f2_sbc2or a_wceq f0_sbc2or a_wa f1_sbc2or a_wex a_wb p_orbi2d f2_sbc2or a_cvv a_wcel a_wn f0_sbc2or f1_sbc2or f2_sbc2or a_wsbc f1_sbc2or a_sup_set_class f2_sbc2or a_wceq f0_sbc2or a_wa f1_sbc2or a_wex a_wb f0_sbc2or f1_sbc2or f2_sbc2or a_wsbc f1_sbc2or a_sup_set_class f2_sbc2or a_wceq f0_sbc2or a_wa f1_sbc2or a_wex a_wn a_wb a_wo f0_sbc2or f1_sbc2or f2_sbc2or a_wsbc f1_sbc2or a_sup_set_class f2_sbc2or a_wceq f0_sbc2or a_wa f1_sbc2or a_wex a_wb f0_sbc2or f1_sbc2or f2_sbc2or a_wsbc f1_sbc2or a_sup_set_class f2_sbc2or a_wceq f0_sbc2or a_wi f1_sbc2or a_wal a_wb a_wo p_mpbii f2_sbc2or a_cvv a_wcel f0_sbc2or f1_sbc2or f2_sbc2or a_wsbc f1_sbc2or a_sup_set_class f2_sbc2or a_wceq f0_sbc2or a_wa f1_sbc2or a_wex a_wb f0_sbc2or f1_sbc2or f2_sbc2or a_wsbc f1_sbc2or a_sup_set_class f2_sbc2or a_wceq f0_sbc2or a_wi f1_sbc2or a_wal a_wb a_wo p_pm2.61i $.
$}

$(By our definition of proper substitution, it can only be true if the
     substituted expression is a set.  (Contributed by Mario Carneiro,
     13-Oct-2016.) $)

${
	$v ph x A  $.
	f0_sbcex $f wff ph $.
	f1_sbcex $f set x $.
	f2_sbcex $f class A $.
	p_sbcex $p |- ( [. A / x ]. ph -> A e. _V ) $= f0_sbcex f1_sbcex f2_sbcex a_df-sbc f2_sbcex f0_sbcex f1_sbcex a_cab p_elex f0_sbcex f1_sbcex f2_sbcex a_wsbc f2_sbcex f0_sbcex f1_sbcex a_cab a_wcel f2_sbcex a_cvv a_wcel p_sylbi $.
$}

$(Equality theorem for class substitution.  Class version of ~ sbequ12 .
     (Contributed by NM, 26-Sep-2003.) $)

${
	$v ph x A  $.
	f0_sbceq1a $f wff ph $.
	f1_sbceq1a $f set x $.
	f2_sbceq1a $f class A $.
	p_sbceq1a $p |- ( x = A -> ( ph <-> [. A / x ]. ph ) ) $= f0_sbceq1a f1_sbceq1a p_sbid f0_sbceq1a f1_sbceq1a f1_sbceq1a f2_sbceq1a p_dfsbcq2 f0_sbceq1a f0_sbceq1a f1_sbceq1a f1_sbceq1a a_wsb f1_sbceq1a a_sup_set_class f2_sbceq1a a_wceq f0_sbceq1a f1_sbceq1a f2_sbceq1a a_wsbc p_syl5bbr $.
$}

$(Equality theorem for class substitution.  Class version of ~ sbequ12r .
     (Contributed by NM, 4-Jan-2017.) $)

${
	$v ph x A  $.
	f0_sbceq2a $f wff ph $.
	f1_sbceq2a $f set x $.
	f2_sbceq2a $f class A $.
	p_sbceq2a $p |- ( A = x -> ( [. A / x ]. ph <-> ph ) ) $= f0_sbceq2a f1_sbceq2a f2_sbceq2a p_sbceq1a f0_sbceq2a f0_sbceq2a f1_sbceq2a f2_sbceq2a a_wsbc a_wb f1_sbceq2a a_sup_set_class f2_sbceq2a p_eqcoms f2_sbceq2a f1_sbceq2a a_sup_set_class a_wceq f0_sbceq2a f0_sbceq2a f1_sbceq2a f2_sbceq2a a_wsbc p_bicomd $.
$}

$(Specialization: if a formula is true for all sets, it is true for any
       class which is a set.  Similar to Theorem 6.11 of [Quine] p. 44.  See
       also ~ stdpc4 and ~ rspsbc .  (Contributed by NM, 16-Jan-2004.) $)

${
	$v ph x A V  $.
	$d ph y  $.
	$d A y  $.
	$d x y  $.
	f0_spsbc $f wff ph $.
	f1_spsbc $f set x $.
	f2_spsbc $f class A $.
	f3_spsbc $f class V $.
	i0_spsbc $f set y $.
	p_spsbc $p |- ( A e. V -> ( A. x ph -> [. A / x ]. ph ) ) $= f0_spsbc f1_spsbc i0_spsbc p_stdpc4 f0_spsbc f1_spsbc i0_spsbc p_sbsbc f0_spsbc f1_spsbc a_wal f0_spsbc f1_spsbc i0_spsbc a_wsb f0_spsbc f1_spsbc i0_spsbc a_sup_set_class a_wsbc p_sylib f0_spsbc f1_spsbc i0_spsbc a_sup_set_class f2_spsbc p_dfsbcq f0_spsbc f1_spsbc a_wal f0_spsbc f1_spsbc i0_spsbc a_sup_set_class a_wsbc i0_spsbc a_sup_set_class f2_spsbc a_wceq f0_spsbc f1_spsbc f2_spsbc a_wsbc p_syl5ib f0_spsbc f1_spsbc a_wal f0_spsbc f1_spsbc f2_spsbc a_wsbc a_wi i0_spsbc f2_spsbc f3_spsbc p_vtocleg $.
$}

$(Specialization: if a formula is true for all sets, it is true for any
       class which is a set.  Similar to Theorem 6.11 of [Quine] p. 44.  See
       also ~ stdpc4 and ~ rspsbc .  (Contributed by Mario Carneiro,
       9-Feb-2017.) $)

${
	$v ph ps x A V  $.
	$d ph  $.
	$d A  $.
	$d x  $.
	f0_spsbcd $f wff ph $.
	f1_spsbcd $f wff ps $.
	f2_spsbcd $f set x $.
	f3_spsbcd $f class A $.
	f4_spsbcd $f class V $.
	e0_spsbcd $e |- ( ph -> A e. V ) $.
	e1_spsbcd $e |- ( ph -> A. x ps ) $.
	p_spsbcd $p |- ( ph -> [. A / x ]. ps ) $= e0_spsbcd e1_spsbcd f1_spsbcd f2_spsbcd f3_spsbcd f4_spsbcd p_spsbc f0_spsbcd f3_spsbcd f4_spsbcd a_wcel f1_spsbcd f2_spsbcd a_wal f1_spsbcd f2_spsbcd f3_spsbcd a_wsbc p_sylc $.
$}

$(A substitution into a theorem remains true (when ` A ` is a set).
       (Contributed by NM, 5-Nov-2005.) $)

${
	$v ph x A V  $.
	f0_sbcth $f wff ph $.
	f1_sbcth $f set x $.
	f2_sbcth $f class A $.
	f3_sbcth $f class V $.
	e0_sbcth $e |- ph $.
	p_sbcth $p |- ( A e. V -> [. A / x ]. ph ) $= e0_sbcth f0_sbcth f1_sbcth a_ax-gen f0_sbcth f1_sbcth f2_sbcth f3_sbcth p_spsbc f2_sbcth f3_sbcth a_wcel f0_sbcth f1_sbcth a_wal f0_sbcth f1_sbcth f2_sbcth a_wsbc p_mpi $.
$}

$(Deduction version of ~ sbcth .  (Contributed by NM, 30-Nov-2005.)
       (Proof shortened by Andrew Salmon, 8-Jun-2011.) $)

${
	$v ph ps x A V  $.
	$d x ph  $.
	f0_sbcthdv $f wff ph $.
	f1_sbcthdv $f wff ps $.
	f2_sbcthdv $f set x $.
	f3_sbcthdv $f class A $.
	f4_sbcthdv $f class V $.
	e0_sbcthdv $e |- ( ph -> ps ) $.
	p_sbcthdv $p |- ( ( ph /\ A e. V ) -> [. A / x ]. ps ) $= e0_sbcthdv f0_sbcthdv f1_sbcthdv f2_sbcthdv p_alrimiv f1_sbcthdv f2_sbcthdv f3_sbcthdv f4_sbcthdv p_spsbc f0_sbcthdv f1_sbcthdv f2_sbcthdv a_wal f3_sbcthdv f4_sbcthdv a_wcel f1_sbcthdv f2_sbcthdv f3_sbcthdv a_wsbc p_mpan9 $.
$}

$(An identity theorem for substitution.  See ~ sbid .  (Contributed by Mario
     Carneiro, 18-Feb-2017.) $)

${
	$v ph x  $.
	f0_sbcid $f wff ph $.
	f1_sbcid $f set x $.
	p_sbcid $p |- ( [. x / x ]. ph <-> ph ) $= f0_sbcid f1_sbcid f1_sbcid p_sbsbc f0_sbcid f1_sbcid p_sbid f0_sbcid f1_sbcid f1_sbcid a_sup_set_class a_wsbc f0_sbcid f1_sbcid f1_sbcid a_wsb f0_sbcid p_bitr3i $.
$}

$(Deduction version of ~ nfsbc1 .  (Contributed by NM, 23-May-2006.)
       (Revised by Mario Carneiro, 12-Oct-2016.) $)

${
	$v ph ps x A  $.
	f0_nfsbc1d $f wff ph $.
	f1_nfsbc1d $f wff ps $.
	f2_nfsbc1d $f set x $.
	f3_nfsbc1d $f class A $.
	e0_nfsbc1d $e |- ( ph -> F/_ x A ) $.
	p_nfsbc1d $p |- ( ph -> F/ x [. A / x ]. ps ) $= f1_nfsbc1d f2_nfsbc1d f3_nfsbc1d a_df-sbc e0_nfsbc1d f1_nfsbc1d f2_nfsbc1d p_nfab1 f2_nfsbc1d f1_nfsbc1d f2_nfsbc1d a_cab a_wnfc f0_nfsbc1d p_a1i f0_nfsbc1d f2_nfsbc1d f3_nfsbc1d f1_nfsbc1d f2_nfsbc1d a_cab p_nfeld f1_nfsbc1d f2_nfsbc1d f3_nfsbc1d a_wsbc f3_nfsbc1d f1_nfsbc1d f2_nfsbc1d a_cab a_wcel f0_nfsbc1d f2_nfsbc1d p_nfxfrd $.
$}

$(Bound-variable hypothesis builder for class substitution.  (Contributed
       by Mario Carneiro, 12-Oct-2016.) $)

${
	$v ph x A  $.
	f0_nfsbc1 $f wff ph $.
	f1_nfsbc1 $f set x $.
	f2_nfsbc1 $f class A $.
	e0_nfsbc1 $e |- F/_ x A $.
	p_nfsbc1 $p |- F/ x [. A / x ]. ph $= e0_nfsbc1 f1_nfsbc1 f2_nfsbc1 a_wnfc a_wtru p_a1i a_wtru f0_nfsbc1 f1_nfsbc1 f2_nfsbc1 p_nfsbc1d f0_nfsbc1 f1_nfsbc1 f2_nfsbc1 a_wsbc f1_nfsbc1 a_wnf p_trud $.
$}

$(Bound-variable hypothesis builder for class substitution.  (Contributed
       by Mario Carneiro, 12-Oct-2016.) $)

${
	$v ph x A  $.
	$d x A  $.
	f0_nfsbc1v $f wff ph $.
	f1_nfsbc1v $f set x $.
	f2_nfsbc1v $f class A $.
	p_nfsbc1v $p |- F/ x [. A / x ]. ph $= f1_nfsbc1v f2_nfsbc1v p_nfcv f0_nfsbc1v f1_nfsbc1v f2_nfsbc1v p_nfsbc1 $.
$}

$(Deduction version of ~ nfsbc .  (Contributed by NM, 23-Nov-2005.)
       (Revised by Mario Carneiro, 12-Oct-2016.) $)

${
	$v ph ps x y A  $.
	f0_nfsbcd $f wff ph $.
	f1_nfsbcd $f wff ps $.
	f2_nfsbcd $f set x $.
	f3_nfsbcd $f set y $.
	f4_nfsbcd $f class A $.
	e0_nfsbcd $e |- F/ y ph $.
	e1_nfsbcd $e |- ( ph -> F/_ x A ) $.
	e2_nfsbcd $e |- ( ph -> F/ x ps ) $.
	p_nfsbcd $p |- ( ph -> F/ x [. A / y ]. ps ) $= f1_nfsbcd f3_nfsbcd f4_nfsbcd a_df-sbc e1_nfsbcd e0_nfsbcd e2_nfsbcd f0_nfsbcd f1_nfsbcd f2_nfsbcd f3_nfsbcd p_nfabd f0_nfsbcd f2_nfsbcd f4_nfsbcd f1_nfsbcd f3_nfsbcd a_cab p_nfeld f1_nfsbcd f3_nfsbcd f4_nfsbcd a_wsbc f4_nfsbcd f1_nfsbcd f3_nfsbcd a_cab a_wcel f0_nfsbcd f2_nfsbcd p_nfxfrd $.
$}

$(Bound-variable hypothesis builder for class substitution.  (Contributed
       by NM, 7-Sep-2014.)  (Revised by Mario Carneiro, 12-Oct-2016.) $)

${
	$v ph x y A  $.
	f0_nfsbc $f wff ph $.
	f1_nfsbc $f set x $.
	f2_nfsbc $f set y $.
	f3_nfsbc $f class A $.
	e0_nfsbc $e |- F/_ x A $.
	e1_nfsbc $e |- F/ x ph $.
	p_nfsbc $p |- F/ x [. A / y ]. ph $= f2_nfsbc p_nftru e0_nfsbc f1_nfsbc f3_nfsbc a_wnfc a_wtru p_a1i e1_nfsbc f0_nfsbc f1_nfsbc a_wnf a_wtru p_a1i a_wtru f0_nfsbc f1_nfsbc f2_nfsbc f3_nfsbc p_nfsbcd f0_nfsbc f2_nfsbc f3_nfsbc a_wsbc f1_nfsbc a_wnf p_trud $.
$}

$(A composition law for class substitution.  (Contributed by NM,
       26-Sep-2003.)  (Revised by Mario Carneiro, 13-Oct-2016.) $)

${
	$v ph x y A  $.
	$d x z  $.
	$d z A  $.
	$d y z ph  $.
	f0_sbcco $f wff ph $.
	f1_sbcco $f set x $.
	f2_sbcco $f set y $.
	f3_sbcco $f class A $.
	i0_sbcco $f set z $.
	p_sbcco $p |- ( [. A / y ]. [. y / x ]. ph <-> [. A / x ]. ph ) $= f0_sbcco f1_sbcco f2_sbcco a_sup_set_class a_wsbc f2_sbcco f3_sbcco p_sbcex f0_sbcco f1_sbcco f3_sbcco p_sbcex f0_sbcco f1_sbcco f2_sbcco a_sup_set_class a_wsbc f2_sbcco i0_sbcco a_sup_set_class f3_sbcco p_dfsbcq f0_sbcco f1_sbcco i0_sbcco a_sup_set_class f3_sbcco p_dfsbcq f0_sbcco f1_sbcco f2_sbcco p_sbsbc f0_sbcco f1_sbcco f2_sbcco a_wsb f0_sbcco f1_sbcco f2_sbcco a_sup_set_class a_wsbc f2_sbcco i0_sbcco p_sbbii f0_sbcco f2_sbcco p_nfv f0_sbcco f1_sbcco i0_sbcco f2_sbcco p_sbco2 f0_sbcco f1_sbcco f2_sbcco a_sup_set_class a_wsbc f2_sbcco i0_sbcco p_sbsbc f0_sbcco f1_sbcco f2_sbcco a_wsb f2_sbcco i0_sbcco a_wsb f0_sbcco f1_sbcco f2_sbcco a_sup_set_class a_wsbc f2_sbcco i0_sbcco a_wsb f0_sbcco f1_sbcco i0_sbcco a_wsb f0_sbcco f1_sbcco f2_sbcco a_sup_set_class a_wsbc f2_sbcco i0_sbcco a_sup_set_class a_wsbc p_3bitr3ri f0_sbcco f1_sbcco i0_sbcco p_sbsbc f0_sbcco f1_sbcco f2_sbcco a_sup_set_class a_wsbc f2_sbcco i0_sbcco a_sup_set_class a_wsbc f0_sbcco f1_sbcco i0_sbcco a_wsb f0_sbcco f1_sbcco i0_sbcco a_sup_set_class a_wsbc p_bitri f0_sbcco f1_sbcco f2_sbcco a_sup_set_class a_wsbc f2_sbcco i0_sbcco a_sup_set_class a_wsbc f0_sbcco f1_sbcco i0_sbcco a_sup_set_class a_wsbc f0_sbcco f1_sbcco f2_sbcco a_sup_set_class a_wsbc f2_sbcco f3_sbcco a_wsbc f0_sbcco f1_sbcco f3_sbcco a_wsbc i0_sbcco f3_sbcco a_cvv p_vtoclbg f0_sbcco f1_sbcco f2_sbcco a_sup_set_class a_wsbc f2_sbcco f3_sbcco a_wsbc f3_sbcco a_cvv a_wcel f0_sbcco f1_sbcco f3_sbcco a_wsbc p_pm5.21nii $.
$}

$(A composition law for class substitution.  Importantly, ` x ` may occur
       free in the class expression substituted for ` A ` .  (Contributed by
       NM, 5-Sep-2004.)  (Proof shortened by Andrew Salmon, 8-Jun-2011.) $)

${
	$v ph x y A B  $.
	$d x y  $.
	$d y ph  $.
	$d A y  $.
	f0_sbcco2 $f wff ph $.
	f1_sbcco2 $f set x $.
	f2_sbcco2 $f set y $.
	f3_sbcco2 $f class A $.
	f4_sbcco2 $f class B $.
	e0_sbcco2 $e |- ( x = y -> A = B ) $.
	p_sbcco2 $p |- ( [. x / y ]. [. B / x ]. ph <-> [. A / x ]. ph ) $= f0_sbcco2 f1_sbcco2 f4_sbcco2 a_wsbc f2_sbcco2 f1_sbcco2 p_sbsbc f0_sbcco2 f1_sbcco2 f3_sbcco2 a_wsbc f2_sbcco2 p_nfv e0_sbcco2 f3_sbcco2 f4_sbcco2 a_wceq f1_sbcco2 a_sup_set_class f2_sbcco2 a_sup_set_class p_eqcoms f0_sbcco2 f1_sbcco2 f3_sbcco2 f4_sbcco2 p_dfsbcq f3_sbcco2 f4_sbcco2 a_wceq f0_sbcco2 f1_sbcco2 f3_sbcco2 a_wsbc f0_sbcco2 f1_sbcco2 f4_sbcco2 a_wsbc p_bicomd f2_sbcco2 a_sup_set_class f1_sbcco2 a_sup_set_class a_wceq f3_sbcco2 f4_sbcco2 a_wceq f0_sbcco2 f1_sbcco2 f4_sbcco2 a_wsbc f0_sbcco2 f1_sbcco2 f3_sbcco2 a_wsbc a_wb p_syl f0_sbcco2 f1_sbcco2 f4_sbcco2 a_wsbc f0_sbcco2 f1_sbcco2 f3_sbcco2 a_wsbc f2_sbcco2 f1_sbcco2 p_sbie f0_sbcco2 f1_sbcco2 f4_sbcco2 a_wsbc f2_sbcco2 f1_sbcco2 a_sup_set_class a_wsbc f0_sbcco2 f1_sbcco2 f4_sbcco2 a_wsbc f2_sbcco2 f1_sbcco2 a_wsb f0_sbcco2 f1_sbcco2 f3_sbcco2 a_wsbc p_bitr3i $.
$}

$(An equivalence for class substitution.  (Contributed by NM,
       23-Aug-1993.)  (Revised by Mario Carneiro, 12-Oct-2016.) $)

${
	$v ph x A  $.
	$d x y A  $.
	$d y ph  $.
	f0_sbc5 $f wff ph $.
	f1_sbc5 $f set x $.
	f2_sbc5 $f class A $.
	i0_sbc5 $f set y $.
	p_sbc5 $p |- ( [. A / x ]. ph <-> E. x ( x = A /\ ph ) ) $= f0_sbc5 f1_sbc5 f2_sbc5 p_sbcex f1_sbc5 a_sup_set_class f2_sbc5 a_wceq f0_sbc5 f1_sbc5 p_exsimpl f1_sbc5 f2_sbc5 p_isset f1_sbc5 a_sup_set_class f2_sbc5 a_wceq f0_sbc5 a_wa f1_sbc5 a_wex f1_sbc5 a_sup_set_class f2_sbc5 a_wceq f1_sbc5 a_wex f2_sbc5 a_cvv a_wcel p_sylibr f0_sbc5 f1_sbc5 i0_sbc5 f2_sbc5 p_dfsbcq2 i0_sbc5 a_sup_set_class f2_sbc5 f1_sbc5 a_sup_set_class p_eqeq2 i0_sbc5 a_sup_set_class f2_sbc5 a_wceq f1_sbc5 a_sup_set_class i0_sbc5 a_sup_set_class a_wceq f1_sbc5 a_sup_set_class f2_sbc5 a_wceq f0_sbc5 p_anbi1d i0_sbc5 a_sup_set_class f2_sbc5 a_wceq f1_sbc5 a_sup_set_class i0_sbc5 a_sup_set_class a_wceq f0_sbc5 a_wa f1_sbc5 a_sup_set_class f2_sbc5 a_wceq f0_sbc5 a_wa f1_sbc5 p_exbidv f0_sbc5 f1_sbc5 i0_sbc5 p_sb5 f0_sbc5 f1_sbc5 i0_sbc5 a_wsb f1_sbc5 a_sup_set_class i0_sbc5 a_sup_set_class a_wceq f0_sbc5 a_wa f1_sbc5 a_wex f0_sbc5 f1_sbc5 f2_sbc5 a_wsbc f1_sbc5 a_sup_set_class f2_sbc5 a_wceq f0_sbc5 a_wa f1_sbc5 a_wex i0_sbc5 f2_sbc5 a_cvv p_vtoclbg f0_sbc5 f1_sbc5 f2_sbc5 a_wsbc f2_sbc5 a_cvv a_wcel f1_sbc5 a_sup_set_class f2_sbc5 a_wceq f0_sbc5 a_wa f1_sbc5 a_wex p_pm5.21nii $.
$}

$(An equivalence for class substitution.  (Contributed by NM,
       11-Oct-2004.)  (Proof shortened by Andrew Salmon, 8-Jun-2011.) $)

${
	$v ph x A V  $.
	$d x A  $.
	f0_sbc6g $f wff ph $.
	f1_sbc6g $f set x $.
	f2_sbc6g $f class A $.
	f3_sbc6g $f class V $.
	p_sbc6g $p |- ( A e. V -> ( [. A / x ]. ph <-> A. x ( x = A -> ph ) ) ) $= f1_sbc6g a_sup_set_class f2_sbc6g a_wceq f0_sbc6g a_wa f1_sbc6g p_nfe1 f0_sbc6g f1_sbc6g f2_sbc6g p_ceqex f0_sbc6g f1_sbc6g a_sup_set_class f2_sbc6g a_wceq f0_sbc6g a_wa f1_sbc6g a_wex f1_sbc6g f2_sbc6g f3_sbc6g p_ceqsalg f0_sbc6g f1_sbc6g f2_sbc6g p_sbc5 f2_sbc6g f3_sbc6g a_wcel f1_sbc6g a_sup_set_class f2_sbc6g a_wceq f0_sbc6g a_wi f1_sbc6g a_wal f1_sbc6g a_sup_set_class f2_sbc6g a_wceq f0_sbc6g a_wa f1_sbc6g a_wex f0_sbc6g f1_sbc6g f2_sbc6g a_wsbc p_syl6rbbr $.
$}

$(An equivalence for class substitution.  (Contributed by NM,
       23-Aug-1993.)  (Proof shortened by Eric Schmidt, 17-Jan-2007.) $)

${
	$v ph x A  $.
	$d x A  $.
	f0_sbc6 $f wff ph $.
	f1_sbc6 $f set x $.
	f2_sbc6 $f class A $.
	e0_sbc6 $e |- A e. _V $.
	p_sbc6 $p |- ( [. A / x ]. ph <-> A. x ( x = A -> ph ) ) $= e0_sbc6 f0_sbc6 f1_sbc6 f2_sbc6 a_cvv p_sbc6g f2_sbc6 a_cvv a_wcel f0_sbc6 f1_sbc6 f2_sbc6 a_wsbc f1_sbc6 a_sup_set_class f2_sbc6 a_wceq f0_sbc6 a_wi f1_sbc6 a_wal a_wb a_ax-mp $.
$}

$(An equivalence for class substitution in the spirit of ~ df-clab .  Note
       that ` x ` and ` A ` don't have to be distinct.  (Contributed by NM,
       18-Nov-2008.)  (Revised by Mario Carneiro, 13-Oct-2016.) $)

${
	$v ph x y A  $.
	$d y A  $.
	$d y ph  $.
	$d x y  $.
	f0_sbc7 $f wff ph $.
	f1_sbc7 $f set x $.
	f2_sbc7 $f set y $.
	f3_sbc7 $f class A $.
	p_sbc7 $p |- ( [. A / x ]. ph <-> E. y ( y = A /\ [. y / x ]. ph ) ) $= f0_sbc7 f1_sbc7 f2_sbc7 f3_sbc7 p_sbcco f0_sbc7 f1_sbc7 f2_sbc7 a_sup_set_class a_wsbc f2_sbc7 f3_sbc7 p_sbc5 f0_sbc7 f1_sbc7 f3_sbc7 a_wsbc f0_sbc7 f1_sbc7 f2_sbc7 a_sup_set_class a_wsbc f2_sbc7 f3_sbc7 a_wsbc f2_sbc7 a_sup_set_class f3_sbc7 a_wceq f0_sbc7 f1_sbc7 f2_sbc7 a_sup_set_class a_wsbc a_wa f2_sbc7 a_wex p_bitr3i $.
$}

$(Change bound variables in a wff substitution.  (Contributed by Jeff
       Hankins, 19-Sep-2009.)  (Proof shortened by Andrew Salmon,
       8-Jun-2011.) $)

${
	$v ph ps x y A  $.
	f0_cbvsbc $f wff ph $.
	f1_cbvsbc $f wff ps $.
	f2_cbvsbc $f set x $.
	f3_cbvsbc $f set y $.
	f4_cbvsbc $f class A $.
	e0_cbvsbc $e |- F/ y ph $.
	e1_cbvsbc $e |- F/ x ps $.
	e2_cbvsbc $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_cbvsbc $p |- ( [. A / x ]. ph <-> [. A / y ]. ps ) $= e0_cbvsbc e1_cbvsbc e2_cbvsbc f0_cbvsbc f1_cbvsbc f2_cbvsbc f3_cbvsbc p_cbvab f0_cbvsbc f2_cbvsbc a_cab f1_cbvsbc f3_cbvsbc a_cab f4_cbvsbc p_eleq2i f0_cbvsbc f2_cbvsbc f4_cbvsbc a_df-sbc f1_cbvsbc f3_cbvsbc f4_cbvsbc a_df-sbc f4_cbvsbc f0_cbvsbc f2_cbvsbc a_cab a_wcel f4_cbvsbc f1_cbvsbc f3_cbvsbc a_cab a_wcel f0_cbvsbc f2_cbvsbc f4_cbvsbc a_wsbc f1_cbvsbc f3_cbvsbc f4_cbvsbc a_wsbc p_3bitr4i $.
$}

$(Change the bound variable of a class substitution using implicit
       substitution.  (Contributed by NM, 30-Sep-2008.)  (Revised by Mario
       Carneiro, 13-Oct-2016.) $)

${
	$v ph ps x y A  $.
	$d y ph  $.
	$d x ps  $.
	f0_cbvsbcv $f wff ph $.
	f1_cbvsbcv $f wff ps $.
	f2_cbvsbcv $f set x $.
	f3_cbvsbcv $f set y $.
	f4_cbvsbcv $f class A $.
	e0_cbvsbcv $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_cbvsbcv $p |- ( [. A / x ]. ph <-> [. A / y ]. ps ) $= f0_cbvsbcv f3_cbvsbcv p_nfv f1_cbvsbcv f2_cbvsbcv p_nfv e0_cbvsbcv f0_cbvsbcv f1_cbvsbcv f2_cbvsbcv f3_cbvsbcv f4_cbvsbcv p_cbvsbc $.
$}

$(Conversion of implicit substitution to explicit class substitution,
       using a bound-variable hypothesis instead of distinct variables.
       (Closed theorem version of ~ sbciegf .)  (Contributed by NM,
       10-Nov-2005.)  (Revised by Mario Carneiro, 13-Oct-2016.) $)

${
	$v ph ps x A V  $.
	$d x A  $.
	$d ps  $.
	f0_sbciegft $f wff ph $.
	f1_sbciegft $f wff ps $.
	f2_sbciegft $f set x $.
	f3_sbciegft $f class A $.
	f4_sbciegft $f class V $.
	p_sbciegft $p |- ( ( A e. V /\ F/ x ps /\ A. x ( x = A -> ( ph <-> ps ) ) ) -> ( [. A / x ]. ph <-> ps ) ) $= f0_sbciegft f2_sbciegft f3_sbciegft p_sbc5 f0_sbciegft f1_sbciegft p_bi1 f0_sbciegft f1_sbciegft a_wb f0_sbciegft f1_sbciegft a_wi f2_sbciegft a_sup_set_class f3_sbciegft a_wceq p_imim2i f2_sbciegft a_sup_set_class f3_sbciegft a_wceq f0_sbciegft f1_sbciegft a_wb a_wi f2_sbciegft a_sup_set_class f3_sbciegft a_wceq f0_sbciegft f1_sbciegft p_imp3a f2_sbciegft a_sup_set_class f3_sbciegft a_wceq f0_sbciegft f1_sbciegft a_wb a_wi f2_sbciegft a_sup_set_class f3_sbciegft a_wceq f0_sbciegft a_wa f1_sbciegft a_wi f2_sbciegft p_alimi f2_sbciegft a_sup_set_class f3_sbciegft a_wceq f0_sbciegft a_wa f1_sbciegft f2_sbciegft p_19.23t f1_sbciegft f2_sbciegft a_wnf f2_sbciegft a_sup_set_class f3_sbciegft a_wceq f0_sbciegft a_wa f1_sbciegft a_wi f2_sbciegft a_wal f2_sbciegft a_sup_set_class f3_sbciegft a_wceq f0_sbciegft a_wa f2_sbciegft a_wex f1_sbciegft a_wi p_biimpa f2_sbciegft a_sup_set_class f3_sbciegft a_wceq f0_sbciegft f1_sbciegft a_wb a_wi f2_sbciegft a_wal f1_sbciegft f2_sbciegft a_wnf f2_sbciegft a_sup_set_class f3_sbciegft a_wceq f0_sbciegft a_wa f1_sbciegft a_wi f2_sbciegft a_wal f2_sbciegft a_sup_set_class f3_sbciegft a_wceq f0_sbciegft a_wa f2_sbciegft a_wex f1_sbciegft a_wi p_sylan2 f1_sbciegft f2_sbciegft a_wnf f2_sbciegft a_sup_set_class f3_sbciegft a_wceq f0_sbciegft f1_sbciegft a_wb a_wi f2_sbciegft a_wal f2_sbciegft a_sup_set_class f3_sbciegft a_wceq f0_sbciegft a_wa f2_sbciegft a_wex f1_sbciegft a_wi f3_sbciegft f4_sbciegft a_wcel p_3adant1 f0_sbciegft f2_sbciegft f3_sbciegft a_wsbc f2_sbciegft a_sup_set_class f3_sbciegft a_wceq f0_sbciegft a_wa f2_sbciegft a_wex f3_sbciegft f4_sbciegft a_wcel f1_sbciegft f2_sbciegft a_wnf f2_sbciegft a_sup_set_class f3_sbciegft a_wceq f0_sbciegft f1_sbciegft a_wb a_wi f2_sbciegft a_wal a_w3a f1_sbciegft p_syl5bi f0_sbciegft f1_sbciegft p_bi2 f0_sbciegft f1_sbciegft a_wb f1_sbciegft f0_sbciegft a_wi f2_sbciegft a_sup_set_class f3_sbciegft a_wceq p_imim2i f2_sbciegft a_sup_set_class f3_sbciegft a_wceq f0_sbciegft f1_sbciegft a_wb a_wi f2_sbciegft a_sup_set_class f3_sbciegft a_wceq f1_sbciegft f0_sbciegft p_com23 f2_sbciegft a_sup_set_class f3_sbciegft a_wceq f0_sbciegft f1_sbciegft a_wb a_wi f1_sbciegft f2_sbciegft a_sup_set_class f3_sbciegft a_wceq f0_sbciegft a_wi a_wi f2_sbciegft p_alimi f1_sbciegft f2_sbciegft a_sup_set_class f3_sbciegft a_wceq f0_sbciegft a_wi f2_sbciegft p_19.21t f1_sbciegft f2_sbciegft a_wnf f1_sbciegft f2_sbciegft a_sup_set_class f3_sbciegft a_wceq f0_sbciegft a_wi a_wi f2_sbciegft a_wal f1_sbciegft f2_sbciegft a_sup_set_class f3_sbciegft a_wceq f0_sbciegft a_wi f2_sbciegft a_wal a_wi p_biimpa f2_sbciegft a_sup_set_class f3_sbciegft a_wceq f0_sbciegft f1_sbciegft a_wb a_wi f2_sbciegft a_wal f1_sbciegft f2_sbciegft a_wnf f1_sbciegft f2_sbciegft a_sup_set_class f3_sbciegft a_wceq f0_sbciegft a_wi a_wi f2_sbciegft a_wal f1_sbciegft f2_sbciegft a_sup_set_class f3_sbciegft a_wceq f0_sbciegft a_wi f2_sbciegft a_wal a_wi p_sylan2 f1_sbciegft f2_sbciegft a_wnf f2_sbciegft a_sup_set_class f3_sbciegft a_wceq f0_sbciegft f1_sbciegft a_wb a_wi f2_sbciegft a_wal f1_sbciegft f2_sbciegft a_sup_set_class f3_sbciegft a_wceq f0_sbciegft a_wi f2_sbciegft a_wal a_wi f3_sbciegft f4_sbciegft a_wcel p_3adant1 f0_sbciegft f2_sbciegft f3_sbciegft f4_sbciegft p_sbc6g f3_sbciegft f4_sbciegft a_wcel f1_sbciegft f2_sbciegft a_wnf f0_sbciegft f2_sbciegft f3_sbciegft a_wsbc f2_sbciegft a_sup_set_class f3_sbciegft a_wceq f0_sbciegft a_wi f2_sbciegft a_wal a_wb f2_sbciegft a_sup_set_class f3_sbciegft a_wceq f0_sbciegft f1_sbciegft a_wb a_wi f2_sbciegft a_wal p_3ad2ant1 f3_sbciegft f4_sbciegft a_wcel f1_sbciegft f2_sbciegft a_wnf f2_sbciegft a_sup_set_class f3_sbciegft a_wceq f0_sbciegft f1_sbciegft a_wb a_wi f2_sbciegft a_wal a_w3a f1_sbciegft f2_sbciegft a_sup_set_class f3_sbciegft a_wceq f0_sbciegft a_wi f2_sbciegft a_wal f0_sbciegft f2_sbciegft f3_sbciegft a_wsbc p_sylibrd f3_sbciegft f4_sbciegft a_wcel f1_sbciegft f2_sbciegft a_wnf f2_sbciegft a_sup_set_class f3_sbciegft a_wceq f0_sbciegft f1_sbciegft a_wb a_wi f2_sbciegft a_wal a_w3a f0_sbciegft f2_sbciegft f3_sbciegft a_wsbc f1_sbciegft p_impbid $.
$}

$(Conversion of implicit substitution to explicit class substitution.
       (Contributed by NM, 14-Dec-2005.)  (Revised by Mario Carneiro,
       13-Oct-2016.) $)

${
	$v ph ps x A V  $.
	$d x A  $.
	f0_sbciegf $f wff ph $.
	f1_sbciegf $f wff ps $.
	f2_sbciegf $f set x $.
	f3_sbciegf $f class A $.
	f4_sbciegf $f class V $.
	e0_sbciegf $e |- F/ x ps $.
	e1_sbciegf $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_sbciegf $p |- ( A e. V -> ( [. A / x ]. ph <-> ps ) ) $= e0_sbciegf e1_sbciegf f2_sbciegf a_sup_set_class f3_sbciegf a_wceq f0_sbciegf f1_sbciegf a_wb a_wi f2_sbciegf a_ax-gen f0_sbciegf f1_sbciegf f2_sbciegf f3_sbciegf f4_sbciegf p_sbciegft f3_sbciegf f4_sbciegf a_wcel f1_sbciegf f2_sbciegf a_wnf f2_sbciegf a_sup_set_class f3_sbciegf a_wceq f0_sbciegf f1_sbciegf a_wb a_wi f2_sbciegf a_wal f0_sbciegf f2_sbciegf f3_sbciegf a_wsbc f1_sbciegf a_wb p_mp3an23 $.
$}

$(Conversion of implicit substitution to explicit class substitution.
       (Contributed by NM, 10-Nov-2005.) $)

${
	$v ph ps x A V  $.
	$d x A  $.
	$d x ps  $.
	f0_sbcieg $f wff ph $.
	f1_sbcieg $f wff ps $.
	f2_sbcieg $f set x $.
	f3_sbcieg $f class A $.
	f4_sbcieg $f class V $.
	e0_sbcieg $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_sbcieg $p |- ( A e. V -> ( [. A / x ]. ph <-> ps ) ) $= f3_sbcieg f4_sbcieg p_elex f1_sbcieg f2_sbcieg p_nfv e0_sbcieg f0_sbcieg f1_sbcieg f2_sbcieg f3_sbcieg a_cvv p_sbciegf f3_sbcieg f4_sbcieg a_wcel f3_sbcieg a_cvv a_wcel f0_sbcieg f2_sbcieg f3_sbcieg a_wsbc f1_sbcieg a_wb p_syl $.
$}

$(Conversion of implicit substitution to explicit class substitution.
       This version of ~ sbcie avoids a disjointness condition on ` x , A ` by
       substituting twice.  (Contributed by Mario Carneiro, 15-Oct-2016.) $)

${
	$v ph ps ch x y A V  $.
	$d x y  $.
	$d A y  $.
	$d ch y  $.
	$d ph y  $.
	$d ps x  $.
	f0_sbcie2g $f wff ph $.
	f1_sbcie2g $f wff ps $.
	f2_sbcie2g $f wff ch $.
	f3_sbcie2g $f set x $.
	f4_sbcie2g $f set y $.
	f5_sbcie2g $f class A $.
	f6_sbcie2g $f class V $.
	e0_sbcie2g $e |- ( x = y -> ( ph <-> ps ) ) $.
	e1_sbcie2g $e |- ( y = A -> ( ps <-> ch ) ) $.
	p_sbcie2g $p |- ( A e. V -> ( [. A / x ]. ph <-> ch ) ) $= f0_sbcie2g f3_sbcie2g f4_sbcie2g a_sup_set_class f5_sbcie2g p_dfsbcq e1_sbcie2g f0_sbcie2g f3_sbcie2g f4_sbcie2g p_sbsbc f1_sbcie2g f3_sbcie2g p_nfv e0_sbcie2g f0_sbcie2g f1_sbcie2g f3_sbcie2g f4_sbcie2g p_sbie f0_sbcie2g f3_sbcie2g f4_sbcie2g a_sup_set_class a_wsbc f0_sbcie2g f3_sbcie2g f4_sbcie2g a_wsb f1_sbcie2g p_bitr3i f0_sbcie2g f3_sbcie2g f4_sbcie2g a_sup_set_class a_wsbc f1_sbcie2g f0_sbcie2g f3_sbcie2g f5_sbcie2g a_wsbc f2_sbcie2g f4_sbcie2g f5_sbcie2g f6_sbcie2g p_vtoclbg $.
$}

$(Conversion of implicit substitution to explicit class substitution.
       (Contributed by NM, 4-Sep-2004.) $)

${
	$v ph ps x A  $.
	$d x A  $.
	$d x ps  $.
	f0_sbcie $f wff ph $.
	f1_sbcie $f wff ps $.
	f2_sbcie $f set x $.
	f3_sbcie $f class A $.
	e0_sbcie $e |- A e. _V $.
	e1_sbcie $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_sbcie $p |- ( [. A / x ]. ph <-> ps ) $= e0_sbcie e1_sbcie f0_sbcie f1_sbcie f2_sbcie f3_sbcie a_cvv p_sbcieg f3_sbcie a_cvv a_wcel f0_sbcie f2_sbcie f3_sbcie a_wsbc f1_sbcie a_wb a_ax-mp $.
$}

$(Conversion of implicit substitution to explicit class substitution,
         deduction form.  (Contributed by NM, 29-Dec-2014.) $)

${
	$v ph ps ch x A V  $.
	$d x A  $.
	f0_sbciedf $f wff ph $.
	f1_sbciedf $f wff ps $.
	f2_sbciedf $f wff ch $.
	f3_sbciedf $f set x $.
	f4_sbciedf $f class A $.
	f5_sbciedf $f class V $.
	e0_sbciedf $e |- ( ph -> A e. V ) $.
	e1_sbciedf $e |- ( ( ph /\ x = A ) -> ( ps <-> ch ) ) $.
	e2_sbciedf $e |- F/ x ph $.
	e3_sbciedf $e |- ( ph -> F/ x ch ) $.
	p_sbciedf $p |- ( ph -> ( [. A / x ]. ps <-> ch ) ) $= e0_sbciedf e3_sbciedf e2_sbciedf e1_sbciedf f0_sbciedf f3_sbciedf a_sup_set_class f4_sbciedf a_wceq f1_sbciedf f2_sbciedf a_wb p_ex f0_sbciedf f3_sbciedf a_sup_set_class f4_sbciedf a_wceq f1_sbciedf f2_sbciedf a_wb a_wi f3_sbciedf p_alrimi f1_sbciedf f2_sbciedf f3_sbciedf f4_sbciedf f5_sbciedf p_sbciegft f0_sbciedf f4_sbciedf f5_sbciedf a_wcel f2_sbciedf f3_sbciedf a_wnf f3_sbciedf a_sup_set_class f4_sbciedf a_wceq f1_sbciedf f2_sbciedf a_wb a_wi f3_sbciedf a_wal f1_sbciedf f3_sbciedf f4_sbciedf a_wsbc f2_sbciedf a_wb p_syl3anc $.
$}

$(Conversion of implicit substitution to explicit class substitution,
       deduction form.  (Contributed by NM, 13-Dec-2014.) $)

${
	$v ph ps ch x A V  $.
	$d x A  $.
	$d x ph  $.
	$d x ch  $.
	f0_sbcied $f wff ph $.
	f1_sbcied $f wff ps $.
	f2_sbcied $f wff ch $.
	f3_sbcied $f set x $.
	f4_sbcied $f class A $.
	f5_sbcied $f class V $.
	e0_sbcied $e |- ( ph -> A e. V ) $.
	e1_sbcied $e |- ( ( ph /\ x = A ) -> ( ps <-> ch ) ) $.
	p_sbcied $p |- ( ph -> ( [. A / x ]. ps <-> ch ) ) $= e0_sbcied e1_sbcied f0_sbcied f3_sbcied p_nfv f0_sbcied f2_sbcied f3_sbcied p_nfvd f0_sbcied f1_sbcied f2_sbcied f3_sbcied f4_sbcied f5_sbcied p_sbciedf $.
$}

$(Conversion of implicit substitution to explicit class substitution,
       deduction form.  (Contributed by NM, 13-Dec-2014.) $)

${
	$v ph ps ch x A B V  $.
	$d x A  $.
	$d x ph  $.
	$d x ch  $.
	f0_sbcied2 $f wff ph $.
	f1_sbcied2 $f wff ps $.
	f2_sbcied2 $f wff ch $.
	f3_sbcied2 $f set x $.
	f4_sbcied2 $f class A $.
	f5_sbcied2 $f class B $.
	f6_sbcied2 $f class V $.
	e0_sbcied2 $e |- ( ph -> A e. V ) $.
	e1_sbcied2 $e |- ( ph -> A = B ) $.
	e2_sbcied2 $e |- ( ( ph /\ x = B ) -> ( ps <-> ch ) ) $.
	p_sbcied2 $p |- ( ph -> ( [. A / x ]. ps <-> ch ) ) $= e0_sbcied2 f3_sbcied2 a_sup_set_class f4_sbcied2 a_wceq p_id e1_sbcied2 f3_sbcied2 a_sup_set_class f4_sbcied2 a_wceq f0_sbcied2 f3_sbcied2 a_sup_set_class f4_sbcied2 f5_sbcied2 p_sylan9eqr e2_sbcied2 f0_sbcied2 f3_sbcied2 a_sup_set_class f4_sbcied2 a_wceq f3_sbcied2 a_sup_set_class f5_sbcied2 a_wceq f1_sbcied2 f2_sbcied2 a_wb p_syldan f0_sbcied2 f1_sbcied2 f2_sbcied2 f3_sbcied2 f4_sbcied2 f6_sbcied2 p_sbcied $.
$}

$(Membership in a restricted class abstraction, expressed with explicit
       class substitution.  (The variation ~ elrabf has implicit
       substitution).  The hypothesis specifies that ` x ` must not be a free
       variable in ` B ` .  (Contributed by NM, 30-Sep-2003.)  (Proof shortened
       by Mario Carneiro, 13-Oct-2016.) $)

${
	$v ph x A B  $.
	$d y A  $.
	$d y B  $.
	$d y ph  $.
	$d x y  $.
	f0_elrabsf $f wff ph $.
	f1_elrabsf $f set x $.
	f2_elrabsf $f class A $.
	f3_elrabsf $f class B $.
	i0_elrabsf $f set y $.
	e0_elrabsf $e |- F/_ x B $.
	p_elrabsf $p |- ( A e. { x e. B | ph } <-> ( A e. B /\ [. A / x ]. ph ) ) $= f0_elrabsf f1_elrabsf i0_elrabsf a_sup_set_class f2_elrabsf p_dfsbcq e0_elrabsf i0_elrabsf f3_elrabsf p_nfcv f0_elrabsf i0_elrabsf p_nfv f0_elrabsf f1_elrabsf i0_elrabsf a_sup_set_class p_nfsbc1v f0_elrabsf f1_elrabsf i0_elrabsf a_sup_set_class p_sbceq1a f0_elrabsf f0_elrabsf f1_elrabsf i0_elrabsf a_sup_set_class a_wsbc f1_elrabsf i0_elrabsf f3_elrabsf p_cbvrab f0_elrabsf f1_elrabsf i0_elrabsf a_sup_set_class a_wsbc f0_elrabsf f1_elrabsf f2_elrabsf a_wsbc i0_elrabsf f2_elrabsf f3_elrabsf f0_elrabsf f1_elrabsf f3_elrabsf a_crab p_elrab2 $.
$}

$(Substitution applied to an atomic wff.  Set theory version of ~ eqsb3 .
       (Contributed by Andrew Salmon, 29-Jun-2011.) $)

${
	$v x A B V  $.
	$d x y B  $.
	$d y A  $.
	f0_eqsbc3 $f set x $.
	f1_eqsbc3 $f class A $.
	f2_eqsbc3 $f class B $.
	f3_eqsbc3 $f class V $.
	i0_eqsbc3 $f set y $.
	p_eqsbc3 $p |- ( A e. V -> ( [. A / x ]. x = B <-> A = B ) ) $= f0_eqsbc3 a_sup_set_class f2_eqsbc3 a_wceq f0_eqsbc3 i0_eqsbc3 a_sup_set_class f1_eqsbc3 p_dfsbcq i0_eqsbc3 a_sup_set_class f1_eqsbc3 f2_eqsbc3 p_eqeq1 f0_eqsbc3 a_sup_set_class f2_eqsbc3 a_wceq f0_eqsbc3 i0_eqsbc3 p_sbsbc i0_eqsbc3 f0_eqsbc3 f2_eqsbc3 p_eqsb3 f0_eqsbc3 a_sup_set_class f2_eqsbc3 a_wceq f0_eqsbc3 i0_eqsbc3 a_sup_set_class a_wsbc f0_eqsbc3 a_sup_set_class f2_eqsbc3 a_wceq f0_eqsbc3 i0_eqsbc3 a_wsb i0_eqsbc3 a_sup_set_class f2_eqsbc3 a_wceq p_bitr3i f0_eqsbc3 a_sup_set_class f2_eqsbc3 a_wceq f0_eqsbc3 i0_eqsbc3 a_sup_set_class a_wsbc i0_eqsbc3 a_sup_set_class f2_eqsbc3 a_wceq f0_eqsbc3 a_sup_set_class f2_eqsbc3 a_wceq f0_eqsbc3 f1_eqsbc3 a_wsbc f1_eqsbc3 f2_eqsbc3 a_wceq i0_eqsbc3 f1_eqsbc3 f3_eqsbc3 p_vtoclbg $.
$}

$(Move negation in and out of class substitution.  (Contributed by NM,
       16-Jan-2004.) $)

${
	$v ph x A V  $.
	$d x y  $.
	$d y A  $.
	$d y ph  $.
	$d y  $.
	f0_sbcng $f wff ph $.
	f1_sbcng $f set x $.
	f2_sbcng $f class A $.
	f3_sbcng $f class V $.
	i0_sbcng $f set y $.
	p_sbcng $p |- ( A e. V -> ( [. A / x ]. -. ph <-> -. [. A / x ]. ph ) ) $= f0_sbcng a_wn f1_sbcng i0_sbcng f2_sbcng p_dfsbcq2 f0_sbcng f1_sbcng i0_sbcng f2_sbcng p_dfsbcq2 i0_sbcng a_sup_set_class f2_sbcng a_wceq f0_sbcng f1_sbcng i0_sbcng a_wsb f0_sbcng f1_sbcng f2_sbcng a_wsbc p_notbid f0_sbcng f1_sbcng i0_sbcng p_sbn f0_sbcng a_wn f1_sbcng i0_sbcng a_wsb f0_sbcng f1_sbcng i0_sbcng a_wsb a_wn f0_sbcng a_wn f1_sbcng f2_sbcng a_wsbc f0_sbcng f1_sbcng f2_sbcng a_wsbc a_wn i0_sbcng f2_sbcng f3_sbcng p_vtoclbg $.
$}

$(Distribution of class substitution over implication.  (Contributed by
       NM, 16-Jan-2004.) $)

${
	$v ph ps x A V  $.
	$d x y  $.
	$d y A  $.
	$d y ph  $.
	$d y ps  $.
	f0_sbcimg $f wff ph $.
	f1_sbcimg $f wff ps $.
	f2_sbcimg $f set x $.
	f3_sbcimg $f class A $.
	f4_sbcimg $f class V $.
	i0_sbcimg $f set y $.
	p_sbcimg $p |- ( A e. V -> ( [. A / x ]. ( ph -> ps ) <-> ( [. A / x ]. ph -> [. A / x ]. ps ) ) ) $= f0_sbcimg f1_sbcimg a_wi f2_sbcimg i0_sbcimg f3_sbcimg p_dfsbcq2 f0_sbcimg f2_sbcimg i0_sbcimg f3_sbcimg p_dfsbcq2 f1_sbcimg f2_sbcimg i0_sbcimg f3_sbcimg p_dfsbcq2 i0_sbcimg a_sup_set_class f3_sbcimg a_wceq f0_sbcimg f2_sbcimg i0_sbcimg a_wsb f0_sbcimg f2_sbcimg f3_sbcimg a_wsbc f1_sbcimg f2_sbcimg i0_sbcimg a_wsb f1_sbcimg f2_sbcimg f3_sbcimg a_wsbc p_imbi12d f0_sbcimg f1_sbcimg f2_sbcimg i0_sbcimg p_sbim f0_sbcimg f1_sbcimg a_wi f2_sbcimg i0_sbcimg a_wsb f0_sbcimg f2_sbcimg i0_sbcimg a_wsb f1_sbcimg f2_sbcimg i0_sbcimg a_wsb a_wi f0_sbcimg f1_sbcimg a_wi f2_sbcimg f3_sbcimg a_wsbc f0_sbcimg f2_sbcimg f3_sbcimg a_wsbc f1_sbcimg f2_sbcimg f3_sbcimg a_wsbc a_wi i0_sbcimg f3_sbcimg f4_sbcimg p_vtoclbg $.
$}

$(Distribution of class substitution over conjunction.  (Contributed by
       NM, 31-Dec-2016.) $)

${
	$v ph ps x A  $.
	$d x y  $.
	$d y A  $.
	$d y ph  $.
	$d y ps  $.
	f0_sbcan $f wff ph $.
	f1_sbcan $f wff ps $.
	f2_sbcan $f set x $.
	f3_sbcan $f class A $.
	i0_sbcan $f set y $.
	p_sbcan $p |- ( [. A / x ]. ( ph /\ ps ) <-> ( [. A / x ]. ph /\ [. A / x ]. ps ) ) $= f0_sbcan f1_sbcan a_wa f2_sbcan f3_sbcan p_sbcex f1_sbcan f2_sbcan f3_sbcan p_sbcex f1_sbcan f2_sbcan f3_sbcan a_wsbc f3_sbcan a_cvv a_wcel f0_sbcan f2_sbcan f3_sbcan a_wsbc p_adantl f0_sbcan f1_sbcan a_wa f2_sbcan i0_sbcan f3_sbcan p_dfsbcq2 f0_sbcan f2_sbcan i0_sbcan f3_sbcan p_dfsbcq2 f1_sbcan f2_sbcan i0_sbcan f3_sbcan p_dfsbcq2 i0_sbcan a_sup_set_class f3_sbcan a_wceq f0_sbcan f2_sbcan i0_sbcan a_wsb f0_sbcan f2_sbcan f3_sbcan a_wsbc f1_sbcan f2_sbcan i0_sbcan a_wsb f1_sbcan f2_sbcan f3_sbcan a_wsbc p_anbi12d f0_sbcan f1_sbcan f2_sbcan i0_sbcan p_sban f0_sbcan f1_sbcan a_wa f2_sbcan i0_sbcan a_wsb f0_sbcan f2_sbcan i0_sbcan a_wsb f1_sbcan f2_sbcan i0_sbcan a_wsb a_wa f0_sbcan f1_sbcan a_wa f2_sbcan f3_sbcan a_wsbc f0_sbcan f2_sbcan f3_sbcan a_wsbc f1_sbcan f2_sbcan f3_sbcan a_wsbc a_wa i0_sbcan f3_sbcan a_cvv p_vtoclbg f0_sbcan f1_sbcan a_wa f2_sbcan f3_sbcan a_wsbc f3_sbcan a_cvv a_wcel f0_sbcan f2_sbcan f3_sbcan a_wsbc f1_sbcan f2_sbcan f3_sbcan a_wsbc a_wa p_pm5.21nii $.
$}

$(Distribution of class substitution over conjunction.  (Contributed by
       NM, 21-May-2004.) $)

${
	$v ph ps x A V  $.
	$d x y  $.
	$d y A  $.
	$d y ph  $.
	$d y ps  $.
	f0_sbcang $f wff ph $.
	f1_sbcang $f wff ps $.
	f2_sbcang $f set x $.
	f3_sbcang $f class A $.
	f4_sbcang $f class V $.
	i0_sbcang $f set y $.
	p_sbcang $p |- ( A e. V -> ( [. A / x ]. ( ph /\ ps ) <-> ( [. A / x ]. ph /\ [. A / x ]. ps ) ) ) $= f0_sbcang f1_sbcang a_wa f2_sbcang i0_sbcang f3_sbcang p_dfsbcq2 f0_sbcang f2_sbcang i0_sbcang f3_sbcang p_dfsbcq2 f1_sbcang f2_sbcang i0_sbcang f3_sbcang p_dfsbcq2 i0_sbcang a_sup_set_class f3_sbcang a_wceq f0_sbcang f2_sbcang i0_sbcang a_wsb f0_sbcang f2_sbcang f3_sbcang a_wsbc f1_sbcang f2_sbcang i0_sbcang a_wsb f1_sbcang f2_sbcang f3_sbcang a_wsbc p_anbi12d f0_sbcang f1_sbcang f2_sbcang i0_sbcang p_sban f0_sbcang f1_sbcang a_wa f2_sbcang i0_sbcang a_wsb f0_sbcang f2_sbcang i0_sbcang a_wsb f1_sbcang f2_sbcang i0_sbcang a_wsb a_wa f0_sbcang f1_sbcang a_wa f2_sbcang f3_sbcang a_wsbc f0_sbcang f2_sbcang f3_sbcang a_wsbc f1_sbcang f2_sbcang f3_sbcang a_wsbc a_wa i0_sbcang f3_sbcang f4_sbcang p_vtoclbg $.
$}

$(Distribution of class substitution over disjunction.  (Contributed by
       NM, 31-Dec-2016.) $)

${
	$v ph ps x A  $.
	$d x y  $.
	$d y A  $.
	$d y ph  $.
	$d y ps  $.
	f0_sbcor $f wff ph $.
	f1_sbcor $f wff ps $.
	f2_sbcor $f set x $.
	f3_sbcor $f class A $.
	i0_sbcor $f set y $.
	p_sbcor $p |- ( [. A / x ]. ( ph \/ ps ) <-> ( [. A / x ]. ph \/ [. A / x ]. ps ) ) $= f0_sbcor f1_sbcor a_wo f2_sbcor f3_sbcor p_sbcex f0_sbcor f2_sbcor f3_sbcor p_sbcex f1_sbcor f2_sbcor f3_sbcor p_sbcex f0_sbcor f2_sbcor f3_sbcor a_wsbc f3_sbcor a_cvv a_wcel f1_sbcor f2_sbcor f3_sbcor a_wsbc p_jaoi f0_sbcor f1_sbcor a_wo f2_sbcor i0_sbcor f3_sbcor p_dfsbcq2 f0_sbcor f2_sbcor i0_sbcor f3_sbcor p_dfsbcq2 f1_sbcor f2_sbcor i0_sbcor f3_sbcor p_dfsbcq2 i0_sbcor a_sup_set_class f3_sbcor a_wceq f0_sbcor f2_sbcor i0_sbcor a_wsb f0_sbcor f2_sbcor f3_sbcor a_wsbc f1_sbcor f2_sbcor i0_sbcor a_wsb f1_sbcor f2_sbcor f3_sbcor a_wsbc p_orbi12d f0_sbcor f1_sbcor f2_sbcor i0_sbcor p_sbor f0_sbcor f1_sbcor a_wo f2_sbcor i0_sbcor a_wsb f0_sbcor f2_sbcor i0_sbcor a_wsb f1_sbcor f2_sbcor i0_sbcor a_wsb a_wo f0_sbcor f1_sbcor a_wo f2_sbcor f3_sbcor a_wsbc f0_sbcor f2_sbcor f3_sbcor a_wsbc f1_sbcor f2_sbcor f3_sbcor a_wsbc a_wo i0_sbcor f3_sbcor a_cvv p_vtoclbg f0_sbcor f1_sbcor a_wo f2_sbcor f3_sbcor a_wsbc f3_sbcor a_cvv a_wcel f0_sbcor f2_sbcor f3_sbcor a_wsbc f1_sbcor f2_sbcor f3_sbcor a_wsbc a_wo p_pm5.21nii $.
$}

$(Distribution of class substitution over disjunction.  (Contributed by
       NM, 21-May-2004.) $)

${
	$v ph ps x A V  $.
	$d x y  $.
	$d y A  $.
	$d y ph  $.
	$d y ps  $.
	f0_sbcorg $f wff ph $.
	f1_sbcorg $f wff ps $.
	f2_sbcorg $f set x $.
	f3_sbcorg $f class A $.
	f4_sbcorg $f class V $.
	i0_sbcorg $f set y $.
	p_sbcorg $p |- ( A e. V -> ( [. A / x ]. ( ph \/ ps ) <-> ( [. A / x ]. ph \/ [. A / x ]. ps ) ) ) $= f0_sbcorg f1_sbcorg a_wo f2_sbcorg i0_sbcorg f3_sbcorg p_dfsbcq2 f0_sbcorg f2_sbcorg i0_sbcorg f3_sbcorg p_dfsbcq2 f1_sbcorg f2_sbcorg i0_sbcorg f3_sbcorg p_dfsbcq2 i0_sbcorg a_sup_set_class f3_sbcorg a_wceq f0_sbcorg f2_sbcorg i0_sbcorg a_wsb f0_sbcorg f2_sbcorg f3_sbcorg a_wsbc f1_sbcorg f2_sbcorg i0_sbcorg a_wsb f1_sbcorg f2_sbcorg f3_sbcorg a_wsbc p_orbi12d f0_sbcorg f1_sbcorg f2_sbcorg i0_sbcorg p_sbor f0_sbcorg f1_sbcorg a_wo f2_sbcorg i0_sbcorg a_wsb f0_sbcorg f2_sbcorg i0_sbcorg a_wsb f1_sbcorg f2_sbcorg i0_sbcorg a_wsb a_wo f0_sbcorg f1_sbcorg a_wo f2_sbcorg f3_sbcorg a_wsbc f0_sbcorg f2_sbcorg f3_sbcorg a_wsbc f1_sbcorg f2_sbcorg f3_sbcorg a_wsbc a_wo i0_sbcorg f3_sbcorg f4_sbcorg p_vtoclbg $.
$}

$(Distribution of class substitution over biconditional.  (Contributed by
       Raph Levien, 10-Apr-2004.) $)

${
	$v ph ps x A V  $.
	$d x y  $.
	$d y A  $.
	$d y ph  $.
	$d y ps  $.
	f0_sbcbig $f wff ph $.
	f1_sbcbig $f wff ps $.
	f2_sbcbig $f set x $.
	f3_sbcbig $f class A $.
	f4_sbcbig $f class V $.
	i0_sbcbig $f set y $.
	p_sbcbig $p |- ( A e. V -> ( [. A / x ]. ( ph <-> ps ) <-> ( [. A / x ]. ph <-> [. A / x ]. ps ) ) ) $= f0_sbcbig f1_sbcbig a_wb f2_sbcbig i0_sbcbig f3_sbcbig p_dfsbcq2 f0_sbcbig f2_sbcbig i0_sbcbig f3_sbcbig p_dfsbcq2 f1_sbcbig f2_sbcbig i0_sbcbig f3_sbcbig p_dfsbcq2 i0_sbcbig a_sup_set_class f3_sbcbig a_wceq f0_sbcbig f2_sbcbig i0_sbcbig a_wsb f0_sbcbig f2_sbcbig f3_sbcbig a_wsbc f1_sbcbig f2_sbcbig i0_sbcbig a_wsb f1_sbcbig f2_sbcbig f3_sbcbig a_wsbc p_bibi12d f0_sbcbig f1_sbcbig f2_sbcbig i0_sbcbig p_sbbi f0_sbcbig f1_sbcbig a_wb f2_sbcbig i0_sbcbig a_wsb f0_sbcbig f2_sbcbig i0_sbcbig a_wsb f1_sbcbig f2_sbcbig i0_sbcbig a_wsb a_wb f0_sbcbig f1_sbcbig a_wb f2_sbcbig f3_sbcbig a_wsbc f0_sbcbig f2_sbcbig f3_sbcbig a_wsbc f1_sbcbig f2_sbcbig f3_sbcbig a_wsbc a_wb i0_sbcbig f3_sbcbig f4_sbcbig p_vtoclbg $.
$}

$(Move universal quantifier in and out of class substitution.
       (Contributed by NM, 31-Dec-2016.) $)

${
	$v ph x y A  $.
	$d x z A  $.
	$d x y z  $.
	$d z ph  $.
	f0_sbcal $f wff ph $.
	f1_sbcal $f set x $.
	f2_sbcal $f set y $.
	f3_sbcal $f class A $.
	i0_sbcal $f set z $.
	p_sbcal $p |- ( [. A / y ]. A. x ph <-> A. x [. A / y ]. ph ) $= f0_sbcal f1_sbcal a_wal f2_sbcal f3_sbcal p_sbcex f0_sbcal f2_sbcal f3_sbcal p_sbcex f0_sbcal f2_sbcal f3_sbcal a_wsbc f3_sbcal a_cvv a_wcel f1_sbcal p_sps f0_sbcal f1_sbcal a_wal f2_sbcal i0_sbcal f3_sbcal p_dfsbcq2 f0_sbcal f2_sbcal i0_sbcal f3_sbcal p_dfsbcq2 i0_sbcal a_sup_set_class f3_sbcal a_wceq f0_sbcal f2_sbcal i0_sbcal a_wsb f0_sbcal f2_sbcal f3_sbcal a_wsbc f1_sbcal p_albidv f0_sbcal f1_sbcal f2_sbcal i0_sbcal p_sbal f0_sbcal f1_sbcal a_wal f2_sbcal i0_sbcal a_wsb f0_sbcal f2_sbcal i0_sbcal a_wsb f1_sbcal a_wal f0_sbcal f1_sbcal a_wal f2_sbcal f3_sbcal a_wsbc f0_sbcal f2_sbcal f3_sbcal a_wsbc f1_sbcal a_wal i0_sbcal f3_sbcal a_cvv p_vtoclbg f0_sbcal f1_sbcal a_wal f2_sbcal f3_sbcal a_wsbc f3_sbcal a_cvv a_wcel f0_sbcal f2_sbcal f3_sbcal a_wsbc f1_sbcal a_wal p_pm5.21nii $.
$}

$(Move universal quantifier in and out of class substitution.
       (Contributed by NM, 16-Jan-2004.) $)

${
	$v ph x y A V  $.
	$d x z A  $.
	$d x y z  $.
	$d z ph  $.
	f0_sbcalg $f wff ph $.
	f1_sbcalg $f set x $.
	f2_sbcalg $f set y $.
	f3_sbcalg $f class A $.
	f4_sbcalg $f class V $.
	i0_sbcalg $f set z $.
	p_sbcalg $p |- ( A e. V -> ( [. A / y ]. A. x ph <-> A. x [. A / y ]. ph ) ) $= f0_sbcalg f1_sbcalg a_wal f2_sbcalg i0_sbcalg f3_sbcalg p_dfsbcq2 f0_sbcalg f2_sbcalg i0_sbcalg f3_sbcalg p_dfsbcq2 i0_sbcalg a_sup_set_class f3_sbcalg a_wceq f0_sbcalg f2_sbcalg i0_sbcalg a_wsb f0_sbcalg f2_sbcalg f3_sbcalg a_wsbc f1_sbcalg p_albidv f0_sbcalg f1_sbcalg f2_sbcalg i0_sbcalg p_sbal f0_sbcalg f1_sbcalg a_wal f2_sbcalg i0_sbcalg a_wsb f0_sbcalg f2_sbcalg i0_sbcalg a_wsb f1_sbcalg a_wal f0_sbcalg f1_sbcalg a_wal f2_sbcalg f3_sbcalg a_wsbc f0_sbcalg f2_sbcalg f3_sbcalg a_wsbc f1_sbcalg a_wal i0_sbcalg f3_sbcalg f4_sbcalg p_vtoclbg $.
$}

$(Move existential quantifier in and out of class substitution.
       (Contributed by NM, 21-May-2004.) $)

${
	$v ph x y A  $.
	$d x z A  $.
	$d x y z  $.
	$d z ph  $.
	f0_sbcex2 $f wff ph $.
	f1_sbcex2 $f set x $.
	f2_sbcex2 $f set y $.
	f3_sbcex2 $f class A $.
	i0_sbcex2 $f set z $.
	p_sbcex2 $p |- ( [. A / y ]. E. x ph <-> E. x [. A / y ]. ph ) $= f0_sbcex2 f1_sbcex2 a_wex f2_sbcex2 f3_sbcex2 p_sbcex f0_sbcex2 f2_sbcex2 f3_sbcex2 p_sbcex f0_sbcex2 f2_sbcex2 f3_sbcex2 a_wsbc f3_sbcex2 a_cvv a_wcel f1_sbcex2 p_exlimiv f0_sbcex2 f1_sbcex2 a_wex f2_sbcex2 i0_sbcex2 f3_sbcex2 p_dfsbcq2 f0_sbcex2 f2_sbcex2 i0_sbcex2 f3_sbcex2 p_dfsbcq2 i0_sbcex2 a_sup_set_class f3_sbcex2 a_wceq f0_sbcex2 f2_sbcex2 i0_sbcex2 a_wsb f0_sbcex2 f2_sbcex2 f3_sbcex2 a_wsbc f1_sbcex2 p_exbidv f0_sbcex2 f1_sbcex2 f2_sbcex2 i0_sbcex2 p_sbex f0_sbcex2 f1_sbcex2 a_wex f2_sbcex2 i0_sbcex2 a_wsb f0_sbcex2 f2_sbcex2 i0_sbcex2 a_wsb f1_sbcex2 a_wex f0_sbcex2 f1_sbcex2 a_wex f2_sbcex2 f3_sbcex2 a_wsbc f0_sbcex2 f2_sbcex2 f3_sbcex2 a_wsbc f1_sbcex2 a_wex i0_sbcex2 f3_sbcex2 a_cvv p_vtoclbg f0_sbcex2 f1_sbcex2 a_wex f2_sbcex2 f3_sbcex2 a_wsbc f3_sbcex2 a_cvv a_wcel f0_sbcex2 f2_sbcex2 f3_sbcex2 a_wsbc f1_sbcex2 a_wex p_pm5.21nii $.
$}

$(Move existential quantifier in and out of class substitution.
       (Contributed by NM, 21-May-2004.) $)

${
	$v ph x y A V  $.
	$d x z A  $.
	$d x y z  $.
	$d z ph  $.
	f0_sbcexg $f wff ph $.
	f1_sbcexg $f set x $.
	f2_sbcexg $f set y $.
	f3_sbcexg $f class A $.
	f4_sbcexg $f class V $.
	i0_sbcexg $f set z $.
	p_sbcexg $p |- ( A e. V -> ( [. A / y ]. E. x ph <-> E. x [. A / y ]. ph ) ) $= f0_sbcexg f1_sbcexg a_wex f2_sbcexg i0_sbcexg f3_sbcexg p_dfsbcq2 f0_sbcexg f2_sbcexg i0_sbcexg f3_sbcexg p_dfsbcq2 i0_sbcexg a_sup_set_class f3_sbcexg a_wceq f0_sbcexg f2_sbcexg i0_sbcexg a_wsb f0_sbcexg f2_sbcexg f3_sbcexg a_wsbc f1_sbcexg p_exbidv f0_sbcexg f1_sbcexg f2_sbcexg i0_sbcexg p_sbex f0_sbcexg f1_sbcexg a_wex f2_sbcexg i0_sbcexg a_wsb f0_sbcexg f2_sbcexg i0_sbcexg a_wsb f1_sbcexg a_wex f0_sbcexg f1_sbcexg a_wex f2_sbcexg f3_sbcexg a_wsbc f0_sbcexg f2_sbcexg f3_sbcexg a_wsbc f1_sbcexg a_wex i0_sbcexg f3_sbcexg f4_sbcexg p_vtoclbg $.
$}

$(Set theory version of ~ sbeqal1 .  (Contributed by Andrew Salmon,
       28-Jun-2011.) $)

${
	$v x A B V  $.
	$d x B  $.
	$d x A  $.
	f0_sbceqal $f set x $.
	f1_sbceqal $f class A $.
	f2_sbceqal $f class B $.
	f3_sbceqal $f class V $.
	p_sbceqal $p |- ( A e. V -> ( A. x ( x = A -> x = B ) -> A = B ) ) $= f0_sbceqal a_sup_set_class f1_sbceqal a_wceq f0_sbceqal a_sup_set_class f2_sbceqal a_wceq a_wi f0_sbceqal f1_sbceqal f3_sbceqal p_spsbc f0_sbceqal a_sup_set_class f1_sbceqal a_wceq f0_sbceqal a_sup_set_class f2_sbceqal a_wceq f0_sbceqal f1_sbceqal f3_sbceqal p_sbcimg f1_sbceqal p_eqid f0_sbceqal f1_sbceqal f1_sbceqal f3_sbceqal p_eqsbc3 f1_sbceqal f3_sbceqal a_wcel f0_sbceqal a_sup_set_class f1_sbceqal a_wceq f0_sbceqal f1_sbceqal a_wsbc f1_sbceqal f1_sbceqal a_wceq p_mpbiri f0_sbceqal a_sup_set_class f1_sbceqal a_wceq f0_sbceqal f1_sbceqal a_wsbc f0_sbceqal a_sup_set_class f2_sbceqal a_wceq f0_sbceqal f1_sbceqal a_wsbc p_pm5.5 f1_sbceqal f3_sbceqal a_wcel f0_sbceqal a_sup_set_class f1_sbceqal a_wceq f0_sbceqal f1_sbceqal a_wsbc f0_sbceqal a_sup_set_class f1_sbceqal a_wceq f0_sbceqal f1_sbceqal a_wsbc f0_sbceqal a_sup_set_class f2_sbceqal a_wceq f0_sbceqal f1_sbceqal a_wsbc a_wi f0_sbceqal a_sup_set_class f2_sbceqal a_wceq f0_sbceqal f1_sbceqal a_wsbc a_wb p_syl f0_sbceqal f1_sbceqal f2_sbceqal f3_sbceqal p_eqsbc3 f1_sbceqal f3_sbceqal a_wcel f0_sbceqal a_sup_set_class f1_sbceqal a_wceq f0_sbceqal a_sup_set_class f2_sbceqal a_wceq a_wi f0_sbceqal f1_sbceqal a_wsbc f0_sbceqal a_sup_set_class f1_sbceqal a_wceq f0_sbceqal f1_sbceqal a_wsbc f0_sbceqal a_sup_set_class f2_sbceqal a_wceq f0_sbceqal f1_sbceqal a_wsbc a_wi f0_sbceqal a_sup_set_class f2_sbceqal a_wceq f0_sbceqal f1_sbceqal a_wsbc f1_sbceqal f2_sbceqal a_wceq p_3bitrd f1_sbceqal f3_sbceqal a_wcel f0_sbceqal a_sup_set_class f1_sbceqal a_wceq f0_sbceqal a_sup_set_class f2_sbceqal a_wceq a_wi f0_sbceqal a_wal f0_sbceqal a_sup_set_class f1_sbceqal a_wceq f0_sbceqal a_sup_set_class f2_sbceqal a_wceq a_wi f0_sbceqal f1_sbceqal a_wsbc f1_sbceqal f2_sbceqal a_wceq p_sylibd $.
$}

$(Theorem *14.121 in [WhiteheadRussell] p. 185.  (Contributed by Andrew
       Salmon, 28-Jun-2011.)  (Proof shortened by Wolf Lammen, 9-May-2013.) $)

${
	$v ph x A B V  $.
	$d x A  $.
	$d x B  $.
	f0_sbeqalb $f wff ph $.
	f1_sbeqalb $f set x $.
	f2_sbeqalb $f class A $.
	f3_sbeqalb $f class B $.
	f4_sbeqalb $f class V $.
	p_sbeqalb $p |- ( A e. V -> ( ( A. x ( ph <-> x = A ) /\ A. x ( ph <-> x = B ) ) -> A = B ) ) $= f0_sbeqalb f1_sbeqalb a_sup_set_class f2_sbeqalb a_wceq f1_sbeqalb a_sup_set_class f3_sbeqalb a_wceq p_bibi1 f0_sbeqalb f1_sbeqalb a_sup_set_class f2_sbeqalb a_wceq a_wb f0_sbeqalb f1_sbeqalb a_sup_set_class f3_sbeqalb a_wceq a_wb f1_sbeqalb a_sup_set_class f2_sbeqalb a_wceq f1_sbeqalb a_sup_set_class f3_sbeqalb a_wceq a_wb p_biimpa f0_sbeqalb f1_sbeqalb a_sup_set_class f2_sbeqalb a_wceq a_wb f0_sbeqalb f1_sbeqalb a_sup_set_class f3_sbeqalb a_wceq a_wb a_wa f1_sbeqalb a_sup_set_class f2_sbeqalb a_wceq f1_sbeqalb a_sup_set_class f3_sbeqalb a_wceq p_biimpd f0_sbeqalb f1_sbeqalb a_sup_set_class f2_sbeqalb a_wceq a_wb f0_sbeqalb f1_sbeqalb a_sup_set_class f3_sbeqalb a_wceq a_wb f1_sbeqalb a_sup_set_class f2_sbeqalb a_wceq f1_sbeqalb a_sup_set_class f3_sbeqalb a_wceq a_wi f1_sbeqalb p_alanimi f1_sbeqalb f2_sbeqalb f3_sbeqalb f4_sbeqalb p_sbceqal f0_sbeqalb f1_sbeqalb a_sup_set_class f2_sbeqalb a_wceq a_wb f1_sbeqalb a_wal f0_sbeqalb f1_sbeqalb a_sup_set_class f3_sbeqalb a_wceq a_wb f1_sbeqalb a_wal a_wa f1_sbeqalb a_sup_set_class f2_sbeqalb a_wceq f1_sbeqalb a_sup_set_class f3_sbeqalb a_wceq a_wi f1_sbeqalb a_wal f2_sbeqalb f4_sbeqalb a_wcel f2_sbeqalb f3_sbeqalb a_wceq p_syl5 $.
$}

$(Formula-building deduction rule for class substitution.  (Contributed by
       NM, 29-Dec-2014.) $)

${
	$v ph ps ch x A  $.
	f0_sbcbid $f wff ph $.
	f1_sbcbid $f wff ps $.
	f2_sbcbid $f wff ch $.
	f3_sbcbid $f set x $.
	f4_sbcbid $f class A $.
	e0_sbcbid $e |- F/ x ph $.
	e1_sbcbid $e |- ( ph -> ( ps <-> ch ) ) $.
	p_sbcbid $p |- ( ph -> ( [. A / x ]. ps <-> [. A / x ]. ch ) ) $= e0_sbcbid e1_sbcbid f0_sbcbid f1_sbcbid f2_sbcbid f3_sbcbid p_abbid f0_sbcbid f1_sbcbid f3_sbcbid a_cab f2_sbcbid f3_sbcbid a_cab f4_sbcbid p_eleq2d f1_sbcbid f3_sbcbid f4_sbcbid a_df-sbc f2_sbcbid f3_sbcbid f4_sbcbid a_df-sbc f0_sbcbid f4_sbcbid f1_sbcbid f3_sbcbid a_cab a_wcel f4_sbcbid f2_sbcbid f3_sbcbid a_cab a_wcel f1_sbcbid f3_sbcbid f4_sbcbid a_wsbc f2_sbcbid f3_sbcbid f4_sbcbid a_wsbc p_3bitr4g $.
$}

$(Formula-building deduction rule for class substitution.  (Contributed by
       NM, 29-Dec-2014.) $)

${
	$v ph ps ch x A  $.
	$d x ph  $.
	f0_sbcbidv $f wff ph $.
	f1_sbcbidv $f wff ps $.
	f2_sbcbidv $f wff ch $.
	f3_sbcbidv $f set x $.
	f4_sbcbidv $f class A $.
	e0_sbcbidv $e |- ( ph -> ( ps <-> ch ) ) $.
	p_sbcbidv $p |- ( ph -> ( [. A / x ]. ps <-> [. A / x ]. ch ) ) $= f0_sbcbidv f3_sbcbidv p_nfv e0_sbcbidv f0_sbcbidv f1_sbcbidv f2_sbcbidv f3_sbcbidv f4_sbcbidv p_sbcbid $.
$}

$(Formula-building inference rule for class substitution.  (Contributed by
       NM, 11-Nov-2005.) $)

${
	$v ph ps x A  $.
	f0_sbcbii $f wff ph $.
	f1_sbcbii $f wff ps $.
	f2_sbcbii $f set x $.
	f3_sbcbii $f class A $.
	e0_sbcbii $e |- ( ph <-> ps ) $.
	p_sbcbii $p |- ( [. A / x ]. ph <-> [. A / x ]. ps ) $= e0_sbcbii f0_sbcbii f1_sbcbii a_wb a_wtru p_a1i a_wtru f0_sbcbii f1_sbcbii f2_sbcbii f3_sbcbii p_sbcbidv f0_sbcbii f2_sbcbii f3_sbcbii a_wsbc f1_sbcbii f2_sbcbii f3_sbcbii a_wsbc a_wb p_trud $.
$}

$(Formula-building inference rule for class substitution.  (Contributed by
       NM, 11-Nov-2005.)  (New usage is discouraged.) $)

${
	$v ph ps x A V  $.
	f0_sbcbiiOLD $f wff ph $.
	f1_sbcbiiOLD $f wff ps $.
	f2_sbcbiiOLD $f set x $.
	f3_sbcbiiOLD $f class A $.
	f4_sbcbiiOLD $f class V $.
	e0_sbcbiiOLD $e |- ( ph <-> ps ) $.
	p_sbcbiiOLD $p |- ( A e. V -> ( [. A / x ]. ph <-> [. A / x ]. ps ) ) $= e0_sbcbiiOLD f0_sbcbiiOLD f1_sbcbiiOLD f2_sbcbiiOLD f3_sbcbiiOLD p_sbcbii f0_sbcbiiOLD f2_sbcbiiOLD f3_sbcbiiOLD a_wsbc f1_sbcbiiOLD f2_sbcbiiOLD f3_sbcbiiOLD a_wsbc a_wb f3_sbcbiiOLD f4_sbcbiiOLD a_wcel p_a1i $.
$}

$(~ eqsbc3 with set variable on right side of equals sign.  This proof was
       automatically generated from the virtual deduction proof ~ eqsbc3rVD
       using a translation program.  (Contributed by Alan Sare,
       24-Oct-2011.) $)

${
	$v x A B C  $.
	$d x C  $.
	$d x A  $.
	f0_eqsbc3r $f set x $.
	f1_eqsbc3r $f class A $.
	f2_eqsbc3r $f class B $.
	f3_eqsbc3r $f class C $.
	p_eqsbc3r $p |- ( A e. B -> ( [. A / x ]. C = x <-> C = A ) ) $= f3_eqsbc3r f0_eqsbc3r a_sup_set_class p_eqcom f3_eqsbc3r f0_eqsbc3r a_sup_set_class a_wceq f0_eqsbc3r a_sup_set_class f3_eqsbc3r a_wceq f0_eqsbc3r f1_eqsbc3r p_sbcbii f3_eqsbc3r f0_eqsbc3r a_sup_set_class a_wceq f0_eqsbc3r f1_eqsbc3r a_wsbc f0_eqsbc3r a_sup_set_class f3_eqsbc3r a_wceq f0_eqsbc3r f1_eqsbc3r a_wsbc p_biimpi f0_eqsbc3r f1_eqsbc3r f3_eqsbc3r f2_eqsbc3r p_eqsbc3 f3_eqsbc3r f0_eqsbc3r a_sup_set_class a_wceq f0_eqsbc3r f1_eqsbc3r a_wsbc f0_eqsbc3r a_sup_set_class f3_eqsbc3r a_wceq f0_eqsbc3r f1_eqsbc3r a_wsbc f1_eqsbc3r f2_eqsbc3r a_wcel f1_eqsbc3r f3_eqsbc3r a_wceq p_syl5ib f1_eqsbc3r f3_eqsbc3r p_eqcom f1_eqsbc3r f2_eqsbc3r a_wcel f3_eqsbc3r f0_eqsbc3r a_sup_set_class a_wceq f0_eqsbc3r f1_eqsbc3r a_wsbc f1_eqsbc3r f3_eqsbc3r a_wceq f3_eqsbc3r f1_eqsbc3r a_wceq p_syl6ib f1_eqsbc3r f2_eqsbc3r a_wcel f3_eqsbc3r f1_eqsbc3r a_wceq p_idd f1_eqsbc3r f3_eqsbc3r p_eqcom f1_eqsbc3r f2_eqsbc3r a_wcel f3_eqsbc3r f1_eqsbc3r a_wceq f3_eqsbc3r f1_eqsbc3r a_wceq f1_eqsbc3r f3_eqsbc3r a_wceq p_syl6ibr f0_eqsbc3r f1_eqsbc3r f3_eqsbc3r f2_eqsbc3r p_eqsbc3 f1_eqsbc3r f2_eqsbc3r a_wcel f3_eqsbc3r f1_eqsbc3r a_wceq f1_eqsbc3r f3_eqsbc3r a_wceq f0_eqsbc3r a_sup_set_class f3_eqsbc3r a_wceq f0_eqsbc3r f1_eqsbc3r a_wsbc p_sylibrd f3_eqsbc3r f0_eqsbc3r a_sup_set_class p_eqcom f3_eqsbc3r f0_eqsbc3r a_sup_set_class a_wceq f0_eqsbc3r a_sup_set_class f3_eqsbc3r a_wceq f0_eqsbc3r f1_eqsbc3r p_sbcbii f1_eqsbc3r f2_eqsbc3r a_wcel f3_eqsbc3r f1_eqsbc3r a_wceq f0_eqsbc3r a_sup_set_class f3_eqsbc3r a_wceq f0_eqsbc3r f1_eqsbc3r a_wsbc f3_eqsbc3r f0_eqsbc3r a_sup_set_class a_wceq f0_eqsbc3r f1_eqsbc3r a_wsbc p_syl6ibr f1_eqsbc3r f2_eqsbc3r a_wcel f3_eqsbc3r f0_eqsbc3r a_sup_set_class a_wceq f0_eqsbc3r f1_eqsbc3r a_wsbc f3_eqsbc3r f1_eqsbc3r a_wceq p_impbid $.
$}

$(Distribution of class substitution over triple conjunction.
       (Contributed by NM, 14-Dec-2006.)  (Proof shortened by Andrew Salmon,
       29-Jun-2011.) $)

${
	$v ph ps ch x A V  $.
	$d y ch  $.
	$d y ps  $.
	$d y ph  $.
	$d y A  $.
	$d x y  $.
	f0_sbc3ang $f wff ph $.
	f1_sbc3ang $f wff ps $.
	f2_sbc3ang $f wff ch $.
	f3_sbc3ang $f set x $.
	f4_sbc3ang $f class A $.
	f5_sbc3ang $f class V $.
	i0_sbc3ang $f set y $.
	p_sbc3ang $p |- ( A e. V -> ( [. A / x ]. ( ph /\ ps /\ ch ) <-> ( [. A / x ]. ph /\ [. A / x ]. ps /\ [. A / x ]. ch ) ) ) $= f0_sbc3ang f1_sbc3ang f2_sbc3ang a_w3a f3_sbc3ang i0_sbc3ang f4_sbc3ang p_dfsbcq2 f0_sbc3ang f3_sbc3ang i0_sbc3ang f4_sbc3ang p_dfsbcq2 f1_sbc3ang f3_sbc3ang i0_sbc3ang f4_sbc3ang p_dfsbcq2 f2_sbc3ang f3_sbc3ang i0_sbc3ang f4_sbc3ang p_dfsbcq2 i0_sbc3ang a_sup_set_class f4_sbc3ang a_wceq f0_sbc3ang f3_sbc3ang i0_sbc3ang a_wsb f0_sbc3ang f3_sbc3ang f4_sbc3ang a_wsbc f1_sbc3ang f3_sbc3ang i0_sbc3ang a_wsb f1_sbc3ang f3_sbc3ang f4_sbc3ang a_wsbc f2_sbc3ang f3_sbc3ang i0_sbc3ang a_wsb f2_sbc3ang f3_sbc3ang f4_sbc3ang a_wsbc p_3anbi123d f0_sbc3ang f1_sbc3ang f2_sbc3ang f3_sbc3ang i0_sbc3ang p_sb3an f0_sbc3ang f1_sbc3ang f2_sbc3ang a_w3a f3_sbc3ang i0_sbc3ang a_wsb f0_sbc3ang f3_sbc3ang i0_sbc3ang a_wsb f1_sbc3ang f3_sbc3ang i0_sbc3ang a_wsb f2_sbc3ang f3_sbc3ang i0_sbc3ang a_wsb a_w3a f0_sbc3ang f1_sbc3ang f2_sbc3ang a_w3a f3_sbc3ang f4_sbc3ang a_wsbc f0_sbc3ang f3_sbc3ang f4_sbc3ang a_wsbc f1_sbc3ang f3_sbc3ang f4_sbc3ang a_wsbc f2_sbc3ang f3_sbc3ang f4_sbc3ang a_wsbc a_w3a i0_sbc3ang f4_sbc3ang f5_sbc3ang p_vtoclbg $.
$}

$(Class substitution into a membership relation.  (Contributed by NM,
       17-Nov-2006.)  (Proof shortened by Andrew Salmon, 29-Jun-2011.) $)

${
	$v x A B V  $.
	$d y A  $.
	$d x y B  $.
	f0_sbcel1gv $f set x $.
	f1_sbcel1gv $f class A $.
	f2_sbcel1gv $f class B $.
	f3_sbcel1gv $f class V $.
	i0_sbcel1gv $f set y $.
	p_sbcel1gv $p |- ( A e. V -> ( [. A / x ]. x e. B <-> A e. B ) ) $= f0_sbcel1gv a_sup_set_class f2_sbcel1gv a_wcel f0_sbcel1gv i0_sbcel1gv f1_sbcel1gv p_dfsbcq2 i0_sbcel1gv a_sup_set_class f1_sbcel1gv f2_sbcel1gv p_eleq1 i0_sbcel1gv f0_sbcel1gv f2_sbcel1gv p_clelsb3 f0_sbcel1gv a_sup_set_class f2_sbcel1gv a_wcel f0_sbcel1gv i0_sbcel1gv a_wsb i0_sbcel1gv a_sup_set_class f2_sbcel1gv a_wcel f0_sbcel1gv a_sup_set_class f2_sbcel1gv a_wcel f0_sbcel1gv f1_sbcel1gv a_wsbc f1_sbcel1gv f2_sbcel1gv a_wcel i0_sbcel1gv f1_sbcel1gv f3_sbcel1gv p_vtoclbg $.
$}

$(Class substitution into a membership relation.  (Contributed by NM,
       17-Nov-2006.)  (Proof shortened by Andrew Salmon, 29-Jun-2011.) $)

${
	$v x A B V  $.
	$d y B  $.
	$d x y A  $.
	f0_sbcel2gv $f set x $.
	f1_sbcel2gv $f class A $.
	f2_sbcel2gv $f class B $.
	f3_sbcel2gv $f class V $.
	i0_sbcel2gv $f set y $.
	p_sbcel2gv $p |- ( B e. V -> ( [. B / x ]. A e. x <-> A e. B ) ) $= f1_sbcel2gv f0_sbcel2gv a_sup_set_class a_wcel f0_sbcel2gv i0_sbcel2gv f2_sbcel2gv p_dfsbcq2 i0_sbcel2gv a_sup_set_class f2_sbcel2gv f1_sbcel2gv p_eleq2 f1_sbcel2gv i0_sbcel2gv a_sup_set_class a_wcel f0_sbcel2gv p_nfv f0_sbcel2gv a_sup_set_class i0_sbcel2gv a_sup_set_class f1_sbcel2gv p_eleq2 f1_sbcel2gv f0_sbcel2gv a_sup_set_class a_wcel f1_sbcel2gv i0_sbcel2gv a_sup_set_class a_wcel f0_sbcel2gv i0_sbcel2gv p_sbie f1_sbcel2gv f0_sbcel2gv a_sup_set_class a_wcel f0_sbcel2gv i0_sbcel2gv a_wsb f1_sbcel2gv i0_sbcel2gv a_sup_set_class a_wcel f1_sbcel2gv f0_sbcel2gv a_sup_set_class a_wcel f0_sbcel2gv f2_sbcel2gv a_wsbc f1_sbcel2gv f2_sbcel2gv a_wcel i0_sbcel2gv f2_sbcel2gv f3_sbcel2gv p_vtoclbg $.
$}

$(Substitution analog of Theorem 19.20 of [Margaris] p. 90.  (Contributed
       by NM, 11-Nov-2005.) $)

${
	$v ph ps ch x A V  $.
	$d x ph  $.
	f0_sbcimdv $f wff ph $.
	f1_sbcimdv $f wff ps $.
	f2_sbcimdv $f wff ch $.
	f3_sbcimdv $f set x $.
	f4_sbcimdv $f class A $.
	f5_sbcimdv $f class V $.
	e0_sbcimdv $e |- ( ph -> ( ps -> ch ) ) $.
	p_sbcimdv $p |- ( ( ph /\ A e. V ) -> ( [. A / x ]. ps -> [. A / x ]. ch ) ) $= e0_sbcimdv f0_sbcimdv f1_sbcimdv f2_sbcimdv a_wi f3_sbcimdv p_alrimiv f1_sbcimdv f2_sbcimdv a_wi f3_sbcimdv f4_sbcimdv f5_sbcimdv p_spsbc f0_sbcimdv f1_sbcimdv f2_sbcimdv a_wi f3_sbcimdv a_wal f4_sbcimdv f5_sbcimdv a_wcel f1_sbcimdv f2_sbcimdv a_wi f3_sbcimdv f4_sbcimdv a_wsbc p_syl5 f1_sbcimdv f2_sbcimdv f3_sbcimdv f4_sbcimdv f5_sbcimdv p_sbcimg f4_sbcimdv f5_sbcimdv a_wcel f0_sbcimdv f1_sbcimdv f2_sbcimdv a_wi f3_sbcimdv f4_sbcimdv a_wsbc f1_sbcimdv f3_sbcimdv f4_sbcimdv a_wsbc f2_sbcimdv f3_sbcimdv f4_sbcimdv a_wsbc a_wi p_sylibd f4_sbcimdv f5_sbcimdv a_wcel f0_sbcimdv f1_sbcimdv f3_sbcimdv f4_sbcimdv a_wsbc f2_sbcimdv f3_sbcimdv f4_sbcimdv a_wsbc a_wi p_impcom $.
$}

$(Substitution for a variable not free in a wff does not affect it.
       (Contributed by Mario Carneiro, 14-Oct-2016.) $)

${
	$v ph x A V  $.
	$d x y  $.
	$d y A  $.
	$d y ph  $.
	f0_sbctt $f wff ph $.
	f1_sbctt $f set x $.
	f2_sbctt $f class A $.
	f3_sbctt $f class V $.
	i0_sbctt $f set y $.
	p_sbctt $p |- ( ( A e. V /\ F/ x ph ) -> ( [. A / x ]. ph <-> ph ) ) $= f0_sbctt f1_sbctt i0_sbctt f2_sbctt p_dfsbcq2 i0_sbctt a_sup_set_class f2_sbctt a_wceq f0_sbctt f1_sbctt i0_sbctt a_wsb f0_sbctt f1_sbctt f2_sbctt a_wsbc f0_sbctt p_bibi1d i0_sbctt a_sup_set_class f2_sbctt a_wceq f0_sbctt f1_sbctt i0_sbctt a_wsb f0_sbctt a_wb f0_sbctt f1_sbctt f2_sbctt a_wsbc f0_sbctt a_wb f0_sbctt f1_sbctt a_wnf p_imbi2d f0_sbctt f1_sbctt i0_sbctt p_sbft f0_sbctt f1_sbctt a_wnf f0_sbctt f1_sbctt i0_sbctt a_wsb f0_sbctt a_wb a_wi f0_sbctt f1_sbctt a_wnf f0_sbctt f1_sbctt f2_sbctt a_wsbc f0_sbctt a_wb a_wi i0_sbctt f2_sbctt f3_sbctt p_vtoclg f2_sbctt f3_sbctt a_wcel f0_sbctt f1_sbctt a_wnf f0_sbctt f1_sbctt f2_sbctt a_wsbc f0_sbctt a_wb p_imp $.
$}

$(Substitution for a variable not free in a wff does not affect it.
       (Contributed by NM, 11-Oct-2004.)  (Proof shortened by Andrew Salmon,
       29-Jun-2011.) $)

${
	$v ph x A V  $.
	$d A  $.
	$d ph  $.
	$d x  $.
	f0_sbcgf $f wff ph $.
	f1_sbcgf $f set x $.
	f2_sbcgf $f class A $.
	f3_sbcgf $f class V $.
	e0_sbcgf $e |- F/ x ph $.
	p_sbcgf $p |- ( A e. V -> ( [. A / x ]. ph <-> ph ) ) $= e0_sbcgf f0_sbcgf f1_sbcgf f2_sbcgf f3_sbcgf p_sbctt f2_sbcgf f3_sbcgf a_wcel f0_sbcgf f1_sbcgf a_wnf f0_sbcgf f1_sbcgf f2_sbcgf a_wsbc f0_sbcgf a_wb p_mpan2 $.
$}

$(Substitution for a variable not free in antecedent affects only the
       consequent.  (Contributed by NM, 11-Oct-2004.) $)

${
	$v ph ps x A V  $.
	$d A  $.
	$d ph  $.
	$d x  $.
	f0_sbc19.21g $f wff ph $.
	f1_sbc19.21g $f wff ps $.
	f2_sbc19.21g $f set x $.
	f3_sbc19.21g $f class A $.
	f4_sbc19.21g $f class V $.
	e0_sbc19.21g $e |- F/ x ph $.
	p_sbc19.21g $p |- ( A e. V -> ( [. A / x ]. ( ph -> ps ) <-> ( ph -> [. A / x ]. ps ) ) ) $= f0_sbc19.21g f1_sbc19.21g f2_sbc19.21g f3_sbc19.21g f4_sbc19.21g p_sbcimg e0_sbc19.21g f0_sbc19.21g f2_sbc19.21g f3_sbc19.21g f4_sbc19.21g p_sbcgf f3_sbc19.21g f4_sbc19.21g a_wcel f0_sbc19.21g f2_sbc19.21g f3_sbc19.21g a_wsbc f0_sbc19.21g f1_sbc19.21g f2_sbc19.21g f3_sbc19.21g a_wsbc p_imbi1d f3_sbc19.21g f4_sbc19.21g a_wcel f0_sbc19.21g f1_sbc19.21g a_wi f2_sbc19.21g f3_sbc19.21g a_wsbc f0_sbc19.21g f2_sbc19.21g f3_sbc19.21g a_wsbc f1_sbc19.21g f2_sbc19.21g f3_sbc19.21g a_wsbc a_wi f0_sbc19.21g f1_sbc19.21g f2_sbc19.21g f3_sbc19.21g a_wsbc a_wi p_bitrd $.
$}

$(Substitution for a variable not occurring in a wff does not affect it.
       Distinct variable form of ~ sbcgf .  (Contributed by Alan Sare,
       10-Nov-2012.) $)

${
	$v ph x A V  $.
	$d x ph  $.
	f0_sbcg $f wff ph $.
	f1_sbcg $f set x $.
	f2_sbcg $f class A $.
	f3_sbcg $f class V $.
	p_sbcg $p |- ( A e. V -> ( [. A / x ]. ph <-> ph ) ) $= f0_sbcg f1_sbcg p_nfv f0_sbcg f1_sbcg f2_sbcg f3_sbcg p_sbcgf $.
$}

$(Conversion of implicit substitution to explicit class substitution.
       (Contributed by Mario Carneiro, 19-Dec-2013.) $)

${
	$v ph ps x y A B V W  $.
	$d x y A  $.
	$d y B  $.
	$d x V  $.
	$d y W  $.
	f0_sbc2iegf $f wff ph $.
	f1_sbc2iegf $f wff ps $.
	f2_sbc2iegf $f set x $.
	f3_sbc2iegf $f set y $.
	f4_sbc2iegf $f class A $.
	f5_sbc2iegf $f class B $.
	f6_sbc2iegf $f class V $.
	f7_sbc2iegf $f class W $.
	e0_sbc2iegf $e |- F/ x ps $.
	e1_sbc2iegf $e |- F/ y ps $.
	e2_sbc2iegf $e |- F/ x B e. W $.
	e3_sbc2iegf $e |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) ) $.
	p_sbc2iegf $p |- ( ( A e. V /\ B e. W ) -> ( [. A / x ]. [. B / y ]. ph <-> ps ) ) $= f4_sbc2iegf f6_sbc2iegf a_wcel f5_sbc2iegf f7_sbc2iegf a_wcel p_simpl f5_sbc2iegf f7_sbc2iegf a_wcel f2_sbc2iegf a_sup_set_class f4_sbc2iegf a_wceq p_simpl e3_sbc2iegf f2_sbc2iegf a_sup_set_class f4_sbc2iegf a_wceq f3_sbc2iegf a_sup_set_class f5_sbc2iegf a_wceq f0_sbc2iegf f1_sbc2iegf a_wb f5_sbc2iegf f7_sbc2iegf a_wcel p_adantll f5_sbc2iegf f7_sbc2iegf a_wcel f2_sbc2iegf a_sup_set_class f4_sbc2iegf a_wceq a_wa f3_sbc2iegf p_nfv e1_sbc2iegf f1_sbc2iegf f3_sbc2iegf a_wnf f5_sbc2iegf f7_sbc2iegf a_wcel f2_sbc2iegf a_sup_set_class f4_sbc2iegf a_wceq a_wa p_a1i f5_sbc2iegf f7_sbc2iegf a_wcel f2_sbc2iegf a_sup_set_class f4_sbc2iegf a_wceq a_wa f0_sbc2iegf f1_sbc2iegf f3_sbc2iegf f5_sbc2iegf f7_sbc2iegf p_sbciedf f5_sbc2iegf f7_sbc2iegf a_wcel f2_sbc2iegf a_sup_set_class f4_sbc2iegf a_wceq f0_sbc2iegf f3_sbc2iegf f5_sbc2iegf a_wsbc f1_sbc2iegf a_wb f4_sbc2iegf f6_sbc2iegf a_wcel p_adantll f4_sbc2iegf f6_sbc2iegf a_wcel f2_sbc2iegf p_nfv e2_sbc2iegf f4_sbc2iegf f6_sbc2iegf a_wcel f5_sbc2iegf f7_sbc2iegf a_wcel f2_sbc2iegf p_nfan e0_sbc2iegf f1_sbc2iegf f2_sbc2iegf a_wnf f4_sbc2iegf f6_sbc2iegf a_wcel f5_sbc2iegf f7_sbc2iegf a_wcel a_wa p_a1i f4_sbc2iegf f6_sbc2iegf a_wcel f5_sbc2iegf f7_sbc2iegf a_wcel a_wa f0_sbc2iegf f3_sbc2iegf f5_sbc2iegf a_wsbc f1_sbc2iegf f2_sbc2iegf f4_sbc2iegf f6_sbc2iegf p_sbciedf $.
$}

$(Conversion of implicit substitution to explicit class substitution.
       (Contributed by NM, 16-Dec-2008.)  (Revised by Mario Carneiro,
       19-Dec-2013.) $)

${
	$v ph ps x y A B  $.
	$d x y A  $.
	$d y B  $.
	$d x y ps  $.
	f0_sbc2ie $f wff ph $.
	f1_sbc2ie $f wff ps $.
	f2_sbc2ie $f set x $.
	f3_sbc2ie $f set y $.
	f4_sbc2ie $f class A $.
	f5_sbc2ie $f class B $.
	e0_sbc2ie $e |- A e. _V $.
	e1_sbc2ie $e |- B e. _V $.
	e2_sbc2ie $e |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) ) $.
	p_sbc2ie $p |- ( [. A / x ]. [. B / y ]. ph <-> ps ) $= e0_sbc2ie e1_sbc2ie f1_sbc2ie f2_sbc2ie p_nfv f1_sbc2ie f3_sbc2ie p_nfv e1_sbc2ie f5_sbc2ie a_cvv a_wcel f2_sbc2ie p_nfth e2_sbc2ie f0_sbc2ie f1_sbc2ie f2_sbc2ie f3_sbc2ie f4_sbc2ie f5_sbc2ie a_cvv a_cvv p_sbc2iegf f4_sbc2ie a_cvv a_wcel f5_sbc2ie a_cvv a_wcel f0_sbc2ie f3_sbc2ie f5_sbc2ie a_wsbc f2_sbc2ie f4_sbc2ie a_wsbc f1_sbc2ie a_wb p_mp2an $.
$}

$(Conversion of implicit substitution to explicit class substitution.
       (Contributed by NM, 16-Dec-2008.)  (Proof shortened by Mario Carneiro,
       18-Oct-2016.) $)

${
	$v ph ps ch x y A B  $.
	$d x y A  $.
	$d y B  $.
	$d x y ph  $.
	$d x y ch  $.
	f0_sbc2iedv $f wff ph $.
	f1_sbc2iedv $f wff ps $.
	f2_sbc2iedv $f wff ch $.
	f3_sbc2iedv $f set x $.
	f4_sbc2iedv $f set y $.
	f5_sbc2iedv $f class A $.
	f6_sbc2iedv $f class B $.
	e0_sbc2iedv $e |- A e. _V $.
	e1_sbc2iedv $e |- B e. _V $.
	e2_sbc2iedv $e |- ( ph -> ( ( x = A /\ y = B ) -> ( ps <-> ch ) ) ) $.
	p_sbc2iedv $p |- ( ph -> ( [. A / x ]. [. B / y ]. ps <-> ch ) ) $= e0_sbc2iedv f5_sbc2iedv a_cvv a_wcel f0_sbc2iedv p_a1i e1_sbc2iedv f6_sbc2iedv a_cvv a_wcel f0_sbc2iedv f3_sbc2iedv a_sup_set_class f5_sbc2iedv a_wceq a_wa p_a1i e2_sbc2iedv f0_sbc2iedv f3_sbc2iedv a_sup_set_class f5_sbc2iedv a_wceq f4_sbc2iedv a_sup_set_class f6_sbc2iedv a_wceq f1_sbc2iedv f2_sbc2iedv a_wb p_impl f0_sbc2iedv f3_sbc2iedv a_sup_set_class f5_sbc2iedv a_wceq a_wa f1_sbc2iedv f2_sbc2iedv f4_sbc2iedv f6_sbc2iedv a_cvv p_sbcied f0_sbc2iedv f1_sbc2iedv f4_sbc2iedv f6_sbc2iedv a_wsbc f2_sbc2iedv f3_sbc2iedv f5_sbc2iedv a_cvv p_sbcied $.
$}

$(Conversion of implicit substitution to explicit class substitution.
       (Contributed by Mario Carneiro, 19-Jun-2014.)  (Revised by Mario
       Carneiro, 29-Dec-2014.) $)

${
	$v ph ps x y z A B C  $.
	$d x y z A  $.
	$d y z B  $.
	$d z C  $.
	$d x y z ps  $.
	f0_sbc3ie $f wff ph $.
	f1_sbc3ie $f wff ps $.
	f2_sbc3ie $f set x $.
	f3_sbc3ie $f set y $.
	f4_sbc3ie $f set z $.
	f5_sbc3ie $f class A $.
	f6_sbc3ie $f class B $.
	f7_sbc3ie $f class C $.
	e0_sbc3ie $e |- A e. _V $.
	e1_sbc3ie $e |- B e. _V $.
	e2_sbc3ie $e |- C e. _V $.
	e3_sbc3ie $e |- ( ( x = A /\ y = B /\ z = C ) -> ( ph <-> ps ) ) $.
	p_sbc3ie $p |- ( [. A / x ]. [. B / y ]. [. C / z ]. ph <-> ps ) $= e0_sbc3ie e1_sbc3ie e2_sbc3ie f7_sbc3ie a_cvv a_wcel f2_sbc3ie a_sup_set_class f5_sbc3ie a_wceq f3_sbc3ie a_sup_set_class f6_sbc3ie a_wceq a_wa p_a1i e3_sbc3ie f2_sbc3ie a_sup_set_class f5_sbc3ie a_wceq f3_sbc3ie a_sup_set_class f6_sbc3ie a_wceq f4_sbc3ie a_sup_set_class f7_sbc3ie a_wceq f0_sbc3ie f1_sbc3ie a_wb p_3expa f2_sbc3ie a_sup_set_class f5_sbc3ie a_wceq f3_sbc3ie a_sup_set_class f6_sbc3ie a_wceq a_wa f0_sbc3ie f1_sbc3ie f4_sbc3ie f7_sbc3ie a_cvv p_sbcied f0_sbc3ie f4_sbc3ie f7_sbc3ie a_wsbc f1_sbc3ie f2_sbc3ie f3_sbc3ie f5_sbc3ie f6_sbc3ie p_sbc2ie $.
$}

$(Lemma for ~ sbccom .  (Contributed by NM, 14-Nov-2005.)  (Revised by
       Mario Carneiro, 18-Oct-2016.) $)

${
	$v ph x y A B  $.
	$d x y A  $.
	$d x y B  $.
	$d y  $.
	$d x  $.
	f0_sbccomlem $f wff ph $.
	f1_sbccomlem $f set x $.
	f2_sbccomlem $f set y $.
	f3_sbccomlem $f class A $.
	f4_sbccomlem $f class B $.
	p_sbccomlem $p |- ( [. A / x ]. [. B / y ]. ph <-> [. B / y ]. [. A / x ]. ph ) $= f1_sbccomlem a_sup_set_class f3_sbccomlem a_wceq f2_sbccomlem a_sup_set_class f4_sbccomlem a_wceq f0_sbccomlem a_wa a_wa f1_sbccomlem f2_sbccomlem p_excom f1_sbccomlem a_sup_set_class f3_sbccomlem a_wceq f2_sbccomlem a_sup_set_class f4_sbccomlem a_wceq f0_sbccomlem a_wa f1_sbccomlem f2_sbccomlem p_exdistr f1_sbccomlem a_sup_set_class f3_sbccomlem a_wceq f2_sbccomlem a_sup_set_class f4_sbccomlem a_wceq f0_sbccomlem p_an12 f1_sbccomlem a_sup_set_class f3_sbccomlem a_wceq f2_sbccomlem a_sup_set_class f4_sbccomlem a_wceq f0_sbccomlem a_wa a_wa f2_sbccomlem a_sup_set_class f4_sbccomlem a_wceq f1_sbccomlem a_sup_set_class f3_sbccomlem a_wceq f0_sbccomlem a_wa a_wa f1_sbccomlem p_exbii f2_sbccomlem a_sup_set_class f4_sbccomlem a_wceq f1_sbccomlem a_sup_set_class f3_sbccomlem a_wceq f0_sbccomlem a_wa f1_sbccomlem p_19.42v f1_sbccomlem a_sup_set_class f3_sbccomlem a_wceq f2_sbccomlem a_sup_set_class f4_sbccomlem a_wceq f0_sbccomlem a_wa a_wa f1_sbccomlem a_wex f2_sbccomlem a_sup_set_class f4_sbccomlem a_wceq f1_sbccomlem a_sup_set_class f3_sbccomlem a_wceq f0_sbccomlem a_wa a_wa f1_sbccomlem a_wex f2_sbccomlem a_sup_set_class f4_sbccomlem a_wceq f1_sbccomlem a_sup_set_class f3_sbccomlem a_wceq f0_sbccomlem a_wa f1_sbccomlem a_wex a_wa p_bitri f1_sbccomlem a_sup_set_class f3_sbccomlem a_wceq f2_sbccomlem a_sup_set_class f4_sbccomlem a_wceq f0_sbccomlem a_wa a_wa f1_sbccomlem a_wex f2_sbccomlem a_sup_set_class f4_sbccomlem a_wceq f1_sbccomlem a_sup_set_class f3_sbccomlem a_wceq f0_sbccomlem a_wa f1_sbccomlem a_wex a_wa f2_sbccomlem p_exbii f1_sbccomlem a_sup_set_class f3_sbccomlem a_wceq f2_sbccomlem a_sup_set_class f4_sbccomlem a_wceq f0_sbccomlem a_wa a_wa f2_sbccomlem a_wex f1_sbccomlem a_wex f1_sbccomlem a_sup_set_class f3_sbccomlem a_wceq f2_sbccomlem a_sup_set_class f4_sbccomlem a_wceq f0_sbccomlem a_wa a_wa f1_sbccomlem a_wex f2_sbccomlem a_wex f1_sbccomlem a_sup_set_class f3_sbccomlem a_wceq f2_sbccomlem a_sup_set_class f4_sbccomlem a_wceq f0_sbccomlem a_wa f2_sbccomlem a_wex a_wa f1_sbccomlem a_wex f2_sbccomlem a_sup_set_class f4_sbccomlem a_wceq f1_sbccomlem a_sup_set_class f3_sbccomlem a_wceq f0_sbccomlem a_wa f1_sbccomlem a_wex a_wa f2_sbccomlem a_wex p_3bitr3i f2_sbccomlem a_sup_set_class f4_sbccomlem a_wceq f0_sbccomlem a_wa f2_sbccomlem a_wex f1_sbccomlem f3_sbccomlem p_sbc5 f1_sbccomlem a_sup_set_class f3_sbccomlem a_wceq f0_sbccomlem a_wa f1_sbccomlem a_wex f2_sbccomlem f4_sbccomlem p_sbc5 f1_sbccomlem a_sup_set_class f3_sbccomlem a_wceq f2_sbccomlem a_sup_set_class f4_sbccomlem a_wceq f0_sbccomlem a_wa f2_sbccomlem a_wex a_wa f1_sbccomlem a_wex f2_sbccomlem a_sup_set_class f4_sbccomlem a_wceq f1_sbccomlem a_sup_set_class f3_sbccomlem a_wceq f0_sbccomlem a_wa f1_sbccomlem a_wex a_wa f2_sbccomlem a_wex f2_sbccomlem a_sup_set_class f4_sbccomlem a_wceq f0_sbccomlem a_wa f2_sbccomlem a_wex f1_sbccomlem f3_sbccomlem a_wsbc f1_sbccomlem a_sup_set_class f3_sbccomlem a_wceq f0_sbccomlem a_wa f1_sbccomlem a_wex f2_sbccomlem f4_sbccomlem a_wsbc p_3bitr4i f0_sbccomlem f2_sbccomlem f4_sbccomlem p_sbc5 f0_sbccomlem f2_sbccomlem f4_sbccomlem a_wsbc f2_sbccomlem a_sup_set_class f4_sbccomlem a_wceq f0_sbccomlem a_wa f2_sbccomlem a_wex f1_sbccomlem f3_sbccomlem p_sbcbii f0_sbccomlem f1_sbccomlem f3_sbccomlem p_sbc5 f0_sbccomlem f1_sbccomlem f3_sbccomlem a_wsbc f1_sbccomlem a_sup_set_class f3_sbccomlem a_wceq f0_sbccomlem a_wa f1_sbccomlem a_wex f2_sbccomlem f4_sbccomlem p_sbcbii f2_sbccomlem a_sup_set_class f4_sbccomlem a_wceq f0_sbccomlem a_wa f2_sbccomlem a_wex f1_sbccomlem f3_sbccomlem a_wsbc f1_sbccomlem a_sup_set_class f3_sbccomlem a_wceq f0_sbccomlem a_wa f1_sbccomlem a_wex f2_sbccomlem f4_sbccomlem a_wsbc f0_sbccomlem f2_sbccomlem f4_sbccomlem a_wsbc f1_sbccomlem f3_sbccomlem a_wsbc f0_sbccomlem f1_sbccomlem f3_sbccomlem a_wsbc f2_sbccomlem f4_sbccomlem a_wsbc p_3bitr4i $.
$}

$(Commutative law for double class substitution.  (Contributed by NM,
       15-Nov-2005.)  (Proof shortened by Mario Carneiro, 18-Oct-2016.) $)

${
	$v ph x y A B  $.
	$d w y z A  $.
	$d w x z B  $.
	$d w z ph  $.
	$d x y  $.
	f0_sbccom $f wff ph $.
	f1_sbccom $f set x $.
	f2_sbccom $f set y $.
	f3_sbccom $f class A $.
	f4_sbccom $f class B $.
	i0_sbccom $f set z $.
	i1_sbccom $f set w $.
	p_sbccom $p |- ( [. A / x ]. [. B / y ]. ph <-> [. B / y ]. [. A / x ]. ph ) $= f0_sbccom f1_sbccom i0_sbccom a_sup_set_class a_wsbc f2_sbccom i1_sbccom a_sup_set_class a_wsbc i0_sbccom i1_sbccom f3_sbccom f4_sbccom p_sbccomlem f0_sbccom f2_sbccom f1_sbccom i1_sbccom a_sup_set_class i0_sbccom a_sup_set_class p_sbccomlem f0_sbccom f1_sbccom i0_sbccom a_sup_set_class a_wsbc f2_sbccom i1_sbccom a_sup_set_class a_wsbc f0_sbccom f2_sbccom i1_sbccom a_sup_set_class a_wsbc f1_sbccom i0_sbccom a_sup_set_class a_wsbc i1_sbccom f4_sbccom p_sbcbii f0_sbccom f2_sbccom i1_sbccom a_sup_set_class a_wsbc i1_sbccom f1_sbccom f4_sbccom i0_sbccom a_sup_set_class p_sbccomlem f0_sbccom f1_sbccom i0_sbccom a_sup_set_class a_wsbc f2_sbccom i1_sbccom a_sup_set_class a_wsbc i1_sbccom f4_sbccom a_wsbc f0_sbccom f2_sbccom i1_sbccom a_sup_set_class a_wsbc f1_sbccom i0_sbccom a_sup_set_class a_wsbc i1_sbccom f4_sbccom a_wsbc f0_sbccom f2_sbccom i1_sbccom a_sup_set_class a_wsbc i1_sbccom f4_sbccom a_wsbc f1_sbccom i0_sbccom a_sup_set_class a_wsbc p_bitri f0_sbccom f1_sbccom i0_sbccom a_sup_set_class a_wsbc f2_sbccom i1_sbccom a_sup_set_class a_wsbc i1_sbccom f4_sbccom a_wsbc f0_sbccom f2_sbccom i1_sbccom a_sup_set_class a_wsbc i1_sbccom f4_sbccom a_wsbc f1_sbccom i0_sbccom a_sup_set_class a_wsbc i0_sbccom f3_sbccom p_sbcbii f0_sbccom f1_sbccom i0_sbccom a_sup_set_class a_wsbc i0_sbccom f2_sbccom f3_sbccom i1_sbccom a_sup_set_class p_sbccomlem f0_sbccom f1_sbccom i0_sbccom a_sup_set_class a_wsbc f2_sbccom i1_sbccom a_sup_set_class a_wsbc i0_sbccom f3_sbccom a_wsbc f0_sbccom f1_sbccom i0_sbccom a_sup_set_class a_wsbc i0_sbccom f3_sbccom a_wsbc f2_sbccom i1_sbccom a_sup_set_class a_wsbc i1_sbccom f4_sbccom p_sbcbii f0_sbccom f1_sbccom i0_sbccom a_sup_set_class a_wsbc f2_sbccom i1_sbccom a_sup_set_class a_wsbc i1_sbccom f4_sbccom a_wsbc i0_sbccom f3_sbccom a_wsbc f0_sbccom f1_sbccom i0_sbccom a_sup_set_class a_wsbc f2_sbccom i1_sbccom a_sup_set_class a_wsbc i0_sbccom f3_sbccom a_wsbc i1_sbccom f4_sbccom a_wsbc f0_sbccom f2_sbccom i1_sbccom a_sup_set_class a_wsbc i1_sbccom f4_sbccom a_wsbc f1_sbccom i0_sbccom a_sup_set_class a_wsbc i0_sbccom f3_sbccom a_wsbc f0_sbccom f1_sbccom i0_sbccom a_sup_set_class a_wsbc i0_sbccom f3_sbccom a_wsbc f2_sbccom i1_sbccom a_sup_set_class a_wsbc i1_sbccom f4_sbccom a_wsbc p_3bitr3i f0_sbccom f2_sbccom i1_sbccom a_sup_set_class a_wsbc i1_sbccom f4_sbccom a_wsbc f1_sbccom i0_sbccom f3_sbccom p_sbcco f0_sbccom f1_sbccom i0_sbccom a_sup_set_class a_wsbc i0_sbccom f3_sbccom a_wsbc f2_sbccom i1_sbccom f4_sbccom p_sbcco f0_sbccom f2_sbccom i1_sbccom a_sup_set_class a_wsbc i1_sbccom f4_sbccom a_wsbc f1_sbccom i0_sbccom a_sup_set_class a_wsbc i0_sbccom f3_sbccom a_wsbc f0_sbccom f1_sbccom i0_sbccom a_sup_set_class a_wsbc i0_sbccom f3_sbccom a_wsbc f2_sbccom i1_sbccom a_sup_set_class a_wsbc i1_sbccom f4_sbccom a_wsbc f0_sbccom f2_sbccom i1_sbccom a_sup_set_class a_wsbc i1_sbccom f4_sbccom a_wsbc f1_sbccom f3_sbccom a_wsbc f0_sbccom f1_sbccom i0_sbccom a_sup_set_class a_wsbc i0_sbccom f3_sbccom a_wsbc f2_sbccom f4_sbccom a_wsbc p_3bitr3i f0_sbccom f2_sbccom i1_sbccom f4_sbccom p_sbcco f0_sbccom f2_sbccom i1_sbccom a_sup_set_class a_wsbc i1_sbccom f4_sbccom a_wsbc f0_sbccom f2_sbccom f4_sbccom a_wsbc f1_sbccom f3_sbccom p_sbcbii f0_sbccom f1_sbccom i0_sbccom f3_sbccom p_sbcco f0_sbccom f1_sbccom i0_sbccom a_sup_set_class a_wsbc i0_sbccom f3_sbccom a_wsbc f0_sbccom f1_sbccom f3_sbccom a_wsbc f2_sbccom f4_sbccom p_sbcbii f0_sbccom f2_sbccom i1_sbccom a_sup_set_class a_wsbc i1_sbccom f4_sbccom a_wsbc f1_sbccom f3_sbccom a_wsbc f0_sbccom f1_sbccom i0_sbccom a_sup_set_class a_wsbc i0_sbccom f3_sbccom a_wsbc f2_sbccom f4_sbccom a_wsbc f0_sbccom f2_sbccom f4_sbccom a_wsbc f1_sbccom f3_sbccom a_wsbc f0_sbccom f1_sbccom f3_sbccom a_wsbc f2_sbccom f4_sbccom a_wsbc p_3bitr3i $.
$}

$(Interchange class substitution and restricted quantifier.  (Contributed
       by NM, 1-Mar-2008.)  (Revised by David Abernethy, 22-Feb-2010.) $)

${
	$v ph x y A B V  $.
	$d x y z  $.
	$d A z  $.
	$d B x z  $.
	$d V z  $.
	$d ph z  $.
	f0_sbcralt $f wff ph $.
	f1_sbcralt $f set x $.
	f2_sbcralt $f set y $.
	f3_sbcralt $f class A $.
	f4_sbcralt $f class B $.
	f5_sbcralt $f class V $.
	i0_sbcralt $f set z $.
	p_sbcralt $p |- ( ( A e. V /\ F/_ y A ) -> ( [. A / x ]. A. y e. B ph <-> A. y e. B [. A / x ]. ph ) ) $= f0_sbcralt f2_sbcralt f4_sbcralt a_wral f1_sbcralt i0_sbcralt f3_sbcralt p_sbcco f3_sbcralt f5_sbcralt a_wcel f2_sbcralt f3_sbcralt a_wnfc p_simpl f0_sbcralt f2_sbcralt f4_sbcralt a_wral f1_sbcralt i0_sbcralt p_sbsbc f1_sbcralt f4_sbcralt p_nfcv f0_sbcralt f1_sbcralt i0_sbcralt p_nfs1v f0_sbcralt f1_sbcralt i0_sbcralt a_wsb f1_sbcralt f2_sbcralt f4_sbcralt p_nfral f0_sbcralt f1_sbcralt i0_sbcralt p_sbequ12 f1_sbcralt a_sup_set_class i0_sbcralt a_sup_set_class a_wceq f0_sbcralt f0_sbcralt f1_sbcralt i0_sbcralt a_wsb f2_sbcralt f4_sbcralt p_ralbidv f0_sbcralt f2_sbcralt f4_sbcralt a_wral f0_sbcralt f1_sbcralt i0_sbcralt a_wsb f2_sbcralt f4_sbcralt a_wral f1_sbcralt i0_sbcralt p_sbie f0_sbcralt f2_sbcralt f4_sbcralt a_wral f1_sbcralt i0_sbcralt a_sup_set_class a_wsbc f0_sbcralt f2_sbcralt f4_sbcralt a_wral f1_sbcralt i0_sbcralt a_wsb f0_sbcralt f1_sbcralt i0_sbcralt a_wsb f2_sbcralt f4_sbcralt a_wral p_bitr3i f2_sbcralt f3_sbcralt p_nfnfc1 f2_sbcralt f3_sbcralt a_wnfc f2_sbcralt i0_sbcralt a_sup_set_class p_nfcvd f2_sbcralt f3_sbcralt a_wnfc p_id f2_sbcralt f3_sbcralt a_wnfc f2_sbcralt i0_sbcralt a_sup_set_class f3_sbcralt p_nfeqd f2_sbcralt f3_sbcralt a_wnfc i0_sbcralt a_sup_set_class f3_sbcralt a_wceq f2_sbcralt p_nfan1 f0_sbcralt f1_sbcralt i0_sbcralt f3_sbcralt p_dfsbcq2 i0_sbcralt a_sup_set_class f3_sbcralt a_wceq f0_sbcralt f1_sbcralt i0_sbcralt a_wsb f0_sbcralt f1_sbcralt f3_sbcralt a_wsbc a_wb f2_sbcralt f3_sbcralt a_wnfc p_adantl f2_sbcralt f3_sbcralt a_wnfc i0_sbcralt a_sup_set_class f3_sbcralt a_wceq a_wa f0_sbcralt f1_sbcralt i0_sbcralt a_wsb f0_sbcralt f1_sbcralt f3_sbcralt a_wsbc f2_sbcralt f4_sbcralt p_ralbid f2_sbcralt f3_sbcralt a_wnfc i0_sbcralt a_sup_set_class f3_sbcralt a_wceq f0_sbcralt f1_sbcralt i0_sbcralt a_wsb f2_sbcralt f4_sbcralt a_wral f0_sbcralt f1_sbcralt f3_sbcralt a_wsbc f2_sbcralt f4_sbcralt a_wral a_wb f3_sbcralt f5_sbcralt a_wcel p_adantll f0_sbcralt f2_sbcralt f4_sbcralt a_wral f1_sbcralt i0_sbcralt a_sup_set_class a_wsbc f0_sbcralt f1_sbcralt i0_sbcralt a_wsb f2_sbcralt f4_sbcralt a_wral f3_sbcralt f5_sbcralt a_wcel f2_sbcralt f3_sbcralt a_wnfc a_wa i0_sbcralt a_sup_set_class f3_sbcralt a_wceq a_wa f0_sbcralt f1_sbcralt f3_sbcralt a_wsbc f2_sbcralt f4_sbcralt a_wral p_syl5bb f3_sbcralt f5_sbcralt a_wcel f2_sbcralt f3_sbcralt a_wnfc a_wa f0_sbcralt f2_sbcralt f4_sbcralt a_wral f1_sbcralt i0_sbcralt a_sup_set_class a_wsbc f0_sbcralt f1_sbcralt f3_sbcralt a_wsbc f2_sbcralt f4_sbcralt a_wral i0_sbcralt f3_sbcralt f5_sbcralt p_sbcied f0_sbcralt f2_sbcralt f4_sbcralt a_wral f1_sbcralt f3_sbcralt a_wsbc f0_sbcralt f2_sbcralt f4_sbcralt a_wral f1_sbcralt i0_sbcralt a_sup_set_class a_wsbc i0_sbcralt f3_sbcralt a_wsbc f3_sbcralt f5_sbcralt a_wcel f2_sbcralt f3_sbcralt a_wnfc a_wa f0_sbcralt f1_sbcralt f3_sbcralt a_wsbc f2_sbcralt f4_sbcralt a_wral p_syl5bbr $.
$}

$(Interchange class substitution and restricted existential quantifier.
       (Contributed by NM, 1-Mar-2008.)  (Proof shortened by Mario Carneiro,
       13-Oct-2016.) $)

${
	$v ph x y A B V  $.
	$d x y  $.
	$d A  $.
	$d B x  $.
	$d V  $.
	$d ph  $.
	f0_sbcrext $f wff ph $.
	f1_sbcrext $f set x $.
	f2_sbcrext $f set y $.
	f3_sbcrext $f class A $.
	f4_sbcrext $f class B $.
	f5_sbcrext $f class V $.
	p_sbcrext $p |- ( ( A e. V /\ F/_ y A ) -> ( [. A / x ]. E. y e. B ph <-> E. y e. B [. A / x ]. ph ) ) $= f3_sbcrext f5_sbcrext p_elex f0_sbcrext a_wn f2_sbcrext f4_sbcrext a_wral f1_sbcrext f3_sbcrext a_cvv p_sbcng f3_sbcrext a_cvv a_wcel f0_sbcrext a_wn f2_sbcrext f4_sbcrext a_wral a_wn f1_sbcrext f3_sbcrext a_wsbc f0_sbcrext a_wn f2_sbcrext f4_sbcrext a_wral f1_sbcrext f3_sbcrext a_wsbc a_wn a_wb f2_sbcrext f3_sbcrext a_wnfc p_adantr f0_sbcrext a_wn f1_sbcrext f2_sbcrext f3_sbcrext f4_sbcrext a_cvv p_sbcralt f2_sbcrext f3_sbcrext p_nfnfc1 f2_sbcrext f3_sbcrext a_wnfc p_id f2_sbcrext f3_sbcrext a_wnfc f2_sbcrext a_cvv p_nfcvd f2_sbcrext f3_sbcrext a_wnfc f2_sbcrext f3_sbcrext a_cvv p_nfeld f2_sbcrext f3_sbcrext a_wnfc f3_sbcrext a_cvv a_wcel f2_sbcrext p_nfan1 f0_sbcrext f1_sbcrext f3_sbcrext a_cvv p_sbcng f3_sbcrext a_cvv a_wcel f0_sbcrext a_wn f1_sbcrext f3_sbcrext a_wsbc f0_sbcrext f1_sbcrext f3_sbcrext a_wsbc a_wn a_wb f2_sbcrext f3_sbcrext a_wnfc p_adantl f2_sbcrext f3_sbcrext a_wnfc f3_sbcrext a_cvv a_wcel a_wa f0_sbcrext a_wn f1_sbcrext f3_sbcrext a_wsbc f0_sbcrext f1_sbcrext f3_sbcrext a_wsbc a_wn f2_sbcrext f4_sbcrext p_ralbid f2_sbcrext f3_sbcrext a_wnfc f3_sbcrext a_cvv a_wcel f0_sbcrext a_wn f1_sbcrext f3_sbcrext a_wsbc f2_sbcrext f4_sbcrext a_wral f0_sbcrext f1_sbcrext f3_sbcrext a_wsbc a_wn f2_sbcrext f4_sbcrext a_wral a_wb p_ancoms f3_sbcrext a_cvv a_wcel f2_sbcrext f3_sbcrext a_wnfc a_wa f0_sbcrext a_wn f2_sbcrext f4_sbcrext a_wral f1_sbcrext f3_sbcrext a_wsbc f0_sbcrext a_wn f1_sbcrext f3_sbcrext a_wsbc f2_sbcrext f4_sbcrext a_wral f0_sbcrext f1_sbcrext f3_sbcrext a_wsbc a_wn f2_sbcrext f4_sbcrext a_wral p_bitrd f3_sbcrext a_cvv a_wcel f2_sbcrext f3_sbcrext a_wnfc a_wa f0_sbcrext a_wn f2_sbcrext f4_sbcrext a_wral f1_sbcrext f3_sbcrext a_wsbc f0_sbcrext f1_sbcrext f3_sbcrext a_wsbc a_wn f2_sbcrext f4_sbcrext a_wral p_notbid f3_sbcrext a_cvv a_wcel f2_sbcrext f3_sbcrext a_wnfc a_wa f0_sbcrext a_wn f2_sbcrext f4_sbcrext a_wral a_wn f1_sbcrext f3_sbcrext a_wsbc f0_sbcrext a_wn f2_sbcrext f4_sbcrext a_wral f1_sbcrext f3_sbcrext a_wsbc a_wn f0_sbcrext f1_sbcrext f3_sbcrext a_wsbc a_wn f2_sbcrext f4_sbcrext a_wral a_wn p_bitrd f0_sbcrext f2_sbcrext f4_sbcrext p_dfrex2 f0_sbcrext f2_sbcrext f4_sbcrext a_wrex f0_sbcrext a_wn f2_sbcrext f4_sbcrext a_wral a_wn f1_sbcrext f3_sbcrext p_sbcbii f0_sbcrext f1_sbcrext f3_sbcrext a_wsbc f2_sbcrext f4_sbcrext p_dfrex2 f3_sbcrext a_cvv a_wcel f2_sbcrext f3_sbcrext a_wnfc a_wa f0_sbcrext a_wn f2_sbcrext f4_sbcrext a_wral a_wn f1_sbcrext f3_sbcrext a_wsbc f0_sbcrext f1_sbcrext f3_sbcrext a_wsbc a_wn f2_sbcrext f4_sbcrext a_wral a_wn f0_sbcrext f2_sbcrext f4_sbcrext a_wrex f1_sbcrext f3_sbcrext a_wsbc f0_sbcrext f1_sbcrext f3_sbcrext a_wsbc f2_sbcrext f4_sbcrext a_wrex p_3bitr4g f3_sbcrext f5_sbcrext a_wcel f3_sbcrext a_cvv a_wcel f2_sbcrext f3_sbcrext a_wnfc f0_sbcrext f2_sbcrext f4_sbcrext a_wrex f1_sbcrext f3_sbcrext a_wsbc f0_sbcrext f1_sbcrext f3_sbcrext a_wsbc f2_sbcrext f4_sbcrext a_wrex a_wb p_sylan $.
$}

$(Interchange class substitution and restricted quantifier.  (Contributed
       by NM, 15-Nov-2005.)  (Proof shortened by Andrew Salmon,
       29-Jun-2011.) $)

${
	$v ph x y A B V  $.
	$d y z A  $.
	$d x B  $.
	$d x y z  $.
	$d ph z  $.
	$d B z  $.
	f0_sbcralg $f wff ph $.
	f1_sbcralg $f set x $.
	f2_sbcralg $f set y $.
	f3_sbcralg $f class A $.
	f4_sbcralg $f class B $.
	f5_sbcralg $f class V $.
	i0_sbcralg $f set z $.
	p_sbcralg $p |- ( A e. V -> ( [. A / x ]. A. y e. B ph <-> A. y e. B [. A / x ]. ph ) ) $= f0_sbcralg f2_sbcralg f4_sbcralg a_wral f1_sbcralg i0_sbcralg f3_sbcralg p_dfsbcq2 f0_sbcralg f1_sbcralg i0_sbcralg f3_sbcralg p_dfsbcq2 i0_sbcralg a_sup_set_class f3_sbcralg a_wceq f0_sbcralg f1_sbcralg i0_sbcralg a_wsb f0_sbcralg f1_sbcralg f3_sbcralg a_wsbc f2_sbcralg f4_sbcralg p_ralbidv f1_sbcralg f4_sbcralg p_nfcv f0_sbcralg f1_sbcralg i0_sbcralg p_nfs1v f0_sbcralg f1_sbcralg i0_sbcralg a_wsb f1_sbcralg f2_sbcralg f4_sbcralg p_nfral f0_sbcralg f1_sbcralg i0_sbcralg p_sbequ12 f1_sbcralg a_sup_set_class i0_sbcralg a_sup_set_class a_wceq f0_sbcralg f0_sbcralg f1_sbcralg i0_sbcralg a_wsb f2_sbcralg f4_sbcralg p_ralbidv f0_sbcralg f2_sbcralg f4_sbcralg a_wral f0_sbcralg f1_sbcralg i0_sbcralg a_wsb f2_sbcralg f4_sbcralg a_wral f1_sbcralg i0_sbcralg p_sbie f0_sbcralg f2_sbcralg f4_sbcralg a_wral f1_sbcralg i0_sbcralg a_wsb f0_sbcralg f1_sbcralg i0_sbcralg a_wsb f2_sbcralg f4_sbcralg a_wral f0_sbcralg f2_sbcralg f4_sbcralg a_wral f1_sbcralg f3_sbcralg a_wsbc f0_sbcralg f1_sbcralg f3_sbcralg a_wsbc f2_sbcralg f4_sbcralg a_wral i0_sbcralg f3_sbcralg f5_sbcralg p_vtoclbg $.
$}

$(Interchange class substitution and restricted existential quantifier.
       (Contributed by NM, 15-Nov-2005.)  (Proof shortened by Andrew Salmon,
       29-Jun-2011.) $)

${
	$v ph x y A B V  $.
	$d y z A  $.
	$d x B  $.
	$d x y z  $.
	$d ph z  $.
	$d B z  $.
	f0_sbcrexg $f wff ph $.
	f1_sbcrexg $f set x $.
	f2_sbcrexg $f set y $.
	f3_sbcrexg $f class A $.
	f4_sbcrexg $f class B $.
	f5_sbcrexg $f class V $.
	i0_sbcrexg $f set z $.
	p_sbcrexg $p |- ( A e. V -> ( [. A / x ]. E. y e. B ph <-> E. y e. B [. A / x ]. ph ) ) $= f0_sbcrexg f2_sbcrexg f4_sbcrexg a_wrex f1_sbcrexg i0_sbcrexg f3_sbcrexg p_dfsbcq2 f0_sbcrexg f1_sbcrexg i0_sbcrexg f3_sbcrexg p_dfsbcq2 i0_sbcrexg a_sup_set_class f3_sbcrexg a_wceq f0_sbcrexg f1_sbcrexg i0_sbcrexg a_wsb f0_sbcrexg f1_sbcrexg f3_sbcrexg a_wsbc f2_sbcrexg f4_sbcrexg p_rexbidv f1_sbcrexg f4_sbcrexg p_nfcv f0_sbcrexg f1_sbcrexg i0_sbcrexg p_nfs1v f0_sbcrexg f1_sbcrexg i0_sbcrexg a_wsb f1_sbcrexg f2_sbcrexg f4_sbcrexg p_nfrex f0_sbcrexg f1_sbcrexg i0_sbcrexg p_sbequ12 f1_sbcrexg a_sup_set_class i0_sbcrexg a_sup_set_class a_wceq f0_sbcrexg f0_sbcrexg f1_sbcrexg i0_sbcrexg a_wsb f2_sbcrexg f4_sbcrexg p_rexbidv f0_sbcrexg f2_sbcrexg f4_sbcrexg a_wrex f0_sbcrexg f1_sbcrexg i0_sbcrexg a_wsb f2_sbcrexg f4_sbcrexg a_wrex f1_sbcrexg i0_sbcrexg p_sbie f0_sbcrexg f2_sbcrexg f4_sbcrexg a_wrex f1_sbcrexg i0_sbcrexg a_wsb f0_sbcrexg f1_sbcrexg i0_sbcrexg a_wsb f2_sbcrexg f4_sbcrexg a_wrex f0_sbcrexg f2_sbcrexg f4_sbcrexg a_wrex f1_sbcrexg f3_sbcrexg a_wsbc f0_sbcrexg f1_sbcrexg f3_sbcrexg a_wsbc f2_sbcrexg f4_sbcrexg a_wrex i0_sbcrexg f3_sbcrexg f5_sbcrexg p_vtoclbg $.
$}

$(Interchange class substitution and restricted uniqueness quantifier.
       (Contributed by NM, 24-Feb-2013.) $)

${
	$v ph x y A B V  $.
	$d y z A  $.
	$d x B  $.
	$d x y z  $.
	$d ph z  $.
	$d B z  $.
	f0_sbcreug $f wff ph $.
	f1_sbcreug $f set x $.
	f2_sbcreug $f set y $.
	f3_sbcreug $f class A $.
	f4_sbcreug $f class B $.
	f5_sbcreug $f class V $.
	i0_sbcreug $f set z $.
	p_sbcreug $p |- ( A e. V -> ( [. A / x ]. E! y e. B ph <-> E! y e. B [. A / x ]. ph ) ) $= f0_sbcreug f2_sbcreug f4_sbcreug a_wreu f1_sbcreug i0_sbcreug f3_sbcreug p_dfsbcq2 f0_sbcreug f1_sbcreug i0_sbcreug f3_sbcreug p_dfsbcq2 i0_sbcreug a_sup_set_class f3_sbcreug a_wceq f0_sbcreug f1_sbcreug i0_sbcreug a_wsb f0_sbcreug f1_sbcreug f3_sbcreug a_wsbc f2_sbcreug f4_sbcreug p_reubidv f1_sbcreug f4_sbcreug p_nfcv f0_sbcreug f1_sbcreug i0_sbcreug p_nfs1v f0_sbcreug f1_sbcreug i0_sbcreug a_wsb f1_sbcreug f2_sbcreug f4_sbcreug p_nfreu f0_sbcreug f1_sbcreug i0_sbcreug p_sbequ12 f1_sbcreug a_sup_set_class i0_sbcreug a_sup_set_class a_wceq f0_sbcreug f0_sbcreug f1_sbcreug i0_sbcreug a_wsb f2_sbcreug f4_sbcreug p_reubidv f0_sbcreug f2_sbcreug f4_sbcreug a_wreu f0_sbcreug f1_sbcreug i0_sbcreug a_wsb f2_sbcreug f4_sbcreug a_wreu f1_sbcreug i0_sbcreug p_sbie f0_sbcreug f2_sbcreug f4_sbcreug a_wreu f1_sbcreug i0_sbcreug a_wsb f0_sbcreug f1_sbcreug i0_sbcreug a_wsb f2_sbcreug f4_sbcreug a_wreu f0_sbcreug f2_sbcreug f4_sbcreug a_wreu f1_sbcreug f3_sbcreug a_wsbc f0_sbcreug f1_sbcreug f3_sbcreug a_wsbc f2_sbcreug f4_sbcreug a_wreu i0_sbcreug f3_sbcreug f5_sbcreug p_vtoclbg $.
$}

$(Interchange class substitution and class abstraction.  (Contributed by
       NM, 5-Nov-2005.) $)

${
	$v ph x y A B V  $.
	$d y w A  $.
	$d w B  $.
	$d w ph  $.
	$d x y  $.
	$d w x  $.
	f0_sbcabel $f wff ph $.
	f1_sbcabel $f set x $.
	f2_sbcabel $f set y $.
	f3_sbcabel $f class A $.
	f4_sbcabel $f class B $.
	f5_sbcabel $f class V $.
	i0_sbcabel $f set w $.
	e0_sbcabel $e |- F/_ x B $.
	p_sbcabel $p |- ( A e. V -> ( [. A / x ]. { y | ph } e. B <-> { y | [. A / x ]. ph } e. B ) ) $= f3_sbcabel f5_sbcabel p_elex i0_sbcabel a_sup_set_class f0_sbcabel f2_sbcabel a_cab a_wceq i0_sbcabel a_sup_set_class f4_sbcabel a_wcel a_wa i0_sbcabel f1_sbcabel f3_sbcabel a_cvv p_sbcexg i0_sbcabel a_sup_set_class f0_sbcabel f2_sbcabel a_cab a_wceq i0_sbcabel a_sup_set_class f4_sbcabel a_wcel f1_sbcabel f3_sbcabel a_cvv p_sbcang f0_sbcabel f2_sbcabel i0_sbcabel a_sup_set_class p_abeq2 i0_sbcabel a_sup_set_class f0_sbcabel f2_sbcabel a_cab a_wceq f2_sbcabel a_sup_set_class i0_sbcabel a_sup_set_class a_wcel f0_sbcabel a_wb f2_sbcabel a_wal f1_sbcabel f3_sbcabel p_sbcbii f2_sbcabel a_sup_set_class i0_sbcabel a_sup_set_class a_wcel f0_sbcabel a_wb f2_sbcabel f1_sbcabel f3_sbcabel a_cvv p_sbcalg f2_sbcabel a_sup_set_class i0_sbcabel a_sup_set_class a_wcel f0_sbcabel f1_sbcabel f3_sbcabel a_cvv p_sbcbig f2_sbcabel a_sup_set_class i0_sbcabel a_sup_set_class a_wcel f1_sbcabel f3_sbcabel a_cvv p_sbcg f3_sbcabel a_cvv a_wcel f2_sbcabel a_sup_set_class i0_sbcabel a_sup_set_class a_wcel f1_sbcabel f3_sbcabel a_wsbc f2_sbcabel a_sup_set_class i0_sbcabel a_sup_set_class a_wcel f0_sbcabel f1_sbcabel f3_sbcabel a_wsbc p_bibi1d f3_sbcabel a_cvv a_wcel f2_sbcabel a_sup_set_class i0_sbcabel a_sup_set_class a_wcel f0_sbcabel a_wb f1_sbcabel f3_sbcabel a_wsbc f2_sbcabel a_sup_set_class i0_sbcabel a_sup_set_class a_wcel f1_sbcabel f3_sbcabel a_wsbc f0_sbcabel f1_sbcabel f3_sbcabel a_wsbc a_wb f2_sbcabel a_sup_set_class i0_sbcabel a_sup_set_class a_wcel f0_sbcabel f1_sbcabel f3_sbcabel a_wsbc a_wb p_bitrd f3_sbcabel a_cvv a_wcel f2_sbcabel a_sup_set_class i0_sbcabel a_sup_set_class a_wcel f0_sbcabel a_wb f1_sbcabel f3_sbcabel a_wsbc f2_sbcabel a_sup_set_class i0_sbcabel a_sup_set_class a_wcel f0_sbcabel f1_sbcabel f3_sbcabel a_wsbc a_wb f2_sbcabel p_albidv f3_sbcabel a_cvv a_wcel f2_sbcabel a_sup_set_class i0_sbcabel a_sup_set_class a_wcel f0_sbcabel a_wb f2_sbcabel a_wal f1_sbcabel f3_sbcabel a_wsbc f2_sbcabel a_sup_set_class i0_sbcabel a_sup_set_class a_wcel f0_sbcabel a_wb f1_sbcabel f3_sbcabel a_wsbc f2_sbcabel a_wal f2_sbcabel a_sup_set_class i0_sbcabel a_sup_set_class a_wcel f0_sbcabel f1_sbcabel f3_sbcabel a_wsbc a_wb f2_sbcabel a_wal p_bitrd i0_sbcabel a_sup_set_class f0_sbcabel f2_sbcabel a_cab a_wceq f1_sbcabel f3_sbcabel a_wsbc f2_sbcabel a_sup_set_class i0_sbcabel a_sup_set_class a_wcel f0_sbcabel a_wb f2_sbcabel a_wal f1_sbcabel f3_sbcabel a_wsbc f3_sbcabel a_cvv a_wcel f2_sbcabel a_sup_set_class i0_sbcabel a_sup_set_class a_wcel f0_sbcabel f1_sbcabel f3_sbcabel a_wsbc a_wb f2_sbcabel a_wal p_syl5bb f0_sbcabel f1_sbcabel f3_sbcabel a_wsbc f2_sbcabel i0_sbcabel a_sup_set_class p_abeq2 f3_sbcabel a_cvv a_wcel i0_sbcabel a_sup_set_class f0_sbcabel f2_sbcabel a_cab a_wceq f1_sbcabel f3_sbcabel a_wsbc f2_sbcabel a_sup_set_class i0_sbcabel a_sup_set_class a_wcel f0_sbcabel f1_sbcabel f3_sbcabel a_wsbc a_wb f2_sbcabel a_wal i0_sbcabel a_sup_set_class f0_sbcabel f1_sbcabel f3_sbcabel a_wsbc f2_sbcabel a_cab a_wceq p_syl6bbr e0_sbcabel f1_sbcabel i0_sbcabel f4_sbcabel p_nfcri i0_sbcabel a_sup_set_class f4_sbcabel a_wcel f1_sbcabel f3_sbcabel a_cvv p_sbcgf f3_sbcabel a_cvv a_wcel i0_sbcabel a_sup_set_class f0_sbcabel f2_sbcabel a_cab a_wceq f1_sbcabel f3_sbcabel a_wsbc i0_sbcabel a_sup_set_class f0_sbcabel f1_sbcabel f3_sbcabel a_wsbc f2_sbcabel a_cab a_wceq i0_sbcabel a_sup_set_class f4_sbcabel a_wcel f1_sbcabel f3_sbcabel a_wsbc i0_sbcabel a_sup_set_class f4_sbcabel a_wcel p_anbi12d f3_sbcabel a_cvv a_wcel i0_sbcabel a_sup_set_class f0_sbcabel f2_sbcabel a_cab a_wceq i0_sbcabel a_sup_set_class f4_sbcabel a_wcel a_wa f1_sbcabel f3_sbcabel a_wsbc i0_sbcabel a_sup_set_class f0_sbcabel f2_sbcabel a_cab a_wceq f1_sbcabel f3_sbcabel a_wsbc i0_sbcabel a_sup_set_class f4_sbcabel a_wcel f1_sbcabel f3_sbcabel a_wsbc a_wa i0_sbcabel a_sup_set_class f0_sbcabel f1_sbcabel f3_sbcabel a_wsbc f2_sbcabel a_cab a_wceq i0_sbcabel a_sup_set_class f4_sbcabel a_wcel a_wa p_bitrd f3_sbcabel a_cvv a_wcel i0_sbcabel a_sup_set_class f0_sbcabel f2_sbcabel a_cab a_wceq i0_sbcabel a_sup_set_class f4_sbcabel a_wcel a_wa f1_sbcabel f3_sbcabel a_wsbc i0_sbcabel a_sup_set_class f0_sbcabel f1_sbcabel f3_sbcabel a_wsbc f2_sbcabel a_cab a_wceq i0_sbcabel a_sup_set_class f4_sbcabel a_wcel a_wa i0_sbcabel p_exbidv f3_sbcabel a_cvv a_wcel i0_sbcabel a_sup_set_class f0_sbcabel f2_sbcabel a_cab a_wceq i0_sbcabel a_sup_set_class f4_sbcabel a_wcel a_wa i0_sbcabel a_wex f1_sbcabel f3_sbcabel a_wsbc i0_sbcabel a_sup_set_class f0_sbcabel f2_sbcabel a_cab a_wceq i0_sbcabel a_sup_set_class f4_sbcabel a_wcel a_wa f1_sbcabel f3_sbcabel a_wsbc i0_sbcabel a_wex i0_sbcabel a_sup_set_class f0_sbcabel f1_sbcabel f3_sbcabel a_wsbc f2_sbcabel a_cab a_wceq i0_sbcabel a_sup_set_class f4_sbcabel a_wcel a_wa i0_sbcabel a_wex p_bitrd i0_sbcabel f0_sbcabel f2_sbcabel a_cab f4_sbcabel a_df-clel f0_sbcabel f2_sbcabel a_cab f4_sbcabel a_wcel i0_sbcabel a_sup_set_class f0_sbcabel f2_sbcabel a_cab a_wceq i0_sbcabel a_sup_set_class f4_sbcabel a_wcel a_wa i0_sbcabel a_wex f1_sbcabel f3_sbcabel p_sbcbii i0_sbcabel f0_sbcabel f1_sbcabel f3_sbcabel a_wsbc f2_sbcabel a_cab f4_sbcabel a_df-clel f3_sbcabel a_cvv a_wcel i0_sbcabel a_sup_set_class f0_sbcabel f2_sbcabel a_cab a_wceq i0_sbcabel a_sup_set_class f4_sbcabel a_wcel a_wa i0_sbcabel a_wex f1_sbcabel f3_sbcabel a_wsbc i0_sbcabel a_sup_set_class f0_sbcabel f1_sbcabel f3_sbcabel a_wsbc f2_sbcabel a_cab a_wceq i0_sbcabel a_sup_set_class f4_sbcabel a_wcel a_wa i0_sbcabel a_wex f0_sbcabel f2_sbcabel a_cab f4_sbcabel a_wcel f1_sbcabel f3_sbcabel a_wsbc f0_sbcabel f1_sbcabel f3_sbcabel a_wsbc f2_sbcabel a_cab f4_sbcabel a_wcel p_3bitr4g f3_sbcabel f5_sbcabel a_wcel f3_sbcabel a_cvv a_wcel f0_sbcabel f2_sbcabel a_cab f4_sbcabel a_wcel f1_sbcabel f3_sbcabel a_wsbc f0_sbcabel f1_sbcabel f3_sbcabel a_wsbc f2_sbcabel a_cab f4_sbcabel a_wcel a_wb p_syl $.
$}

$(Restricted quantifier version of Axiom 4 of [Mendelson] p. 69.  This
       provides an axiom for a predicate calculus for a restricted domain.
       This theorem generalizes the unrestricted ~ stdpc4 and ~ spsbc .  See
       also ~ rspsbca and ~ rspcsbela .  (Contributed by NM, 17-Nov-2006.)
       (Proof shortened by Mario Carneiro, 13-Oct-2016.) $)

${
	$v ph x A B  $.
	$d y A  $.
	$d x y B  $.
	$d y ph  $.
	f0_rspsbc $f wff ph $.
	f1_rspsbc $f set x $.
	f2_rspsbc $f class A $.
	f3_rspsbc $f class B $.
	i0_rspsbc $f set y $.
	p_rspsbc $p |- ( A e. B -> ( A. x e. B ph -> [. A / x ]. ph ) ) $= f0_rspsbc f1_rspsbc i0_rspsbc f3_rspsbc p_cbvralsv f0_rspsbc f1_rspsbc i0_rspsbc f2_rspsbc p_dfsbcq2 f0_rspsbc f1_rspsbc i0_rspsbc a_wsb f0_rspsbc f1_rspsbc f2_rspsbc a_wsbc i0_rspsbc f2_rspsbc f3_rspsbc p_rspcv f0_rspsbc f1_rspsbc f3_rspsbc a_wral f0_rspsbc f1_rspsbc i0_rspsbc a_wsb i0_rspsbc f3_rspsbc a_wral f2_rspsbc f3_rspsbc a_wcel f0_rspsbc f1_rspsbc f2_rspsbc a_wsbc p_syl5bi $.
$}

$(Restricted quantifier version of Axiom 4 of [Mendelson] p. 69.
       (Contributed by NM, 14-Dec-2005.) $)

${
	$v ph x A B  $.
	$d A  $.
	$d x B  $.
	$d ph  $.
	f0_rspsbca $f wff ph $.
	f1_rspsbca $f set x $.
	f2_rspsbca $f class A $.
	f3_rspsbca $f class B $.
	p_rspsbca $p |- ( ( A e. B /\ A. x e. B ph ) -> [. A / x ]. ph ) $= f0_rspsbca f1_rspsbca f2_rspsbca f3_rspsbca p_rspsbc f2_rspsbca f3_rspsbca a_wcel f0_rspsbca f1_rspsbca f3_rspsbca a_wral f0_rspsbca f1_rspsbca f2_rspsbca a_wsbc p_imp $.
$}

$(Existence form of ~ rspsbca .  (Contributed by NM, 29-Feb-2008.)  (Proof
       shortened by Mario Carneiro, 13-Oct-2016.) $)

${
	$v ph x A B  $.
	$d y A  $.
	$d x y B  $.
	$d y ph  $.
	f0_rspesbca $f wff ph $.
	f1_rspesbca $f set x $.
	f2_rspesbca $f class A $.
	f3_rspesbca $f class B $.
	i0_rspesbca $f set y $.
	p_rspesbca $p |- ( ( A e. B /\ [. A / x ]. ph ) -> E. x e. B ph ) $= f0_rspesbca f1_rspesbca i0_rspesbca f2_rspesbca p_dfsbcq2 f0_rspesbca f1_rspesbca i0_rspesbca a_wsb f0_rspesbca f1_rspesbca f2_rspesbca a_wsbc i0_rspesbca f2_rspesbca f3_rspesbca p_rspcev f0_rspesbca f1_rspesbca i0_rspesbca f3_rspesbca p_cbvrexsv f2_rspesbca f3_rspesbca a_wcel f0_rspesbca f1_rspesbca f2_rspesbca a_wsbc a_wa f0_rspesbca f1_rspesbca i0_rspesbca a_wsb i0_rspesbca f3_rspesbca a_wrex f0_rspesbca f1_rspesbca f3_rspesbca a_wrex p_sylibr $.
$}

$(Existence form of ~ spsbc .  (Contributed by Mario Carneiro,
       18-Nov-2016.) $)

${
	$v ph x A  $.
	$d A  $.
	$d x  $.
	$d ph  $.
	f0_spesbc $f wff ph $.
	f1_spesbc $f set x $.
	f2_spesbc $f class A $.
	p_spesbc $p |- ( [. A / x ]. ph -> E. x ph ) $= f0_spesbc f1_spesbc f2_spesbc p_sbcex f0_spesbc f1_spesbc f2_spesbc a_cvv p_rspesbca f2_spesbc a_cvv a_wcel f0_spesbc f1_spesbc f2_spesbc a_wsbc f0_spesbc f1_spesbc a_cvv a_wrex p_mpancom f0_spesbc f1_spesbc p_rexv f0_spesbc f1_spesbc f2_spesbc a_wsbc f0_spesbc f1_spesbc a_cvv a_wrex f0_spesbc f1_spesbc a_wex p_sylib $.
$}

$(form of ~ spsbc .  (Contributed by Mario Carneiro, 9-Feb-2017.) $)

${
	$v ph ps x A  $.
	$d A  $.
	$d x  $.
	$d ph  $.
	f0_spesbcd $f wff ph $.
	f1_spesbcd $f wff ps $.
	f2_spesbcd $f set x $.
	f3_spesbcd $f class A $.
	e0_spesbcd $e |- ( ph -> [. A / x ]. ps ) $.
	p_spesbcd $p |- ( ph -> E. x ps ) $= e0_spesbcd f1_spesbcd f2_spesbcd f3_spesbcd p_spesbc f0_spesbcd f1_spesbcd f2_spesbcd f3_spesbcd a_wsbc f1_spesbcd f2_spesbcd a_wex p_syl $.
$}

$(A substitution into a theorem.  (Contributed by NM, 1-Mar-2008.)  (Proof
       shortened by Mario Carneiro, 13-Oct-2016.) $)

${
	$v ph x A B  $.
	$d x B  $.
	f0_sbcth2 $f wff ph $.
	f1_sbcth2 $f set x $.
	f2_sbcth2 $f class A $.
	f3_sbcth2 $f class B $.
	e0_sbcth2 $e |- ( x e. B -> ph ) $.
	p_sbcth2 $p |- ( A e. B -> [. A / x ]. ph ) $= e0_sbcth2 f0_sbcth2 f1_sbcth2 f3_sbcth2 p_rgen f0_sbcth2 f1_sbcth2 f2_sbcth2 f3_sbcth2 p_rspsbc f2_sbcth2 f3_sbcth2 a_wcel f0_sbcth2 f1_sbcth2 f3_sbcth2 a_wral f0_sbcth2 f1_sbcth2 f2_sbcth2 a_wsbc p_mpi $.
$}

$(Restricted quantifier version of Axiom 5 of [Mendelson] p. 69.  This is
       an axiom of a predicate calculus for a restricted domain.  Compare the
       unrestricted ~ stdpc5 .  (Contributed by NM, 16-Jan-2004.) $)

${
	$v ph ps x A  $.
	f0_ra5 $f wff ph $.
	f1_ra5 $f wff ps $.
	f2_ra5 $f set x $.
	f3_ra5 $f class A $.
	e0_ra5 $e |- F/ x ph $.
	p_ra5 $p |- ( A. x e. A ( ph -> ps ) -> ( ph -> A. x e. A ps ) ) $= f0_ra5 f1_ra5 a_wi f2_ra5 f3_ra5 a_df-ral f2_ra5 a_sup_set_class f3_ra5 a_wcel f0_ra5 f1_ra5 p_bi2.04 f2_ra5 a_sup_set_class f3_ra5 a_wcel f0_ra5 f1_ra5 a_wi a_wi f0_ra5 f2_ra5 a_sup_set_class f3_ra5 a_wcel f1_ra5 a_wi a_wi f2_ra5 p_albii f0_ra5 f1_ra5 a_wi f2_ra5 f3_ra5 a_wral f2_ra5 a_sup_set_class f3_ra5 a_wcel f0_ra5 f1_ra5 a_wi a_wi f2_ra5 a_wal f0_ra5 f2_ra5 a_sup_set_class f3_ra5 a_wcel f1_ra5 a_wi a_wi f2_ra5 a_wal p_bitri e0_ra5 f0_ra5 f2_ra5 a_sup_set_class f3_ra5 a_wcel f1_ra5 a_wi f2_ra5 p_stdpc5 f0_ra5 f1_ra5 a_wi f2_ra5 f3_ra5 a_wral f0_ra5 f2_ra5 a_sup_set_class f3_ra5 a_wcel f1_ra5 a_wi a_wi f2_ra5 a_wal f0_ra5 f2_ra5 a_sup_set_class f3_ra5 a_wcel f1_ra5 a_wi f2_ra5 a_wal a_wi p_sylbi f1_ra5 f2_ra5 f3_ra5 a_df-ral f0_ra5 f1_ra5 a_wi f2_ra5 f3_ra5 a_wral f0_ra5 f2_ra5 a_sup_set_class f3_ra5 a_wcel f1_ra5 a_wi f2_ra5 a_wal f1_ra5 f2_ra5 f3_ra5 a_wral p_syl6ibr $.
$}

$(Alternate definition of restricted "at most one."  Note that
       ` E* x e. A ph ` is not equivalent to
       ` E. y e. A A. x e. A ( ph -> x = y ) ` (in analogy to ~ reu6 ); to see
       this, let ` A ` be the empty set.  However, one direction of this
       pattern holds; see ~ rmo2i .  (Contributed by NM, 17-Jun-2017.) $)

${
	$v ph x y A  $.
	$d x y A  $.
	f0_rmo2 $f wff ph $.
	f1_rmo2 $f set x $.
	f2_rmo2 $f set y $.
	f3_rmo2 $f class A $.
	e0_rmo2 $e |- F/ y ph $.
	p_rmo2 $p |- ( E* x e. A ph <-> E. y A. x e. A ( ph -> x = y ) ) $= f0_rmo2 f1_rmo2 f3_rmo2 a_df-rmo f1_rmo2 a_sup_set_class f3_rmo2 a_wcel f2_rmo2 p_nfv e0_rmo2 f1_rmo2 a_sup_set_class f3_rmo2 a_wcel f0_rmo2 f2_rmo2 p_nfan f1_rmo2 a_sup_set_class f3_rmo2 a_wcel f0_rmo2 a_wa f1_rmo2 f2_rmo2 p_mo2 f1_rmo2 a_sup_set_class f3_rmo2 a_wcel f0_rmo2 f1_rmo2 a_sup_set_class f2_rmo2 a_sup_set_class a_wceq p_impexp f1_rmo2 a_sup_set_class f3_rmo2 a_wcel f0_rmo2 a_wa f1_rmo2 a_sup_set_class f2_rmo2 a_sup_set_class a_wceq a_wi f1_rmo2 a_sup_set_class f3_rmo2 a_wcel f0_rmo2 f1_rmo2 a_sup_set_class f2_rmo2 a_sup_set_class a_wceq a_wi a_wi f1_rmo2 p_albii f0_rmo2 f1_rmo2 a_sup_set_class f2_rmo2 a_sup_set_class a_wceq a_wi f1_rmo2 f3_rmo2 a_df-ral f1_rmo2 a_sup_set_class f3_rmo2 a_wcel f0_rmo2 a_wa f1_rmo2 a_sup_set_class f2_rmo2 a_sup_set_class a_wceq a_wi f1_rmo2 a_wal f1_rmo2 a_sup_set_class f3_rmo2 a_wcel f0_rmo2 f1_rmo2 a_sup_set_class f2_rmo2 a_sup_set_class a_wceq a_wi a_wi f1_rmo2 a_wal f0_rmo2 f1_rmo2 a_sup_set_class f2_rmo2 a_sup_set_class a_wceq a_wi f1_rmo2 f3_rmo2 a_wral p_bitr4i f1_rmo2 a_sup_set_class f3_rmo2 a_wcel f0_rmo2 a_wa f1_rmo2 a_sup_set_class f2_rmo2 a_sup_set_class a_wceq a_wi f1_rmo2 a_wal f0_rmo2 f1_rmo2 a_sup_set_class f2_rmo2 a_sup_set_class a_wceq a_wi f1_rmo2 f3_rmo2 a_wral f2_rmo2 p_exbii f0_rmo2 f1_rmo2 f3_rmo2 a_wrmo f1_rmo2 a_sup_set_class f3_rmo2 a_wcel f0_rmo2 a_wa f1_rmo2 a_wmo f1_rmo2 a_sup_set_class f3_rmo2 a_wcel f0_rmo2 a_wa f1_rmo2 a_sup_set_class f2_rmo2 a_sup_set_class a_wceq a_wi f1_rmo2 a_wal f2_rmo2 a_wex f0_rmo2 f1_rmo2 a_sup_set_class f2_rmo2 a_sup_set_class a_wceq a_wi f1_rmo2 f3_rmo2 a_wral f2_rmo2 a_wex p_3bitri $.
$}

$(Condition implying restricted "at most one."  (Contributed by NM,
       17-Jun-2017.) $)

${
	$v ph x y A  $.
	$d x y A  $.
	f0_rmo2i $f wff ph $.
	f1_rmo2i $f set x $.
	f2_rmo2i $f set y $.
	f3_rmo2i $f class A $.
	e0_rmo2i $e |- F/ y ph $.
	p_rmo2i $p |- ( E. y e. A A. x e. A ( ph -> x = y ) -> E* x e. A ph ) $= f0_rmo2i f1_rmo2i a_sup_set_class f2_rmo2i a_sup_set_class a_wceq a_wi f1_rmo2i f3_rmo2i a_wral f2_rmo2i f3_rmo2i p_rexex e0_rmo2i f0_rmo2i f1_rmo2i f2_rmo2i f3_rmo2i p_rmo2 f0_rmo2i f1_rmo2i a_sup_set_class f2_rmo2i a_sup_set_class a_wceq a_wi f1_rmo2i f3_rmo2i a_wral f2_rmo2i f3_rmo2i a_wrex f0_rmo2i f1_rmo2i a_sup_set_class f2_rmo2i a_sup_set_class a_wceq a_wi f1_rmo2i f3_rmo2i a_wral f2_rmo2i a_wex f0_rmo2i f1_rmo2i f3_rmo2i a_wrmo p_sylibr $.
$}

$(Restricted "at most one" using explicit substitution.  (Contributed by
       NM, 4-Nov-2012.)  (Revised by NM, 16-Jun-2017.) $)

${
	$v ph x y A  $.
	$d x y A  $.
	f0_rmo3 $f wff ph $.
	f1_rmo3 $f set x $.
	f2_rmo3 $f set y $.
	f3_rmo3 $f class A $.
	e0_rmo3 $e |- F/ y ph $.
	p_rmo3 $p |- ( E* x e. A ph <-> A. x e. A A. y e. A ( ( ph /\ [ y / x ] ph ) -> x = y ) ) $= f0_rmo3 f1_rmo3 f3_rmo3 a_df-rmo f1_rmo3 a_sup_set_class f3_rmo3 a_wcel f0_rmo3 f1_rmo3 f2_rmo3 p_sban f2_rmo3 f1_rmo3 f3_rmo3 p_clelsb3 f1_rmo3 a_sup_set_class f3_rmo3 a_wcel f1_rmo3 f2_rmo3 a_wsb f2_rmo3 a_sup_set_class f3_rmo3 a_wcel f0_rmo3 f1_rmo3 f2_rmo3 a_wsb p_anbi1i f1_rmo3 a_sup_set_class f3_rmo3 a_wcel f0_rmo3 a_wa f1_rmo3 f2_rmo3 a_wsb f1_rmo3 a_sup_set_class f3_rmo3 a_wcel f1_rmo3 f2_rmo3 a_wsb f0_rmo3 f1_rmo3 f2_rmo3 a_wsb a_wa f2_rmo3 a_sup_set_class f3_rmo3 a_wcel f0_rmo3 f1_rmo3 f2_rmo3 a_wsb a_wa p_bitri f1_rmo3 a_sup_set_class f3_rmo3 a_wcel f0_rmo3 a_wa f1_rmo3 f2_rmo3 a_wsb f2_rmo3 a_sup_set_class f3_rmo3 a_wcel f0_rmo3 f1_rmo3 f2_rmo3 a_wsb a_wa f1_rmo3 a_sup_set_class f3_rmo3 a_wcel f0_rmo3 a_wa p_anbi2i f1_rmo3 a_sup_set_class f3_rmo3 a_wcel f0_rmo3 f2_rmo3 a_sup_set_class f3_rmo3 a_wcel f0_rmo3 f1_rmo3 f2_rmo3 a_wsb p_an4 f1_rmo3 a_sup_set_class f3_rmo3 a_wcel f2_rmo3 a_sup_set_class f3_rmo3 a_wcel p_ancom f1_rmo3 a_sup_set_class f3_rmo3 a_wcel f2_rmo3 a_sup_set_class f3_rmo3 a_wcel a_wa f2_rmo3 a_sup_set_class f3_rmo3 a_wcel f1_rmo3 a_sup_set_class f3_rmo3 a_wcel a_wa f0_rmo3 f0_rmo3 f1_rmo3 f2_rmo3 a_wsb a_wa p_anbi1i f1_rmo3 a_sup_set_class f3_rmo3 a_wcel f0_rmo3 a_wa f1_rmo3 a_sup_set_class f3_rmo3 a_wcel f0_rmo3 a_wa f1_rmo3 f2_rmo3 a_wsb a_wa f1_rmo3 a_sup_set_class f3_rmo3 a_wcel f0_rmo3 a_wa f2_rmo3 a_sup_set_class f3_rmo3 a_wcel f0_rmo3 f1_rmo3 f2_rmo3 a_wsb a_wa a_wa f1_rmo3 a_sup_set_class f3_rmo3 a_wcel f2_rmo3 a_sup_set_class f3_rmo3 a_wcel a_wa f0_rmo3 f0_rmo3 f1_rmo3 f2_rmo3 a_wsb a_wa a_wa f2_rmo3 a_sup_set_class f3_rmo3 a_wcel f1_rmo3 a_sup_set_class f3_rmo3 a_wcel a_wa f0_rmo3 f0_rmo3 f1_rmo3 f2_rmo3 a_wsb a_wa a_wa p_3bitri f1_rmo3 a_sup_set_class f3_rmo3 a_wcel f0_rmo3 a_wa f1_rmo3 a_sup_set_class f3_rmo3 a_wcel f0_rmo3 a_wa f1_rmo3 f2_rmo3 a_wsb a_wa f2_rmo3 a_sup_set_class f3_rmo3 a_wcel f1_rmo3 a_sup_set_class f3_rmo3 a_wcel a_wa f0_rmo3 f0_rmo3 f1_rmo3 f2_rmo3 a_wsb a_wa a_wa f1_rmo3 a_sup_set_class f2_rmo3 a_sup_set_class a_wceq p_imbi1i f2_rmo3 a_sup_set_class f3_rmo3 a_wcel f1_rmo3 a_sup_set_class f3_rmo3 a_wcel a_wa f0_rmo3 f0_rmo3 f1_rmo3 f2_rmo3 a_wsb a_wa f1_rmo3 a_sup_set_class f2_rmo3 a_sup_set_class a_wceq p_impexp f2_rmo3 a_sup_set_class f3_rmo3 a_wcel f1_rmo3 a_sup_set_class f3_rmo3 a_wcel f0_rmo3 f0_rmo3 f1_rmo3 f2_rmo3 a_wsb a_wa f1_rmo3 a_sup_set_class f2_rmo3 a_sup_set_class a_wceq a_wi p_impexp f1_rmo3 a_sup_set_class f3_rmo3 a_wcel f0_rmo3 a_wa f1_rmo3 a_sup_set_class f3_rmo3 a_wcel f0_rmo3 a_wa f1_rmo3 f2_rmo3 a_wsb a_wa f1_rmo3 a_sup_set_class f2_rmo3 a_sup_set_class a_wceq a_wi f2_rmo3 a_sup_set_class f3_rmo3 a_wcel f1_rmo3 a_sup_set_class f3_rmo3 a_wcel a_wa f0_rmo3 f0_rmo3 f1_rmo3 f2_rmo3 a_wsb a_wa a_wa f1_rmo3 a_sup_set_class f2_rmo3 a_sup_set_class a_wceq a_wi f2_rmo3 a_sup_set_class f3_rmo3 a_wcel f1_rmo3 a_sup_set_class f3_rmo3 a_wcel a_wa f0_rmo3 f0_rmo3 f1_rmo3 f2_rmo3 a_wsb a_wa f1_rmo3 a_sup_set_class f2_rmo3 a_sup_set_class a_wceq a_wi a_wi f2_rmo3 a_sup_set_class f3_rmo3 a_wcel f1_rmo3 a_sup_set_class f3_rmo3 a_wcel f0_rmo3 f0_rmo3 f1_rmo3 f2_rmo3 a_wsb a_wa f1_rmo3 a_sup_set_class f2_rmo3 a_sup_set_class a_wceq a_wi a_wi a_wi p_3bitri f1_rmo3 a_sup_set_class f3_rmo3 a_wcel f0_rmo3 a_wa f1_rmo3 a_sup_set_class f3_rmo3 a_wcel f0_rmo3 a_wa f1_rmo3 f2_rmo3 a_wsb a_wa f1_rmo3 a_sup_set_class f2_rmo3 a_sup_set_class a_wceq a_wi f2_rmo3 a_sup_set_class f3_rmo3 a_wcel f1_rmo3 a_sup_set_class f3_rmo3 a_wcel f0_rmo3 f0_rmo3 f1_rmo3 f2_rmo3 a_wsb a_wa f1_rmo3 a_sup_set_class f2_rmo3 a_sup_set_class a_wceq a_wi a_wi a_wi f2_rmo3 p_albii f1_rmo3 a_sup_set_class f3_rmo3 a_wcel f0_rmo3 f0_rmo3 f1_rmo3 f2_rmo3 a_wsb a_wa f1_rmo3 a_sup_set_class f2_rmo3 a_sup_set_class a_wceq a_wi a_wi f2_rmo3 f3_rmo3 a_df-ral f1_rmo3 a_sup_set_class f3_rmo3 a_wcel f0_rmo3 f0_rmo3 f1_rmo3 f2_rmo3 a_wsb a_wa f1_rmo3 a_sup_set_class f2_rmo3 a_sup_set_class a_wceq a_wi f2_rmo3 f3_rmo3 p_r19.21v f1_rmo3 a_sup_set_class f3_rmo3 a_wcel f0_rmo3 a_wa f1_rmo3 a_sup_set_class f3_rmo3 a_wcel f0_rmo3 a_wa f1_rmo3 f2_rmo3 a_wsb a_wa f1_rmo3 a_sup_set_class f2_rmo3 a_sup_set_class a_wceq a_wi f2_rmo3 a_wal f2_rmo3 a_sup_set_class f3_rmo3 a_wcel f1_rmo3 a_sup_set_class f3_rmo3 a_wcel f0_rmo3 f0_rmo3 f1_rmo3 f2_rmo3 a_wsb a_wa f1_rmo3 a_sup_set_class f2_rmo3 a_sup_set_class a_wceq a_wi a_wi a_wi f2_rmo3 a_wal f1_rmo3 a_sup_set_class f3_rmo3 a_wcel f0_rmo3 f0_rmo3 f1_rmo3 f2_rmo3 a_wsb a_wa f1_rmo3 a_sup_set_class f2_rmo3 a_sup_set_class a_wceq a_wi a_wi f2_rmo3 f3_rmo3 a_wral f1_rmo3 a_sup_set_class f3_rmo3 a_wcel f0_rmo3 f0_rmo3 f1_rmo3 f2_rmo3 a_wsb a_wa f1_rmo3 a_sup_set_class f2_rmo3 a_sup_set_class a_wceq a_wi f2_rmo3 f3_rmo3 a_wral a_wi p_3bitr2i f1_rmo3 a_sup_set_class f3_rmo3 a_wcel f0_rmo3 a_wa f1_rmo3 a_sup_set_class f3_rmo3 a_wcel f0_rmo3 a_wa f1_rmo3 f2_rmo3 a_wsb a_wa f1_rmo3 a_sup_set_class f2_rmo3 a_sup_set_class a_wceq a_wi f2_rmo3 a_wal f1_rmo3 a_sup_set_class f3_rmo3 a_wcel f0_rmo3 f0_rmo3 f1_rmo3 f2_rmo3 a_wsb a_wa f1_rmo3 a_sup_set_class f2_rmo3 a_sup_set_class a_wceq a_wi f2_rmo3 f3_rmo3 a_wral a_wi f1_rmo3 p_albii f1_rmo3 a_sup_set_class f3_rmo3 a_wcel f2_rmo3 p_nfv e0_rmo3 f1_rmo3 a_sup_set_class f3_rmo3 a_wcel f0_rmo3 f2_rmo3 p_nfan f1_rmo3 a_sup_set_class f3_rmo3 a_wcel f0_rmo3 a_wa f1_rmo3 f2_rmo3 p_mo3 f0_rmo3 f0_rmo3 f1_rmo3 f2_rmo3 a_wsb a_wa f1_rmo3 a_sup_set_class f2_rmo3 a_sup_set_class a_wceq a_wi f2_rmo3 f3_rmo3 a_wral f1_rmo3 f3_rmo3 a_df-ral f1_rmo3 a_sup_set_class f3_rmo3 a_wcel f0_rmo3 a_wa f1_rmo3 a_sup_set_class f3_rmo3 a_wcel f0_rmo3 a_wa f1_rmo3 f2_rmo3 a_wsb a_wa f1_rmo3 a_sup_set_class f2_rmo3 a_sup_set_class a_wceq a_wi f2_rmo3 a_wal f1_rmo3 a_wal f1_rmo3 a_sup_set_class f3_rmo3 a_wcel f0_rmo3 f0_rmo3 f1_rmo3 f2_rmo3 a_wsb a_wa f1_rmo3 a_sup_set_class f2_rmo3 a_sup_set_class a_wceq a_wi f2_rmo3 f3_rmo3 a_wral a_wi f1_rmo3 a_wal f1_rmo3 a_sup_set_class f3_rmo3 a_wcel f0_rmo3 a_wa f1_rmo3 a_wmo f0_rmo3 f0_rmo3 f1_rmo3 f2_rmo3 a_wsb a_wa f1_rmo3 a_sup_set_class f2_rmo3 a_sup_set_class a_wceq a_wi f2_rmo3 f3_rmo3 a_wral f1_rmo3 f3_rmo3 a_wral p_3bitr4i f0_rmo3 f1_rmo3 f3_rmo3 a_wrmo f1_rmo3 a_sup_set_class f3_rmo3 a_wcel f0_rmo3 a_wa f1_rmo3 a_wmo f0_rmo3 f0_rmo3 f1_rmo3 f2_rmo3 a_wsb a_wa f1_rmo3 a_sup_set_class f2_rmo3 a_sup_set_class a_wceq a_wi f2_rmo3 f3_rmo3 a_wral f1_rmo3 f3_rmo3 a_wral p_bitri $.
$}

$(Consequence of "at most one", using implicit substitution.  (Contributed
       by NM, 2-Jan-2015.)  (Revised by NM, 16-Jun-2017.) $)

${
	$v ph ps ch x A B C  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	$d ph  $.
	$d x ps  $.
	$d x ch  $.
	f0_rmob $f wff ph $.
	f1_rmob $f wff ps $.
	f2_rmob $f wff ch $.
	f3_rmob $f set x $.
	f4_rmob $f class A $.
	f5_rmob $f class B $.
	f6_rmob $f class C $.
	e0_rmob $e |- ( x = B -> ( ph <-> ps ) ) $.
	e1_rmob $e |- ( x = C -> ( ph <-> ch ) ) $.
	p_rmob $p |- ( ( E* x e. A ph /\ ( B e. A /\ ps ) ) -> ( B = C <-> ( C e. A /\ ch ) ) ) $= f0_rmob f3_rmob f4_rmob a_df-rmo f3_rmob a_sup_set_class f4_rmob a_wcel f0_rmob a_wa f3_rmob a_wmo f5_rmob f4_rmob a_wcel f1_rmob p_simprl f5_rmob f6_rmob f4_rmob p_eleq1 f3_rmob a_sup_set_class f4_rmob a_wcel f0_rmob a_wa f3_rmob a_wmo f5_rmob f4_rmob a_wcel f1_rmob a_wa a_wa f5_rmob f4_rmob a_wcel f5_rmob f6_rmob a_wceq f6_rmob f4_rmob a_wcel p_syl5ibcom f6_rmob f4_rmob a_wcel f2_rmob p_simpl f6_rmob f4_rmob a_wcel f2_rmob a_wa f6_rmob f4_rmob a_wcel a_wi f3_rmob a_sup_set_class f4_rmob a_wcel f0_rmob a_wa f3_rmob a_wmo f5_rmob f4_rmob a_wcel f1_rmob a_wa a_wa p_a1i f3_rmob a_sup_set_class f4_rmob a_wcel f0_rmob a_wa f3_rmob a_wmo f5_rmob f4_rmob a_wcel f1_rmob f6_rmob f4_rmob a_wcel p_simplrl f3_rmob a_sup_set_class f4_rmob a_wcel f0_rmob a_wa f3_rmob a_wmo f5_rmob f4_rmob a_wcel f1_rmob a_wa a_wa f6_rmob f4_rmob a_wcel p_simpr f3_rmob a_sup_set_class f4_rmob a_wcel f0_rmob a_wa f3_rmob a_wmo f5_rmob f4_rmob a_wcel f1_rmob a_wa f6_rmob f4_rmob a_wcel p_simpll f3_rmob a_sup_set_class f4_rmob a_wcel f0_rmob a_wa f3_rmob a_wmo f5_rmob f4_rmob a_wcel f1_rmob f6_rmob f4_rmob a_wcel p_simplrl f3_rmob a_sup_set_class f4_rmob a_wcel f0_rmob a_wa f3_rmob a_wmo f5_rmob f4_rmob a_wcel f1_rmob f6_rmob f4_rmob a_wcel p_simplrr f3_rmob a_sup_set_class f5_rmob f4_rmob p_eleq1 e0_rmob f3_rmob a_sup_set_class f5_rmob a_wceq f3_rmob a_sup_set_class f4_rmob a_wcel f5_rmob f4_rmob a_wcel f0_rmob f1_rmob p_anbi12d f3_rmob a_sup_set_class f6_rmob f4_rmob p_eleq1 e1_rmob f3_rmob a_sup_set_class f6_rmob a_wceq f3_rmob a_sup_set_class f4_rmob a_wcel f6_rmob f4_rmob a_wcel f0_rmob f2_rmob p_anbi12d f3_rmob a_sup_set_class f4_rmob a_wcel f0_rmob a_wa f5_rmob f4_rmob a_wcel f1_rmob a_wa f6_rmob f4_rmob a_wcel f2_rmob a_wa f3_rmob f5_rmob f6_rmob f4_rmob f4_rmob p_mob f3_rmob a_sup_set_class f4_rmob a_wcel f0_rmob a_wa f3_rmob a_wmo f5_rmob f4_rmob a_wcel f1_rmob a_wa a_wa f6_rmob f4_rmob a_wcel a_wa f5_rmob f4_rmob a_wcel f6_rmob f4_rmob a_wcel f3_rmob a_sup_set_class f4_rmob a_wcel f0_rmob a_wa f3_rmob a_wmo f5_rmob f4_rmob a_wcel f1_rmob f5_rmob f6_rmob a_wceq f6_rmob f4_rmob a_wcel f2_rmob a_wa a_wb p_syl212anc f3_rmob a_sup_set_class f4_rmob a_wcel f0_rmob a_wa f3_rmob a_wmo f5_rmob f4_rmob a_wcel f1_rmob a_wa a_wa f6_rmob f4_rmob a_wcel f5_rmob f6_rmob a_wceq f6_rmob f4_rmob a_wcel f2_rmob a_wa a_wb p_ex f3_rmob a_sup_set_class f4_rmob a_wcel f0_rmob a_wa f3_rmob a_wmo f5_rmob f4_rmob a_wcel f1_rmob a_wa a_wa f6_rmob f4_rmob a_wcel f5_rmob f6_rmob a_wceq f6_rmob f4_rmob a_wcel f2_rmob a_wa p_pm5.21ndd f0_rmob f3_rmob f4_rmob a_wrmo f3_rmob a_sup_set_class f4_rmob a_wcel f0_rmob a_wa f3_rmob a_wmo f5_rmob f4_rmob a_wcel f1_rmob a_wa f5_rmob f6_rmob a_wceq f6_rmob f4_rmob a_wcel f2_rmob a_wa a_wb p_sylanb $.
$}

$(Consequence of "at most one", using implicit substitution.  (Contributed
       by NM, 4-Nov-2012.)  (Revised by NM, 16-Jun-2017.) $)

${
	$v ph ps ch x A B C  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	$d ph  $.
	$d x ps  $.
	$d x ch  $.
	f0_rmoi $f wff ph $.
	f1_rmoi $f wff ps $.
	f2_rmoi $f wff ch $.
	f3_rmoi $f set x $.
	f4_rmoi $f class A $.
	f5_rmoi $f class B $.
	f6_rmoi $f class C $.
	e0_rmoi $e |- ( x = B -> ( ph <-> ps ) ) $.
	e1_rmoi $e |- ( x = C -> ( ph <-> ch ) ) $.
	p_rmoi $p |- ( ( E* x e. A ph /\ ( B e. A /\ ps ) /\ ( C e. A /\ ch ) ) -> B = C ) $= e0_rmoi e1_rmoi f0_rmoi f1_rmoi f2_rmoi f3_rmoi f4_rmoi f5_rmoi f6_rmoi p_rmob f0_rmoi f3_rmoi f4_rmoi a_wrmo f5_rmoi f4_rmoi a_wcel f1_rmoi a_wa f5_rmoi f6_rmoi a_wceq f6_rmoi f4_rmoi a_wcel f2_rmoi a_wa p_biimp3ar $.
$}


