$[ turnstile_special_source.mm $]

$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/Restricted_quantification.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        The universal class

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(Declare the symbol for the universal class. $)

$c _V $.

$(Letter V (for the universal class) $)

$(Extend class notation to include the universal class symbol. $)

${
	$v  $.
	a_cvv $a class _V $.
$}

$(Soundness justification theorem for ~ df-v .  (Contributed by Rodolfo
       Medina, 27-Apr-2010.) $)

${
	$v x y  $.
	$d z x  $.
	$d z y  $.
	f0_vjust $f set x $.
	f1_vjust $f set y $.
	i0_vjust $f set z $.
	p_vjust $p |- { x | x = x } = { y | y = y } $= f0_vjust p_equid f0_vjust a_sup_set_class f0_vjust a_sup_set_class a_wceq f0_vjust i0_vjust p_sbt f1_vjust p_equid f1_vjust a_sup_set_class f1_vjust a_sup_set_class a_wceq f1_vjust i0_vjust p_sbt f0_vjust a_sup_set_class f0_vjust a_sup_set_class a_wceq f0_vjust i0_vjust a_wsb f1_vjust a_sup_set_class f1_vjust a_sup_set_class a_wceq f1_vjust i0_vjust a_wsb p_2th f0_vjust a_sup_set_class f0_vjust a_sup_set_class a_wceq i0_vjust f0_vjust a_df-clab f1_vjust a_sup_set_class f1_vjust a_sup_set_class a_wceq i0_vjust f1_vjust a_df-clab f0_vjust a_sup_set_class f0_vjust a_sup_set_class a_wceq f0_vjust i0_vjust a_wsb f1_vjust a_sup_set_class f1_vjust a_sup_set_class a_wceq f1_vjust i0_vjust a_wsb i0_vjust a_sup_set_class f0_vjust a_sup_set_class f0_vjust a_sup_set_class a_wceq f0_vjust a_cab a_wcel i0_vjust a_sup_set_class f1_vjust a_sup_set_class f1_vjust a_sup_set_class a_wceq f1_vjust a_cab a_wcel p_3bitr4i i0_vjust f0_vjust a_sup_set_class f0_vjust a_sup_set_class a_wceq f0_vjust a_cab f1_vjust a_sup_set_class f1_vjust a_sup_set_class a_wceq f1_vjust a_cab p_eqriv $.
$}

$(Define the universal class.  Definition 5.20 of [TakeutiZaring] p. 21.
     Also Definition 2.9 of [Quine] p. 19.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v x  $.
	f0_df-v $f set x $.
	a_df-v $a |- _V = { x | x = x } $.
$}

$(All set variables are sets (see ~ isset ).  Theorem 6.8 of [Quine] p. 43.
     (Contributed by NM, 5-Aug-1993.) $)

${
	$v x  $.
	f0_vex $f set x $.
	p_vex $p |- x e. _V $= f0_vex a_sup_set_class p_eqid f0_vex a_df-v f0_vex a_sup_set_class f0_vex a_sup_set_class a_wceq f0_vex a_cvv p_abeq2i f0_vex a_sup_set_class a_cvv a_wcel f0_vex a_sup_set_class f0_vex a_sup_set_class a_wceq p_mpbir $.
$}

$(Two ways to say " ` A ` is a set":  A class ` A ` is a member of the
       universal class ` _V ` (see ~ df-v ) if and only if the class ` A `
       exists (i.e. there exists some set ` x ` equal to class ` A ` ).
       Theorem 6.9 of [Quine] p. 43. _Notational convention_:  We will use the
       notational device " ` A e. _V ` " to mean " ` A ` is a set" very
       frequently, for example in ~ uniex .  Note the when ` A ` is not a set,
       it is called a proper class.  In some theorems, such as ~ uniexg , in
       order to shorten certain proofs we use the more general antecedent
       ` A e. V ` instead of ` A e. _V ` to mean " ` A ` is a set."

       Note that a constant is implicitly considered distinct from all
       variables.  This is why ` _V ` is not included in the distinct variable
       list, even though ~ df-clel requires that the expression substituted for
       ` B ` not contain ` x ` .  (Also, the Metamath spec does not allow
       constants in the distinct variable list.)  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v x A  $.
	$d x A  $.
	f0_isset $f set x $.
	f1_isset $f class A $.
	p_isset $p |- ( A e. _V <-> E. x x = A ) $= f0_isset f1_isset a_cvv a_df-clel f0_isset p_vex f0_isset a_sup_set_class a_cvv a_wcel f0_isset a_sup_set_class f1_isset a_wceq p_biantru f0_isset a_sup_set_class f1_isset a_wceq f0_isset a_sup_set_class f1_isset a_wceq f0_isset a_sup_set_class a_cvv a_wcel a_wa f0_isset p_exbii f1_isset a_cvv a_wcel f0_isset a_sup_set_class f1_isset a_wceq f0_isset a_sup_set_class a_cvv a_wcel a_wa f0_isset a_wex f0_isset a_sup_set_class f1_isset a_wceq f0_isset a_wex p_bitr4i $.
$}

$(A version of isset that does not require x and A to be distinct.
       (Contributed by Andrew Salmon, 6-Jun-2011.)  (Revised by Mario Carneiro,
       10-Oct-2016.) $)

${
	$v x A  $.
	$d A y  $.
	$d x y  $.
	f0_issetf $f set x $.
	f1_issetf $f class A $.
	i0_issetf $f set y $.
	e0_issetf $e |- F/_ x A $.
	p_issetf $p |- ( A e. _V <-> E. x x = A ) $= i0_issetf f1_issetf p_isset e0_issetf f0_issetf i0_issetf a_sup_set_class f1_issetf p_nfeq2 f0_issetf a_sup_set_class f1_issetf a_wceq i0_issetf p_nfv i0_issetf a_sup_set_class f0_issetf a_sup_set_class f1_issetf p_eqeq1 i0_issetf a_sup_set_class f1_issetf a_wceq f0_issetf a_sup_set_class f1_issetf a_wceq i0_issetf f0_issetf p_cbvex f1_issetf a_cvv a_wcel i0_issetf a_sup_set_class f1_issetf a_wceq i0_issetf a_wex f0_issetf a_sup_set_class f1_issetf a_wceq f0_issetf a_wex p_bitri $.
$}

$(A way to say " ` A ` is a set" (inference rule).  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v x A  $.
	$d x A  $.
	f0_isseti $f set x $.
	f1_isseti $f class A $.
	e0_isseti $e |- A e. _V $.
	p_isseti $p |- E. x x = A $= e0_isseti f0_isseti f1_isseti p_isset f1_isseti a_cvv a_wcel f0_isseti a_sup_set_class f1_isseti a_wceq f0_isseti a_wex p_mpbi $.
$}

$(A way to say " ` A ` is a set" (inference rule).  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v x A  $.
	$d x A  $.
	f0_issetri $f set x $.
	f1_issetri $f class A $.
	e0_issetri $e |- E. x x = A $.
	p_issetri $p |- A e. _V $= e0_issetri f0_issetri f1_issetri p_isset f1_issetri a_cvv a_wcel f0_issetri a_sup_set_class f1_issetri a_wceq f0_issetri a_wex p_mpbir $.
$}

$(If a class is a member of another class, it is a set.  Theorem 6.12 of
       [Quine] p. 44.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by
       Andrew Salmon, 8-Jun-2011.) $)

${
	$v A B  $.
	$d x A  $.
	$d x B  $.
	f0_elex $f class A $.
	f1_elex $f class B $.
	i0_elex $f set x $.
	p_elex $p |- ( A e. B -> A e. _V ) $= i0_elex a_sup_set_class f0_elex a_wceq i0_elex a_sup_set_class f1_elex a_wcel i0_elex p_exsimpl i0_elex f0_elex f1_elex a_df-clel i0_elex f0_elex p_isset i0_elex a_sup_set_class f0_elex a_wceq i0_elex a_sup_set_class f1_elex a_wcel a_wa i0_elex a_wex i0_elex a_sup_set_class f0_elex a_wceq i0_elex a_wex f0_elex f1_elex a_wcel f0_elex a_cvv a_wcel p_3imtr4i $.
$}

$(If a class is a member of another class, it is a set.  (Contributed by
       NM, 11-Jun-1994.) $)

${
	$v A B  $.
	f0_elexi $f class A $.
	f1_elexi $f class B $.
	e0_elexi $e |- A e. B $.
	p_elexi $p |- A e. _V $= e0_elexi f0_elexi f1_elexi p_elex f0_elexi f1_elexi a_wcel f0_elexi a_cvv a_wcel a_ax-mp $.
$}

$(An element of a class exists.  (Contributed by NM, 1-May-1995.) $)

${
	$v x A V  $.
	$d x A  $.
	f0_elisset $f set x $.
	f1_elisset $f class A $.
	f2_elisset $f class V $.
	p_elisset $p |- ( A e. V -> E. x x = A ) $= f1_elisset f2_elisset p_elex f0_elisset f1_elisset p_isset f1_elisset f2_elisset a_wcel f1_elisset a_cvv a_wcel f0_elisset a_sup_set_class f1_elisset a_wceq f0_elisset a_wex p_sylib $.
$}

$(If two classes each contain another class, then both contain some set.
       (Contributed by Alan Sare, 24-Oct-2011.) $)

${
	$v x A B C  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	f0_elex22 $f set x $.
	f1_elex22 $f class A $.
	f2_elex22 $f class B $.
	f3_elex22 $f class C $.
	p_elex22 $p |- ( ( A e. B /\ A e. C ) -> E. x ( x e. B /\ x e. C ) ) $= f1_elex22 f2_elex22 f0_elex22 a_sup_set_class p_eleq1a f1_elex22 f3_elex22 f0_elex22 a_sup_set_class p_eleq1a f1_elex22 f2_elex22 a_wcel f0_elex22 a_sup_set_class f1_elex22 a_wceq f0_elex22 a_sup_set_class f2_elex22 a_wcel f1_elex22 f3_elex22 a_wcel f0_elex22 a_sup_set_class f3_elex22 a_wcel p_anim12ii f1_elex22 f2_elex22 a_wcel f1_elex22 f3_elex22 a_wcel a_wa f0_elex22 a_sup_set_class f1_elex22 a_wceq f0_elex22 a_sup_set_class f2_elex22 a_wcel f0_elex22 a_sup_set_class f3_elex22 a_wcel a_wa a_wi f0_elex22 p_alrimiv f0_elex22 f1_elex22 f2_elex22 p_elisset f1_elex22 f2_elex22 a_wcel f0_elex22 a_sup_set_class f1_elex22 a_wceq f0_elex22 a_wex f1_elex22 f3_elex22 a_wcel p_adantr f0_elex22 a_sup_set_class f1_elex22 a_wceq f0_elex22 a_sup_set_class f2_elex22 a_wcel f0_elex22 a_sup_set_class f3_elex22 a_wcel a_wa f0_elex22 p_exim f1_elex22 f2_elex22 a_wcel f1_elex22 f3_elex22 a_wcel a_wa f0_elex22 a_sup_set_class f1_elex22 a_wceq f0_elex22 a_sup_set_class f2_elex22 a_wcel f0_elex22 a_sup_set_class f3_elex22 a_wcel a_wa a_wi f0_elex22 a_wal f0_elex22 a_sup_set_class f1_elex22 a_wceq f0_elex22 a_wex f0_elex22 a_sup_set_class f2_elex22 a_wcel f0_elex22 a_sup_set_class f3_elex22 a_wcel a_wa f0_elex22 a_wex p_sylc $.
$}

$(If a class contains another class, then it contains some set.
       (Contributed by Alan Sare, 25-Sep-2011.) $)

${
	$v x A B  $.
	$d x A  $.
	$d x B  $.
	f0_elex2 $f set x $.
	f1_elex2 $f class A $.
	f2_elex2 $f class B $.
	p_elex2 $p |- ( A e. B -> E. x x e. B ) $= f1_elex2 f2_elex2 f0_elex2 a_sup_set_class p_eleq1a f1_elex2 f2_elex2 a_wcel f0_elex2 a_sup_set_class f1_elex2 a_wceq f0_elex2 a_sup_set_class f2_elex2 a_wcel a_wi f0_elex2 p_alrimiv f0_elex2 f1_elex2 f2_elex2 p_elisset f0_elex2 a_sup_set_class f1_elex2 a_wceq f0_elex2 a_sup_set_class f2_elex2 a_wcel f0_elex2 p_exim f1_elex2 f2_elex2 a_wcel f0_elex2 a_sup_set_class f1_elex2 a_wceq f0_elex2 a_sup_set_class f2_elex2 a_wcel a_wi f0_elex2 a_wal f0_elex2 a_sup_set_class f1_elex2 a_wceq f0_elex2 a_wex f0_elex2 a_sup_set_class f2_elex2 a_wcel f0_elex2 a_wex p_sylc $.
$}

$(A universal quantifier restricted to the universe is unrestricted.
     (Contributed by NM, 26-Mar-2004.) $)

${
	$v ph x  $.
	f0_ralv $f wff ph $.
	f1_ralv $f set x $.
	p_ralv $p |- ( A. x e. _V ph <-> A. x ph ) $= f0_ralv f1_ralv a_cvv a_df-ral f1_ralv p_vex f1_ralv a_sup_set_class a_cvv a_wcel f0_ralv p_a1bi f0_ralv f1_ralv a_sup_set_class a_cvv a_wcel f0_ralv a_wi f1_ralv p_albii f0_ralv f1_ralv a_cvv a_wral f1_ralv a_sup_set_class a_cvv a_wcel f0_ralv a_wi f1_ralv a_wal f0_ralv f1_ralv a_wal p_bitr4i $.
$}

$(An existential quantifier restricted to the universe is unrestricted.
     (Contributed by NM, 26-Mar-2004.) $)

${
	$v ph x  $.
	f0_rexv $f wff ph $.
	f1_rexv $f set x $.
	p_rexv $p |- ( E. x e. _V ph <-> E. x ph ) $= f0_rexv f1_rexv a_cvv a_df-rex f1_rexv p_vex f1_rexv a_sup_set_class a_cvv a_wcel f0_rexv p_biantrur f0_rexv f1_rexv a_sup_set_class a_cvv a_wcel f0_rexv a_wa f1_rexv p_exbii f0_rexv f1_rexv a_cvv a_wrex f1_rexv a_sup_set_class a_cvv a_wcel f0_rexv a_wa f1_rexv a_wex f0_rexv f1_rexv a_wex p_bitr4i $.
$}

$(A uniqueness quantifier restricted to the universe is unrestricted.
     (Contributed by NM, 1-Nov-2010.) $)

${
	$v ph x  $.
	f0_reuv $f wff ph $.
	f1_reuv $f set x $.
	p_reuv $p |- ( E! x e. _V ph <-> E! x ph ) $= f0_reuv f1_reuv a_cvv a_df-reu f1_reuv p_vex f1_reuv a_sup_set_class a_cvv a_wcel f0_reuv p_biantrur f0_reuv f1_reuv a_sup_set_class a_cvv a_wcel f0_reuv a_wa f1_reuv p_eubii f0_reuv f1_reuv a_cvv a_wreu f1_reuv a_sup_set_class a_cvv a_wcel f0_reuv a_wa f1_reuv a_weu f0_reuv f1_reuv a_weu p_bitr4i $.
$}

$(A uniqueness quantifier restricted to the universe is unrestricted.
     (Contributed by Alexander van der Vekens, 17-Jun-2017.) $)

${
	$v ph x  $.
	f0_rmov $f wff ph $.
	f1_rmov $f set x $.
	p_rmov $p |- ( E* x e. _V ph <-> E* x ph ) $= f0_rmov f1_rmov a_cvv a_df-rmo f1_rmov p_vex f1_rmov a_sup_set_class a_cvv a_wcel f0_rmov p_biantrur f0_rmov f1_rmov a_sup_set_class a_cvv a_wcel f0_rmov a_wa f1_rmov p_mobii f0_rmov f1_rmov a_cvv a_wrmo f1_rmov a_sup_set_class a_cvv a_wcel f0_rmov a_wa f1_rmov a_wmo f0_rmov f1_rmov a_wmo p_bitr4i $.
$}

$(A class abstraction restricted to the universe is unrestricted.
     (Contributed by NM, 27-Dec-2004.)  (Proof shortened by Andrew Salmon,
     8-Jun-2011.) $)

${
	$v ph x  $.
	f0_rabab $f wff ph $.
	f1_rabab $f set x $.
	p_rabab $p |- { x e. _V | ph } = { x | ph } $= f0_rabab f1_rabab a_cvv a_df-rab f1_rabab p_vex f1_rabab a_sup_set_class a_cvv a_wcel f0_rabab p_biantrur f0_rabab f1_rabab a_sup_set_class a_cvv a_wcel f0_rabab a_wa f1_rabab p_abbii f0_rabab f1_rabab a_cvv a_crab f1_rabab a_sup_set_class a_cvv a_wcel f0_rabab a_wa f1_rabab a_cab f0_rabab f1_rabab a_cab p_eqtr4i $.
$}

$(Commutation of restricted and unrestricted universal quantifiers.
       (Contributed by NM, 26-Mar-2004.)  (Proof shortened by Andrew Salmon,
       8-Jun-2011.) $)

${
	$v ph x y A  $.
	$d x y  $.
	$d y A  $.
	f0_ralcom4 $f wff ph $.
	f1_ralcom4 $f set x $.
	f2_ralcom4 $f set y $.
	f3_ralcom4 $f class A $.
	p_ralcom4 $p |- ( A. x e. A A. y ph <-> A. y A. x e. A ph ) $= f0_ralcom4 f1_ralcom4 f2_ralcom4 f3_ralcom4 a_cvv p_ralcom f0_ralcom4 f2_ralcom4 p_ralv f0_ralcom4 f2_ralcom4 a_cvv a_wral f0_ralcom4 f2_ralcom4 a_wal f1_ralcom4 f3_ralcom4 p_ralbii f0_ralcom4 f1_ralcom4 f3_ralcom4 a_wral f2_ralcom4 p_ralv f0_ralcom4 f2_ralcom4 a_cvv a_wral f1_ralcom4 f3_ralcom4 a_wral f0_ralcom4 f1_ralcom4 f3_ralcom4 a_wral f2_ralcom4 a_cvv a_wral f0_ralcom4 f2_ralcom4 a_wal f1_ralcom4 f3_ralcom4 a_wral f0_ralcom4 f1_ralcom4 f3_ralcom4 a_wral f2_ralcom4 a_wal p_3bitr3i $.
$}

$(Commutation of restricted and unrestricted existential quantifiers.
       (Contributed by NM, 12-Apr-2004.)  (Proof shortened by Andrew Salmon,
       8-Jun-2011.) $)

${
	$v ph x y A  $.
	$d x y  $.
	$d y A  $.
	f0_rexcom4 $f wff ph $.
	f1_rexcom4 $f set x $.
	f2_rexcom4 $f set y $.
	f3_rexcom4 $f class A $.
	p_rexcom4 $p |- ( E. x e. A E. y ph <-> E. y E. x e. A ph ) $= f0_rexcom4 f1_rexcom4 f2_rexcom4 f3_rexcom4 a_cvv p_rexcom f0_rexcom4 f2_rexcom4 p_rexv f0_rexcom4 f2_rexcom4 a_cvv a_wrex f0_rexcom4 f2_rexcom4 a_wex f1_rexcom4 f3_rexcom4 p_rexbii f0_rexcom4 f1_rexcom4 f3_rexcom4 a_wrex f2_rexcom4 p_rexv f0_rexcom4 f2_rexcom4 a_cvv a_wrex f1_rexcom4 f3_rexcom4 a_wrex f0_rexcom4 f1_rexcom4 f3_rexcom4 a_wrex f2_rexcom4 a_cvv a_wrex f0_rexcom4 f2_rexcom4 a_wex f1_rexcom4 f3_rexcom4 a_wrex f0_rexcom4 f1_rexcom4 f3_rexcom4 a_wrex f2_rexcom4 a_wex p_3bitr3i $.
$}

$(Specialized existential commutation lemma.  (Contributed by Jeff Madsen,
       1-Jun-2011.) $)

${
	$v ph ps x y A  $.
	$d A x  $.
	$d x y  $.
	$d ph x  $.
	f0_rexcom4a $f wff ph $.
	f1_rexcom4a $f wff ps $.
	f2_rexcom4a $f set x $.
	f3_rexcom4a $f set y $.
	f4_rexcom4a $f class A $.
	p_rexcom4a $p |- ( E. x E. y e. A ( ph /\ ps ) <-> E. y e. A ( ph /\ E. x ps ) ) $= f0_rexcom4a f1_rexcom4a a_wa f3_rexcom4a f2_rexcom4a f4_rexcom4a p_rexcom4 f0_rexcom4a f1_rexcom4a f2_rexcom4a p_19.42v f0_rexcom4a f1_rexcom4a a_wa f2_rexcom4a a_wex f0_rexcom4a f1_rexcom4a f2_rexcom4a a_wex a_wa f3_rexcom4a f4_rexcom4a p_rexbii f0_rexcom4a f1_rexcom4a a_wa f3_rexcom4a f4_rexcom4a a_wrex f2_rexcom4a a_wex f0_rexcom4a f1_rexcom4a a_wa f2_rexcom4a a_wex f3_rexcom4a f4_rexcom4a a_wrex f0_rexcom4a f1_rexcom4a f2_rexcom4a a_wex a_wa f3_rexcom4a f4_rexcom4a a_wrex p_bitr3i $.
$}

$(Specialized existential commutation lemma.  (Contributed by Jeff Madsen,
       1-Jun-2011.) $)

${
	$v ph x y A B  $.
	$d A x  $.
	$d x y  $.
	$d ph x  $.
	$d B x  $.
	f0_rexcom4b $f wff ph $.
	f1_rexcom4b $f set x $.
	f2_rexcom4b $f set y $.
	f3_rexcom4b $f class A $.
	f4_rexcom4b $f class B $.
	e0_rexcom4b $e |- B e. _V $.
	p_rexcom4b $p |- ( E. x E. y e. A ( ph /\ x = B ) <-> E. y e. A ph ) $= f0_rexcom4b f1_rexcom4b a_sup_set_class f4_rexcom4b a_wceq f1_rexcom4b f2_rexcom4b f3_rexcom4b p_rexcom4a e0_rexcom4b f1_rexcom4b f4_rexcom4b p_isseti f1_rexcom4b a_sup_set_class f4_rexcom4b a_wceq f1_rexcom4b a_wex f0_rexcom4b p_biantru f0_rexcom4b f0_rexcom4b f1_rexcom4b a_sup_set_class f4_rexcom4b a_wceq f1_rexcom4b a_wex a_wa f2_rexcom4b f3_rexcom4b p_rexbii f0_rexcom4b f1_rexcom4b a_sup_set_class f4_rexcom4b a_wceq a_wa f2_rexcom4b f3_rexcom4b a_wrex f1_rexcom4b a_wex f0_rexcom4b f1_rexcom4b a_sup_set_class f4_rexcom4b a_wceq f1_rexcom4b a_wex a_wa f2_rexcom4b f3_rexcom4b a_wrex f0_rexcom4b f2_rexcom4b f3_rexcom4b a_wrex p_bitr4i $.
$}

$(Closed theorem version of ~ ceqsalg .  (Contributed by NM,
       28-Feb-2013.)  (Revised by Mario Carneiro, 10-Oct-2016.) $)

${
	$v ph ps x A V  $.
	$d x A  $.
	f0_ceqsalt $f wff ph $.
	f1_ceqsalt $f wff ps $.
	f2_ceqsalt $f set x $.
	f3_ceqsalt $f class A $.
	f4_ceqsalt $f class V $.
	p_ceqsalt $p |- ( ( F/ x ps /\ A. x ( x = A -> ( ph <-> ps ) ) /\ A e. V ) -> ( A. x ( x = A -> ph ) <-> ps ) ) $= f2_ceqsalt f3_ceqsalt f4_ceqsalt p_elisset f3_ceqsalt f4_ceqsalt a_wcel f1_ceqsalt f2_ceqsalt a_wnf f2_ceqsalt a_sup_set_class f3_ceqsalt a_wceq f2_ceqsalt a_wex f2_ceqsalt a_sup_set_class f3_ceqsalt a_wceq f0_ceqsalt f1_ceqsalt a_wb a_wi f2_ceqsalt a_wal p_3ad2ant3 f0_ceqsalt f1_ceqsalt p_bi1 f0_ceqsalt f1_ceqsalt a_wb f0_ceqsalt f1_ceqsalt f2_ceqsalt a_sup_set_class f3_ceqsalt a_wceq p_imim3i f2_ceqsalt a_sup_set_class f3_ceqsalt a_wceq f0_ceqsalt f1_ceqsalt a_wb a_wi f2_ceqsalt a_sup_set_class f3_ceqsalt a_wceq f0_ceqsalt a_wi f2_ceqsalt a_sup_set_class f3_ceqsalt a_wceq f1_ceqsalt a_wi f2_ceqsalt p_al2imi f2_ceqsalt a_sup_set_class f3_ceqsalt a_wceq f0_ceqsalt f1_ceqsalt a_wb a_wi f2_ceqsalt a_wal f1_ceqsalt f2_ceqsalt a_wnf f2_ceqsalt a_sup_set_class f3_ceqsalt a_wceq f0_ceqsalt a_wi f2_ceqsalt a_wal f2_ceqsalt a_sup_set_class f3_ceqsalt a_wceq f1_ceqsalt a_wi f2_ceqsalt a_wal a_wi f3_ceqsalt f4_ceqsalt a_wcel p_3ad2ant2 f2_ceqsalt a_sup_set_class f3_ceqsalt a_wceq f1_ceqsalt f2_ceqsalt p_19.23t f1_ceqsalt f2_ceqsalt a_wnf f2_ceqsalt a_sup_set_class f3_ceqsalt a_wceq f0_ceqsalt f1_ceqsalt a_wb a_wi f2_ceqsalt a_wal f2_ceqsalt a_sup_set_class f3_ceqsalt a_wceq f1_ceqsalt a_wi f2_ceqsalt a_wal f2_ceqsalt a_sup_set_class f3_ceqsalt a_wceq f2_ceqsalt a_wex f1_ceqsalt a_wi a_wb f3_ceqsalt f4_ceqsalt a_wcel p_3ad2ant1 f1_ceqsalt f2_ceqsalt a_wnf f2_ceqsalt a_sup_set_class f3_ceqsalt a_wceq f0_ceqsalt f1_ceqsalt a_wb a_wi f2_ceqsalt a_wal f3_ceqsalt f4_ceqsalt a_wcel a_w3a f2_ceqsalt a_sup_set_class f3_ceqsalt a_wceq f0_ceqsalt a_wi f2_ceqsalt a_wal f2_ceqsalt a_sup_set_class f3_ceqsalt a_wceq f1_ceqsalt a_wi f2_ceqsalt a_wal f2_ceqsalt a_sup_set_class f3_ceqsalt a_wceq f2_ceqsalt a_wex f1_ceqsalt a_wi p_sylibd f1_ceqsalt f2_ceqsalt a_wnf f2_ceqsalt a_sup_set_class f3_ceqsalt a_wceq f0_ceqsalt f1_ceqsalt a_wb a_wi f2_ceqsalt a_wal f3_ceqsalt f4_ceqsalt a_wcel a_w3a f2_ceqsalt a_sup_set_class f3_ceqsalt a_wceq f0_ceqsalt a_wi f2_ceqsalt a_wal f2_ceqsalt a_sup_set_class f3_ceqsalt a_wceq f2_ceqsalt a_wex f1_ceqsalt p_mpid f0_ceqsalt f1_ceqsalt p_bi2 f0_ceqsalt f1_ceqsalt a_wb f1_ceqsalt f0_ceqsalt a_wi f2_ceqsalt a_sup_set_class f3_ceqsalt a_wceq p_imim2i f2_ceqsalt a_sup_set_class f3_ceqsalt a_wceq f0_ceqsalt f1_ceqsalt a_wb a_wi f2_ceqsalt a_sup_set_class f3_ceqsalt a_wceq f1_ceqsalt f0_ceqsalt p_com23 f2_ceqsalt a_sup_set_class f3_ceqsalt a_wceq f0_ceqsalt f1_ceqsalt a_wb a_wi f1_ceqsalt f2_ceqsalt a_sup_set_class f3_ceqsalt a_wceq f0_ceqsalt a_wi a_wi f2_ceqsalt p_alimi f2_ceqsalt a_sup_set_class f3_ceqsalt a_wceq f0_ceqsalt f1_ceqsalt a_wb a_wi f2_ceqsalt a_wal f1_ceqsalt f2_ceqsalt a_wnf f1_ceqsalt f2_ceqsalt a_sup_set_class f3_ceqsalt a_wceq f0_ceqsalt a_wi a_wi f2_ceqsalt a_wal f3_ceqsalt f4_ceqsalt a_wcel p_3ad2ant2 f1_ceqsalt f2_ceqsalt a_sup_set_class f3_ceqsalt a_wceq f0_ceqsalt a_wi f2_ceqsalt p_19.21t f1_ceqsalt f2_ceqsalt a_wnf f2_ceqsalt a_sup_set_class f3_ceqsalt a_wceq f0_ceqsalt f1_ceqsalt a_wb a_wi f2_ceqsalt a_wal f1_ceqsalt f2_ceqsalt a_sup_set_class f3_ceqsalt a_wceq f0_ceqsalt a_wi a_wi f2_ceqsalt a_wal f1_ceqsalt f2_ceqsalt a_sup_set_class f3_ceqsalt a_wceq f0_ceqsalt a_wi f2_ceqsalt a_wal a_wi a_wb f3_ceqsalt f4_ceqsalt a_wcel p_3ad2ant1 f1_ceqsalt f2_ceqsalt a_wnf f2_ceqsalt a_sup_set_class f3_ceqsalt a_wceq f0_ceqsalt f1_ceqsalt a_wb a_wi f2_ceqsalt a_wal f3_ceqsalt f4_ceqsalt a_wcel a_w3a f1_ceqsalt f2_ceqsalt a_sup_set_class f3_ceqsalt a_wceq f0_ceqsalt a_wi a_wi f2_ceqsalt a_wal f1_ceqsalt f2_ceqsalt a_sup_set_class f3_ceqsalt a_wceq f0_ceqsalt a_wi f2_ceqsalt a_wal a_wi p_mpbid f1_ceqsalt f2_ceqsalt a_wnf f2_ceqsalt a_sup_set_class f3_ceqsalt a_wceq f0_ceqsalt f1_ceqsalt a_wb a_wi f2_ceqsalt a_wal f3_ceqsalt f4_ceqsalt a_wcel a_w3a f2_ceqsalt a_sup_set_class f3_ceqsalt a_wceq f0_ceqsalt a_wi f2_ceqsalt a_wal f1_ceqsalt p_impbid $.
$}

$(Restricted quantifier version of ~ ceqsalt .  (Contributed by NM,
       28-Feb-2013.)  (Revised by Mario Carneiro, 10-Oct-2016.) $)

${
	$v ph ps x A B  $.
	$d x A  $.
	$d x B  $.
	f0_ceqsralt $f wff ph $.
	f1_ceqsralt $f wff ps $.
	f2_ceqsralt $f set x $.
	f3_ceqsralt $f class A $.
	f4_ceqsralt $f class B $.
	p_ceqsralt $p |- ( ( F/ x ps /\ A. x ( x = A -> ( ph <-> ps ) ) /\ A e. B ) -> ( A. x e. B ( x = A -> ph ) <-> ps ) ) $= f2_ceqsralt a_sup_set_class f3_ceqsralt a_wceq f0_ceqsralt a_wi f2_ceqsralt f4_ceqsralt a_df-ral f2_ceqsralt a_sup_set_class f3_ceqsralt f4_ceqsralt p_eleq1 f2_ceqsralt a_sup_set_class f3_ceqsralt a_wceq f2_ceqsralt a_sup_set_class f4_ceqsralt a_wcel f3_ceqsralt f4_ceqsralt a_wcel p_pm5.32ri f2_ceqsralt a_sup_set_class f4_ceqsralt a_wcel f2_ceqsralt a_sup_set_class f3_ceqsralt a_wceq a_wa f3_ceqsralt f4_ceqsralt a_wcel f2_ceqsralt a_sup_set_class f3_ceqsralt a_wceq a_wa f0_ceqsralt p_imbi1i f2_ceqsralt a_sup_set_class f4_ceqsralt a_wcel f2_ceqsralt a_sup_set_class f3_ceqsralt a_wceq f0_ceqsralt p_impexp f3_ceqsralt f4_ceqsralt a_wcel f2_ceqsralt a_sup_set_class f3_ceqsralt a_wceq f0_ceqsralt p_impexp f2_ceqsralt a_sup_set_class f4_ceqsralt a_wcel f2_ceqsralt a_sup_set_class f3_ceqsralt a_wceq a_wa f0_ceqsralt a_wi f3_ceqsralt f4_ceqsralt a_wcel f2_ceqsralt a_sup_set_class f3_ceqsralt a_wceq a_wa f0_ceqsralt a_wi f2_ceqsralt a_sup_set_class f4_ceqsralt a_wcel f2_ceqsralt a_sup_set_class f3_ceqsralt a_wceq f0_ceqsralt a_wi a_wi f3_ceqsralt f4_ceqsralt a_wcel f2_ceqsralt a_sup_set_class f3_ceqsralt a_wceq f0_ceqsralt a_wi a_wi p_3bitr3i f2_ceqsralt a_sup_set_class f4_ceqsralt a_wcel f2_ceqsralt a_sup_set_class f3_ceqsralt a_wceq f0_ceqsralt a_wi a_wi f3_ceqsralt f4_ceqsralt a_wcel f2_ceqsralt a_sup_set_class f3_ceqsralt a_wceq f0_ceqsralt a_wi a_wi f2_ceqsralt p_albii f2_ceqsralt a_sup_set_class f4_ceqsralt a_wcel f2_ceqsralt a_sup_set_class f3_ceqsralt a_wceq f0_ceqsralt a_wi a_wi f2_ceqsralt a_wal f3_ceqsralt f4_ceqsralt a_wcel f2_ceqsralt a_sup_set_class f3_ceqsralt a_wceq f0_ceqsralt a_wi a_wi f2_ceqsralt a_wal a_wb f1_ceqsralt f2_ceqsralt a_wnf f2_ceqsralt a_sup_set_class f3_ceqsralt a_wceq f0_ceqsralt f1_ceqsralt a_wb a_wi f2_ceqsralt a_wal f3_ceqsralt f4_ceqsralt a_wcel a_w3a p_a1i f2_ceqsralt a_sup_set_class f3_ceqsralt a_wceq f0_ceqsralt a_wi f2_ceqsralt f4_ceqsralt a_wral f2_ceqsralt a_sup_set_class f4_ceqsralt a_wcel f2_ceqsralt a_sup_set_class f3_ceqsralt a_wceq f0_ceqsralt a_wi a_wi f2_ceqsralt a_wal f1_ceqsralt f2_ceqsralt a_wnf f2_ceqsralt a_sup_set_class f3_ceqsralt a_wceq f0_ceqsralt f1_ceqsralt a_wb a_wi f2_ceqsralt a_wal f3_ceqsralt f4_ceqsralt a_wcel a_w3a f3_ceqsralt f4_ceqsralt a_wcel f2_ceqsralt a_sup_set_class f3_ceqsralt a_wceq f0_ceqsralt a_wi a_wi f2_ceqsralt a_wal p_syl5bb f3_ceqsralt f4_ceqsralt a_wcel f2_ceqsralt a_sup_set_class f3_ceqsralt a_wceq f0_ceqsralt a_wi f2_ceqsralt p_19.21v f1_ceqsralt f2_ceqsralt a_wnf f2_ceqsralt a_sup_set_class f3_ceqsralt a_wceq f0_ceqsralt f1_ceqsralt a_wb a_wi f2_ceqsralt a_wal f3_ceqsralt f4_ceqsralt a_wcel a_w3a f2_ceqsralt a_sup_set_class f3_ceqsralt a_wceq f0_ceqsralt a_wi f2_ceqsralt f4_ceqsralt a_wral f3_ceqsralt f4_ceqsralt a_wcel f2_ceqsralt a_sup_set_class f3_ceqsralt a_wceq f0_ceqsralt a_wi a_wi f2_ceqsralt a_wal f3_ceqsralt f4_ceqsralt a_wcel f2_ceqsralt a_sup_set_class f3_ceqsralt a_wceq f0_ceqsralt a_wi f2_ceqsralt a_wal a_wi p_syl6bb f3_ceqsralt f4_ceqsralt a_wcel f2_ceqsralt a_sup_set_class f3_ceqsralt a_wceq f0_ceqsralt a_wi f2_ceqsralt a_wal p_biimt f3_ceqsralt f4_ceqsralt a_wcel f1_ceqsralt f2_ceqsralt a_wnf f2_ceqsralt a_sup_set_class f3_ceqsralt a_wceq f0_ceqsralt a_wi f2_ceqsralt a_wal f3_ceqsralt f4_ceqsralt a_wcel f2_ceqsralt a_sup_set_class f3_ceqsralt a_wceq f0_ceqsralt a_wi f2_ceqsralt a_wal a_wi a_wb f2_ceqsralt a_sup_set_class f3_ceqsralt a_wceq f0_ceqsralt f1_ceqsralt a_wb a_wi f2_ceqsralt a_wal p_3ad2ant3 f0_ceqsralt f1_ceqsralt f2_ceqsralt f3_ceqsralt f4_ceqsralt p_ceqsalt f1_ceqsralt f2_ceqsralt a_wnf f2_ceqsralt a_sup_set_class f3_ceqsralt a_wceq f0_ceqsralt f1_ceqsralt a_wb a_wi f2_ceqsralt a_wal f3_ceqsralt f4_ceqsralt a_wcel a_w3a f2_ceqsralt a_sup_set_class f3_ceqsralt a_wceq f0_ceqsralt a_wi f2_ceqsralt f4_ceqsralt a_wral f3_ceqsralt f4_ceqsralt a_wcel f2_ceqsralt a_sup_set_class f3_ceqsralt a_wceq f0_ceqsralt a_wi f2_ceqsralt a_wal a_wi f2_ceqsralt a_sup_set_class f3_ceqsralt a_wceq f0_ceqsralt a_wi f2_ceqsralt a_wal f1_ceqsralt p_3bitr2d $.
$}

$(A representation of explicit substitution of a class for a variable,
       inferred from an implicit substitution hypothesis.  (Contributed by NM,
       29-Oct-2003.)  (Proof shortened by Andrew Salmon, 8-Jun-2011.) $)

${
	$v ph ps x A V  $.
	$d x A  $.
	f0_ceqsalg $f wff ph $.
	f1_ceqsalg $f wff ps $.
	f2_ceqsalg $f set x $.
	f3_ceqsalg $f class A $.
	f4_ceqsalg $f class V $.
	e0_ceqsalg $e |- F/ x ps $.
	e1_ceqsalg $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_ceqsalg $p |- ( A e. V -> ( A. x ( x = A -> ph ) <-> ps ) ) $= f2_ceqsalg f3_ceqsalg f4_ceqsalg p_elisset f2_ceqsalg a_sup_set_class f3_ceqsalg a_wceq f0_ceqsalg a_wi f2_ceqsalg p_nfa1 e0_ceqsalg e1_ceqsalg f2_ceqsalg a_sup_set_class f3_ceqsalg a_wceq f0_ceqsalg f1_ceqsalg p_biimpd f2_ceqsalg a_sup_set_class f3_ceqsalg a_wceq f0_ceqsalg f1_ceqsalg p_a2i f2_ceqsalg a_sup_set_class f3_ceqsalg a_wceq f0_ceqsalg a_wi f2_ceqsalg a_sup_set_class f3_ceqsalg a_wceq f1_ceqsalg a_wi f2_ceqsalg p_sps f2_ceqsalg a_sup_set_class f3_ceqsalg a_wceq f0_ceqsalg a_wi f2_ceqsalg a_wal f2_ceqsalg a_sup_set_class f3_ceqsalg a_wceq f1_ceqsalg f2_ceqsalg p_exlimd f3_ceqsalg f4_ceqsalg a_wcel f2_ceqsalg a_sup_set_class f3_ceqsalg a_wceq f2_ceqsalg a_wex f2_ceqsalg a_sup_set_class f3_ceqsalg a_wceq f0_ceqsalg a_wi f2_ceqsalg a_wal f1_ceqsalg p_syl5com e0_ceqsalg e1_ceqsalg f2_ceqsalg a_sup_set_class f3_ceqsalg a_wceq f0_ceqsalg f1_ceqsalg p_biimprcd f1_ceqsalg f2_ceqsalg a_sup_set_class f3_ceqsalg a_wceq f0_ceqsalg a_wi f2_ceqsalg p_alrimi f3_ceqsalg f4_ceqsalg a_wcel f2_ceqsalg a_sup_set_class f3_ceqsalg a_wceq f0_ceqsalg a_wi f2_ceqsalg a_wal f1_ceqsalg p_impbid1 $.
$}

$(A representation of explicit substitution of a class for a variable,
       inferred from an implicit substitution hypothesis.  (Contributed by NM,
       18-Aug-1993.) $)

${
	$v ph ps x A  $.
	$d x A  $.
	f0_ceqsal $f wff ph $.
	f1_ceqsal $f wff ps $.
	f2_ceqsal $f set x $.
	f3_ceqsal $f class A $.
	e0_ceqsal $e |- F/ x ps $.
	e1_ceqsal $e |- A e. _V $.
	e2_ceqsal $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_ceqsal $p |- ( A. x ( x = A -> ph ) <-> ps ) $= e1_ceqsal e0_ceqsal e2_ceqsal f0_ceqsal f1_ceqsal f2_ceqsal f3_ceqsal a_cvv p_ceqsalg f3_ceqsal a_cvv a_wcel f2_ceqsal a_sup_set_class f3_ceqsal a_wceq f0_ceqsal a_wi f2_ceqsal a_wal f1_ceqsal a_wb a_ax-mp $.
$}

$(A representation of explicit substitution of a class for a variable,
       inferred from an implicit substitution hypothesis.  (Contributed by NM,
       18-Aug-1993.) $)

${
	$v ph ps x A  $.
	$d x A  $.
	$d x ps  $.
	f0_ceqsalv $f wff ph $.
	f1_ceqsalv $f wff ps $.
	f2_ceqsalv $f set x $.
	f3_ceqsalv $f class A $.
	e0_ceqsalv $e |- A e. _V $.
	e1_ceqsalv $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_ceqsalv $p |- ( A. x ( x = A -> ph ) <-> ps ) $= f1_ceqsalv f2_ceqsalv p_nfv e0_ceqsalv e1_ceqsalv f0_ceqsalv f1_ceqsalv f2_ceqsalv f3_ceqsalv p_ceqsal $.
$}

$(Restricted quantifier version of ~ ceqsalv .  (Contributed by NM,
       21-Jun-2013.) $)

${
	$v ph ps x A B  $.
	$d x A  $.
	$d x B  $.
	$d x ps  $.
	f0_ceqsralv $f wff ph $.
	f1_ceqsralv $f wff ps $.
	f2_ceqsralv $f set x $.
	f3_ceqsralv $f class A $.
	f4_ceqsralv $f class B $.
	e0_ceqsralv $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_ceqsralv $p |- ( A e. B -> ( A. x e. B ( x = A -> ph ) <-> ps ) ) $= f1_ceqsralv f2_ceqsralv p_nfv e0_ceqsralv f2_ceqsralv a_sup_set_class f3_ceqsralv a_wceq f0_ceqsralv f1_ceqsralv a_wb a_wi f2_ceqsralv a_ax-gen f0_ceqsralv f1_ceqsralv f2_ceqsralv f3_ceqsralv f4_ceqsralv p_ceqsralt f1_ceqsralv f2_ceqsralv a_wnf f2_ceqsralv a_sup_set_class f3_ceqsralv a_wceq f0_ceqsralv f1_ceqsralv a_wb a_wi f2_ceqsralv a_wal f3_ceqsralv f4_ceqsralv a_wcel f2_ceqsralv a_sup_set_class f3_ceqsralv a_wceq f0_ceqsralv a_wi f2_ceqsralv f4_ceqsralv a_wral f1_ceqsralv a_wb p_mp3an12 $.
$}

$(Implicit substitution for class with embedded variable.  (Contributed by
       NM, 17-May-1996.) $)

${
	$v ph ps ch th x A B  $.
	$d x ps  $.
	f0_gencl $f wff ph $.
	f1_gencl $f wff ps $.
	f2_gencl $f wff ch $.
	f3_gencl $f wff th $.
	f4_gencl $f set x $.
	f5_gencl $f class A $.
	f6_gencl $f class B $.
	e0_gencl $e |- ( th <-> E. x ( ch /\ A = B ) ) $.
	e1_gencl $e |- ( A = B -> ( ph <-> ps ) ) $.
	e2_gencl $e |- ( ch -> ph ) $.
	p_gencl $p |- ( th -> ps ) $= e0_gencl e2_gencl e1_gencl f2_gencl f0_gencl f5_gencl f6_gencl a_wceq f1_gencl p_syl5ib f5_gencl f6_gencl a_wceq f2_gencl f1_gencl p_impcom f2_gencl f5_gencl f6_gencl a_wceq a_wa f1_gencl f4_gencl p_exlimiv f3_gencl f2_gencl f5_gencl f6_gencl a_wceq a_wa f4_gencl a_wex f1_gencl p_sylbi $.
$}

$(Implicit substitution for class with embedded variable.  (Contributed by
       NM, 17-May-1996.) $)

${
	$v ph ps ch x y A B C D R S  $.
	$d x y  $.
	$d x R  $.
	$d x ps  $.
	$d y C  $.
	$d y S  $.
	$d y ch  $.
	f0_2gencl $f wff ph $.
	f1_2gencl $f wff ps $.
	f2_2gencl $f wff ch $.
	f3_2gencl $f set x $.
	f4_2gencl $f set y $.
	f5_2gencl $f class A $.
	f6_2gencl $f class B $.
	f7_2gencl $f class C $.
	f8_2gencl $f class D $.
	f9_2gencl $f class R $.
	f10_2gencl $f class S $.
	e0_2gencl $e |- ( C e. S <-> E. x e. R A = C ) $.
	e1_2gencl $e |- ( D e. S <-> E. y e. R B = D ) $.
	e2_2gencl $e |- ( A = C -> ( ph <-> ps ) ) $.
	e3_2gencl $e |- ( B = D -> ( ps <-> ch ) ) $.
	e4_2gencl $e |- ( ( x e. R /\ y e. R ) -> ph ) $.
	p_2gencl $p |- ( ( C e. S /\ D e. S ) -> ch ) $= e1_2gencl f6_2gencl f8_2gencl a_wceq f4_2gencl f9_2gencl a_df-rex f8_2gencl f10_2gencl a_wcel f6_2gencl f8_2gencl a_wceq f4_2gencl f9_2gencl a_wrex f4_2gencl a_sup_set_class f9_2gencl a_wcel f6_2gencl f8_2gencl a_wceq a_wa f4_2gencl a_wex p_bitri e3_2gencl f6_2gencl f8_2gencl a_wceq f1_2gencl f2_2gencl f7_2gencl f10_2gencl a_wcel p_imbi2d e0_2gencl f5_2gencl f7_2gencl a_wceq f3_2gencl f9_2gencl a_df-rex f7_2gencl f10_2gencl a_wcel f5_2gencl f7_2gencl a_wceq f3_2gencl f9_2gencl a_wrex f3_2gencl a_sup_set_class f9_2gencl a_wcel f5_2gencl f7_2gencl a_wceq a_wa f3_2gencl a_wex p_bitri e2_2gencl f5_2gencl f7_2gencl a_wceq f0_2gencl f1_2gencl f4_2gencl a_sup_set_class f9_2gencl a_wcel p_imbi2d e4_2gencl f3_2gencl a_sup_set_class f9_2gencl a_wcel f4_2gencl a_sup_set_class f9_2gencl a_wcel f0_2gencl p_ex f4_2gencl a_sup_set_class f9_2gencl a_wcel f0_2gencl a_wi f4_2gencl a_sup_set_class f9_2gencl a_wcel f1_2gencl a_wi f3_2gencl a_sup_set_class f9_2gencl a_wcel f7_2gencl f10_2gencl a_wcel f3_2gencl f5_2gencl f7_2gencl p_gencl f7_2gencl f10_2gencl a_wcel f4_2gencl a_sup_set_class f9_2gencl a_wcel f1_2gencl p_com12 f7_2gencl f10_2gencl a_wcel f1_2gencl a_wi f7_2gencl f10_2gencl a_wcel f2_2gencl a_wi f4_2gencl a_sup_set_class f9_2gencl a_wcel f8_2gencl f10_2gencl a_wcel f4_2gencl f6_2gencl f8_2gencl p_gencl f8_2gencl f10_2gencl a_wcel f7_2gencl f10_2gencl a_wcel f2_2gencl p_impcom $.
$}

$(Implicit substitution for class with embedded variable.  (Contributed by
       NM, 17-May-1996.) $)

${
	$v ph ps ch th x y z A B C D R S F G  $.
	$d x y z  $.
	$d y z D  $.
	$d z F  $.
	$d x y R  $.
	$d y z S  $.
	$d x ps  $.
	$d y ch  $.
	$d z th  $.
	f0_3gencl $f wff ph $.
	f1_3gencl $f wff ps $.
	f2_3gencl $f wff ch $.
	f3_3gencl $f wff th $.
	f4_3gencl $f set x $.
	f5_3gencl $f set y $.
	f6_3gencl $f set z $.
	f7_3gencl $f class A $.
	f8_3gencl $f class B $.
	f9_3gencl $f class C $.
	f10_3gencl $f class D $.
	f11_3gencl $f class R $.
	f12_3gencl $f class S $.
	f13_3gencl $f class F $.
	f14_3gencl $f class G $.
	e0_3gencl $e |- ( D e. S <-> E. x e. R A = D ) $.
	e1_3gencl $e |- ( F e. S <-> E. y e. R B = F ) $.
	e2_3gencl $e |- ( G e. S <-> E. z e. R C = G ) $.
	e3_3gencl $e |- ( A = D -> ( ph <-> ps ) ) $.
	e4_3gencl $e |- ( B = F -> ( ps <-> ch ) ) $.
	e5_3gencl $e |- ( C = G -> ( ch <-> th ) ) $.
	e6_3gencl $e |- ( ( x e. R /\ y e. R /\ z e. R ) -> ph ) $.
	p_3gencl $p |- ( ( D e. S /\ F e. S /\ G e. S ) -> th ) $= e2_3gencl f9_3gencl f14_3gencl a_wceq f6_3gencl f11_3gencl a_df-rex f14_3gencl f12_3gencl a_wcel f9_3gencl f14_3gencl a_wceq f6_3gencl f11_3gencl a_wrex f6_3gencl a_sup_set_class f11_3gencl a_wcel f9_3gencl f14_3gencl a_wceq a_wa f6_3gencl a_wex p_bitri e5_3gencl f9_3gencl f14_3gencl a_wceq f2_3gencl f3_3gencl f10_3gencl f12_3gencl a_wcel f13_3gencl f12_3gencl a_wcel a_wa p_imbi2d e0_3gencl e1_3gencl e3_3gencl f7_3gencl f10_3gencl a_wceq f0_3gencl f1_3gencl f6_3gencl a_sup_set_class f11_3gencl a_wcel p_imbi2d e4_3gencl f8_3gencl f13_3gencl a_wceq f1_3gencl f2_3gencl f6_3gencl a_sup_set_class f11_3gencl a_wcel p_imbi2d e6_3gencl f4_3gencl a_sup_set_class f11_3gencl a_wcel f5_3gencl a_sup_set_class f11_3gencl a_wcel f6_3gencl a_sup_set_class f11_3gencl a_wcel f0_3gencl p_3expia f6_3gencl a_sup_set_class f11_3gencl a_wcel f0_3gencl a_wi f6_3gencl a_sup_set_class f11_3gencl a_wcel f1_3gencl a_wi f6_3gencl a_sup_set_class f11_3gencl a_wcel f2_3gencl a_wi f4_3gencl f5_3gencl f7_3gencl f8_3gencl f10_3gencl f13_3gencl f11_3gencl f12_3gencl p_2gencl f10_3gencl f12_3gencl a_wcel f13_3gencl f12_3gencl a_wcel a_wa f6_3gencl a_sup_set_class f11_3gencl a_wcel f2_3gencl p_com12 f10_3gencl f12_3gencl a_wcel f13_3gencl f12_3gencl a_wcel a_wa f2_3gencl a_wi f10_3gencl f12_3gencl a_wcel f13_3gencl f12_3gencl a_wcel a_wa f3_3gencl a_wi f6_3gencl a_sup_set_class f11_3gencl a_wcel f14_3gencl f12_3gencl a_wcel f6_3gencl f9_3gencl f14_3gencl p_gencl f14_3gencl f12_3gencl a_wcel f10_3gencl f12_3gencl a_wcel f13_3gencl f12_3gencl a_wcel a_wa f3_3gencl p_com12 f10_3gencl f12_3gencl a_wcel f13_3gencl f12_3gencl a_wcel f14_3gencl f12_3gencl a_wcel f3_3gencl p_3impia $.
$}

$(Implicit substitution inference for general classes.  (Contributed by
       NM, 26-Aug-2007.) $)

${
	$v ph ps ch x A V  $.
	$d x A  $.
	$d x ps  $.
	f0_cgsexg $f wff ph $.
	f1_cgsexg $f wff ps $.
	f2_cgsexg $f wff ch $.
	f3_cgsexg $f set x $.
	f4_cgsexg $f class A $.
	f5_cgsexg $f class V $.
	e0_cgsexg $e |- ( x = A -> ch ) $.
	e1_cgsexg $e |- ( ch -> ( ph <-> ps ) ) $.
	p_cgsexg $p |- ( A e. V -> ( E. x ( ch /\ ph ) <-> ps ) ) $= e1_cgsexg f2_cgsexg f0_cgsexg f1_cgsexg p_biimpa f2_cgsexg f0_cgsexg a_wa f1_cgsexg f3_cgsexg p_exlimiv f3_cgsexg f4_cgsexg f5_cgsexg p_elisset e0_cgsexg f3_cgsexg a_sup_set_class f4_cgsexg a_wceq f2_cgsexg f3_cgsexg p_eximi f4_cgsexg f5_cgsexg a_wcel f3_cgsexg a_sup_set_class f4_cgsexg a_wceq f3_cgsexg a_wex f2_cgsexg f3_cgsexg a_wex p_syl e1_cgsexg f2_cgsexg f0_cgsexg f1_cgsexg p_biimprcd f1_cgsexg f2_cgsexg f0_cgsexg p_ancld f1_cgsexg f2_cgsexg f2_cgsexg f0_cgsexg a_wa f3_cgsexg p_eximdv f4_cgsexg f5_cgsexg a_wcel f2_cgsexg f3_cgsexg a_wex f1_cgsexg f2_cgsexg f0_cgsexg a_wa f3_cgsexg a_wex p_syl5com f4_cgsexg f5_cgsexg a_wcel f2_cgsexg f0_cgsexg a_wa f3_cgsexg a_wex f1_cgsexg p_impbid2 $.
$}

$(Implicit substitution inference for general classes.  (Contributed by
       NM, 26-Jul-1995.) $)

${
	$v ph ps ch x y A B V W  $.
	$d x y ps  $.
	$d x y A  $.
	$d x y B  $.
	f0_cgsex2g $f wff ph $.
	f1_cgsex2g $f wff ps $.
	f2_cgsex2g $f wff ch $.
	f3_cgsex2g $f set x $.
	f4_cgsex2g $f set y $.
	f5_cgsex2g $f class A $.
	f6_cgsex2g $f class B $.
	f7_cgsex2g $f class V $.
	f8_cgsex2g $f class W $.
	e0_cgsex2g $e |- ( ( x = A /\ y = B ) -> ch ) $.
	e1_cgsex2g $e |- ( ch -> ( ph <-> ps ) ) $.
	p_cgsex2g $p |- ( ( A e. V /\ B e. W ) -> ( E. x E. y ( ch /\ ph ) <-> ps ) ) $= e1_cgsex2g f2_cgsex2g f0_cgsex2g f1_cgsex2g p_biimpa f2_cgsex2g f0_cgsex2g a_wa f1_cgsex2g f3_cgsex2g f4_cgsex2g p_exlimivv f3_cgsex2g f5_cgsex2g f7_cgsex2g p_elisset f4_cgsex2g f6_cgsex2g f8_cgsex2g p_elisset f5_cgsex2g f7_cgsex2g a_wcel f3_cgsex2g a_sup_set_class f5_cgsex2g a_wceq f3_cgsex2g a_wex f6_cgsex2g f8_cgsex2g a_wcel f4_cgsex2g a_sup_set_class f6_cgsex2g a_wceq f4_cgsex2g a_wex p_anim12i f3_cgsex2g a_sup_set_class f5_cgsex2g a_wceq f4_cgsex2g a_sup_set_class f6_cgsex2g a_wceq f3_cgsex2g f4_cgsex2g p_eeanv f5_cgsex2g f7_cgsex2g a_wcel f6_cgsex2g f8_cgsex2g a_wcel a_wa f3_cgsex2g a_sup_set_class f5_cgsex2g a_wceq f3_cgsex2g a_wex f4_cgsex2g a_sup_set_class f6_cgsex2g a_wceq f4_cgsex2g a_wex a_wa f3_cgsex2g a_sup_set_class f5_cgsex2g a_wceq f4_cgsex2g a_sup_set_class f6_cgsex2g a_wceq a_wa f4_cgsex2g a_wex f3_cgsex2g a_wex p_sylibr e0_cgsex2g f3_cgsex2g a_sup_set_class f5_cgsex2g a_wceq f4_cgsex2g a_sup_set_class f6_cgsex2g a_wceq a_wa f2_cgsex2g f3_cgsex2g f4_cgsex2g p_2eximi f5_cgsex2g f7_cgsex2g a_wcel f6_cgsex2g f8_cgsex2g a_wcel a_wa f3_cgsex2g a_sup_set_class f5_cgsex2g a_wceq f4_cgsex2g a_sup_set_class f6_cgsex2g a_wceq a_wa f4_cgsex2g a_wex f3_cgsex2g a_wex f2_cgsex2g f4_cgsex2g a_wex f3_cgsex2g a_wex p_syl e1_cgsex2g f2_cgsex2g f0_cgsex2g f1_cgsex2g p_biimprcd f1_cgsex2g f2_cgsex2g f0_cgsex2g p_ancld f1_cgsex2g f2_cgsex2g f2_cgsex2g f0_cgsex2g a_wa f3_cgsex2g f4_cgsex2g p_2eximdv f5_cgsex2g f7_cgsex2g a_wcel f6_cgsex2g f8_cgsex2g a_wcel a_wa f2_cgsex2g f4_cgsex2g a_wex f3_cgsex2g a_wex f1_cgsex2g f2_cgsex2g f0_cgsex2g a_wa f4_cgsex2g a_wex f3_cgsex2g a_wex p_syl5com f5_cgsex2g f7_cgsex2g a_wcel f6_cgsex2g f8_cgsex2g a_wcel a_wa f2_cgsex2g f0_cgsex2g a_wa f4_cgsex2g a_wex f3_cgsex2g a_wex f1_cgsex2g p_impbid2 $.
$}

$(An implicit substitution inference for 4 general classes.  (Contributed
       by NM, 5-Aug-1995.) $)

${
	$v ph ps ch x y z w A B C D R S  $.
	$d x y z w A  $.
	$d x y z w B  $.
	$d x y z w C  $.
	$d x y z w D  $.
	$d x y z w ps  $.
	f0_cgsex4g $f wff ph $.
	f1_cgsex4g $f wff ps $.
	f2_cgsex4g $f wff ch $.
	f3_cgsex4g $f set x $.
	f4_cgsex4g $f set y $.
	f5_cgsex4g $f set z $.
	f6_cgsex4g $f set w $.
	f7_cgsex4g $f class A $.
	f8_cgsex4g $f class B $.
	f9_cgsex4g $f class C $.
	f10_cgsex4g $f class D $.
	f11_cgsex4g $f class R $.
	f12_cgsex4g $f class S $.
	e0_cgsex4g $e |- ( ( ( x = A /\ y = B ) /\ ( z = C /\ w = D ) ) -> ch ) $.
	e1_cgsex4g $e |- ( ch -> ( ph <-> ps ) ) $.
	p_cgsex4g $p |- ( ( ( A e. R /\ B e. S ) /\ ( C e. R /\ D e. S ) ) -> ( E. x E. y E. z E. w ( ch /\ ph ) <-> ps ) ) $= e1_cgsex4g f2_cgsex4g f0_cgsex4g f1_cgsex4g p_biimpa f2_cgsex4g f0_cgsex4g a_wa f1_cgsex4g f5_cgsex4g f6_cgsex4g p_exlimivv f2_cgsex4g f0_cgsex4g a_wa f6_cgsex4g a_wex f5_cgsex4g a_wex f1_cgsex4g f3_cgsex4g f4_cgsex4g p_exlimivv f3_cgsex4g f7_cgsex4g f11_cgsex4g p_elisset f4_cgsex4g f8_cgsex4g f12_cgsex4g p_elisset f7_cgsex4g f11_cgsex4g a_wcel f3_cgsex4g a_sup_set_class f7_cgsex4g a_wceq f3_cgsex4g a_wex f8_cgsex4g f12_cgsex4g a_wcel f4_cgsex4g a_sup_set_class f8_cgsex4g a_wceq f4_cgsex4g a_wex p_anim12i f3_cgsex4g a_sup_set_class f7_cgsex4g a_wceq f4_cgsex4g a_sup_set_class f8_cgsex4g a_wceq f3_cgsex4g f4_cgsex4g p_eeanv f7_cgsex4g f11_cgsex4g a_wcel f8_cgsex4g f12_cgsex4g a_wcel a_wa f3_cgsex4g a_sup_set_class f7_cgsex4g a_wceq f3_cgsex4g a_wex f4_cgsex4g a_sup_set_class f8_cgsex4g a_wceq f4_cgsex4g a_wex a_wa f3_cgsex4g a_sup_set_class f7_cgsex4g a_wceq f4_cgsex4g a_sup_set_class f8_cgsex4g a_wceq a_wa f4_cgsex4g a_wex f3_cgsex4g a_wex p_sylibr f5_cgsex4g f9_cgsex4g f11_cgsex4g p_elisset f6_cgsex4g f10_cgsex4g f12_cgsex4g p_elisset f9_cgsex4g f11_cgsex4g a_wcel f5_cgsex4g a_sup_set_class f9_cgsex4g a_wceq f5_cgsex4g a_wex f10_cgsex4g f12_cgsex4g a_wcel f6_cgsex4g a_sup_set_class f10_cgsex4g a_wceq f6_cgsex4g a_wex p_anim12i f5_cgsex4g a_sup_set_class f9_cgsex4g a_wceq f6_cgsex4g a_sup_set_class f10_cgsex4g a_wceq f5_cgsex4g f6_cgsex4g p_eeanv f9_cgsex4g f11_cgsex4g a_wcel f10_cgsex4g f12_cgsex4g a_wcel a_wa f5_cgsex4g a_sup_set_class f9_cgsex4g a_wceq f5_cgsex4g a_wex f6_cgsex4g a_sup_set_class f10_cgsex4g a_wceq f6_cgsex4g a_wex a_wa f5_cgsex4g a_sup_set_class f9_cgsex4g a_wceq f6_cgsex4g a_sup_set_class f10_cgsex4g a_wceq a_wa f6_cgsex4g a_wex f5_cgsex4g a_wex p_sylibr f7_cgsex4g f11_cgsex4g a_wcel f8_cgsex4g f12_cgsex4g a_wcel a_wa f3_cgsex4g a_sup_set_class f7_cgsex4g a_wceq f4_cgsex4g a_sup_set_class f8_cgsex4g a_wceq a_wa f4_cgsex4g a_wex f3_cgsex4g a_wex f9_cgsex4g f11_cgsex4g a_wcel f10_cgsex4g f12_cgsex4g a_wcel a_wa f5_cgsex4g a_sup_set_class f9_cgsex4g a_wceq f6_cgsex4g a_sup_set_class f10_cgsex4g a_wceq a_wa f6_cgsex4g a_wex f5_cgsex4g a_wex p_anim12i f3_cgsex4g a_sup_set_class f7_cgsex4g a_wceq f4_cgsex4g a_sup_set_class f8_cgsex4g a_wceq a_wa f5_cgsex4g a_sup_set_class f9_cgsex4g a_wceq f6_cgsex4g a_sup_set_class f10_cgsex4g a_wceq a_wa f3_cgsex4g f4_cgsex4g f5_cgsex4g f6_cgsex4g p_ee4anv f7_cgsex4g f11_cgsex4g a_wcel f8_cgsex4g f12_cgsex4g a_wcel a_wa f9_cgsex4g f11_cgsex4g a_wcel f10_cgsex4g f12_cgsex4g a_wcel a_wa a_wa f3_cgsex4g a_sup_set_class f7_cgsex4g a_wceq f4_cgsex4g a_sup_set_class f8_cgsex4g a_wceq a_wa f4_cgsex4g a_wex f3_cgsex4g a_wex f5_cgsex4g a_sup_set_class f9_cgsex4g a_wceq f6_cgsex4g a_sup_set_class f10_cgsex4g a_wceq a_wa f6_cgsex4g a_wex f5_cgsex4g a_wex a_wa f3_cgsex4g a_sup_set_class f7_cgsex4g a_wceq f4_cgsex4g a_sup_set_class f8_cgsex4g a_wceq a_wa f5_cgsex4g a_sup_set_class f9_cgsex4g a_wceq f6_cgsex4g a_sup_set_class f10_cgsex4g a_wceq a_wa a_wa f6_cgsex4g a_wex f5_cgsex4g a_wex f4_cgsex4g a_wex f3_cgsex4g a_wex p_sylibr e0_cgsex4g f3_cgsex4g a_sup_set_class f7_cgsex4g a_wceq f4_cgsex4g a_sup_set_class f8_cgsex4g a_wceq a_wa f5_cgsex4g a_sup_set_class f9_cgsex4g a_wceq f6_cgsex4g a_sup_set_class f10_cgsex4g a_wceq a_wa a_wa f2_cgsex4g f5_cgsex4g f6_cgsex4g p_2eximi f3_cgsex4g a_sup_set_class f7_cgsex4g a_wceq f4_cgsex4g a_sup_set_class f8_cgsex4g a_wceq a_wa f5_cgsex4g a_sup_set_class f9_cgsex4g a_wceq f6_cgsex4g a_sup_set_class f10_cgsex4g a_wceq a_wa a_wa f6_cgsex4g a_wex f5_cgsex4g a_wex f2_cgsex4g f6_cgsex4g a_wex f5_cgsex4g a_wex f3_cgsex4g f4_cgsex4g p_2eximi f7_cgsex4g f11_cgsex4g a_wcel f8_cgsex4g f12_cgsex4g a_wcel a_wa f9_cgsex4g f11_cgsex4g a_wcel f10_cgsex4g f12_cgsex4g a_wcel a_wa a_wa f3_cgsex4g a_sup_set_class f7_cgsex4g a_wceq f4_cgsex4g a_sup_set_class f8_cgsex4g a_wceq a_wa f5_cgsex4g a_sup_set_class f9_cgsex4g a_wceq f6_cgsex4g a_sup_set_class f10_cgsex4g a_wceq a_wa a_wa f6_cgsex4g a_wex f5_cgsex4g a_wex f4_cgsex4g a_wex f3_cgsex4g a_wex f2_cgsex4g f6_cgsex4g a_wex f5_cgsex4g a_wex f4_cgsex4g a_wex f3_cgsex4g a_wex p_syl e1_cgsex4g f2_cgsex4g f0_cgsex4g f1_cgsex4g p_biimprcd f1_cgsex4g f2_cgsex4g f0_cgsex4g p_ancld f1_cgsex4g f2_cgsex4g f2_cgsex4g f0_cgsex4g a_wa f5_cgsex4g f6_cgsex4g p_2eximdv f1_cgsex4g f2_cgsex4g f6_cgsex4g a_wex f5_cgsex4g a_wex f2_cgsex4g f0_cgsex4g a_wa f6_cgsex4g a_wex f5_cgsex4g a_wex f3_cgsex4g f4_cgsex4g p_2eximdv f7_cgsex4g f11_cgsex4g a_wcel f8_cgsex4g f12_cgsex4g a_wcel a_wa f9_cgsex4g f11_cgsex4g a_wcel f10_cgsex4g f12_cgsex4g a_wcel a_wa a_wa f2_cgsex4g f6_cgsex4g a_wex f5_cgsex4g a_wex f4_cgsex4g a_wex f3_cgsex4g a_wex f1_cgsex4g f2_cgsex4g f0_cgsex4g a_wa f6_cgsex4g a_wex f5_cgsex4g a_wex f4_cgsex4g a_wex f3_cgsex4g a_wex p_syl5com f7_cgsex4g f11_cgsex4g a_wcel f8_cgsex4g f12_cgsex4g a_wcel a_wa f9_cgsex4g f11_cgsex4g a_wcel f10_cgsex4g f12_cgsex4g a_wcel a_wa a_wa f2_cgsex4g f0_cgsex4g a_wa f6_cgsex4g a_wex f5_cgsex4g a_wex f4_cgsex4g a_wex f3_cgsex4g a_wex f1_cgsex4g p_impbid2 $.
$}

$(Elimination of an existential quantifier, using implicit substitution.
       (Contributed by NM, 2-Mar-1995.)  (Revised by Mario Carneiro,
       10-Oct-2016.) $)

${
	$v ph ps x A  $.
	$d x A  $.
	f0_ceqsex $f wff ph $.
	f1_ceqsex $f wff ps $.
	f2_ceqsex $f set x $.
	f3_ceqsex $f class A $.
	e0_ceqsex $e |- F/ x ps $.
	e1_ceqsex $e |- A e. _V $.
	e2_ceqsex $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_ceqsex $p |- ( E. x ( x = A /\ ph ) <-> ps ) $= e0_ceqsex e2_ceqsex f2_ceqsex a_sup_set_class f3_ceqsex a_wceq f0_ceqsex f1_ceqsex p_biimpa f2_ceqsex a_sup_set_class f3_ceqsex a_wceq f0_ceqsex a_wa f1_ceqsex f2_ceqsex p_exlimi e0_ceqsex e2_ceqsex f2_ceqsex a_sup_set_class f3_ceqsex a_wceq f0_ceqsex f1_ceqsex p_biimprcd f1_ceqsex f2_ceqsex a_sup_set_class f3_ceqsex a_wceq f0_ceqsex a_wi f2_ceqsex p_alrimi e1_ceqsex f2_ceqsex f3_ceqsex p_isseti f2_ceqsex a_sup_set_class f3_ceqsex a_wceq f0_ceqsex f2_ceqsex p_exintr f1_ceqsex f2_ceqsex a_sup_set_class f3_ceqsex a_wceq f0_ceqsex a_wi f2_ceqsex a_wal f2_ceqsex a_sup_set_class f3_ceqsex a_wceq f2_ceqsex a_wex f2_ceqsex a_sup_set_class f3_ceqsex a_wceq f0_ceqsex a_wa f2_ceqsex a_wex p_ee10 f2_ceqsex a_sup_set_class f3_ceqsex a_wceq f0_ceqsex a_wa f2_ceqsex a_wex f1_ceqsex p_impbii $.
$}

$(Elimination of an existential quantifier, using implicit substitution.
       (Contributed by NM, 2-Mar-1995.) $)

${
	$v ph ps x A  $.
	$d x A  $.
	$d x ps  $.
	f0_ceqsexv $f wff ph $.
	f1_ceqsexv $f wff ps $.
	f2_ceqsexv $f set x $.
	f3_ceqsexv $f class A $.
	e0_ceqsexv $e |- A e. _V $.
	e1_ceqsexv $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_ceqsexv $p |- ( E. x ( x = A /\ ph ) <-> ps ) $= f1_ceqsexv f2_ceqsexv p_nfv e0_ceqsexv e1_ceqsexv f0_ceqsexv f1_ceqsexv f2_ceqsexv f3_ceqsexv p_ceqsex $.
$}

$(Elimination of two existential quantifiers, using implicit
       substitution.  (Contributed by Scott Fenton, 7-Jun-2006.) $)

${
	$v ph ps ch x y A B  $.
	$d x y A  $.
	$d x y B  $.
	f0_ceqsex2 $f wff ph $.
	f1_ceqsex2 $f wff ps $.
	f2_ceqsex2 $f wff ch $.
	f3_ceqsex2 $f set x $.
	f4_ceqsex2 $f set y $.
	f5_ceqsex2 $f class A $.
	f6_ceqsex2 $f class B $.
	e0_ceqsex2 $e |- F/ x ps $.
	e1_ceqsex2 $e |- F/ y ch $.
	e2_ceqsex2 $e |- A e. _V $.
	e3_ceqsex2 $e |- B e. _V $.
	e4_ceqsex2 $e |- ( x = A -> ( ph <-> ps ) ) $.
	e5_ceqsex2 $e |- ( y = B -> ( ps <-> ch ) ) $.
	p_ceqsex2 $p |- ( E. x E. y ( x = A /\ y = B /\ ph ) <-> ch ) $= f3_ceqsex2 a_sup_set_class f5_ceqsex2 a_wceq f4_ceqsex2 a_sup_set_class f6_ceqsex2 a_wceq f0_ceqsex2 p_3anass f3_ceqsex2 a_sup_set_class f5_ceqsex2 a_wceq f4_ceqsex2 a_sup_set_class f6_ceqsex2 a_wceq f0_ceqsex2 a_w3a f3_ceqsex2 a_sup_set_class f5_ceqsex2 a_wceq f4_ceqsex2 a_sup_set_class f6_ceqsex2 a_wceq f0_ceqsex2 a_wa a_wa f4_ceqsex2 p_exbii f3_ceqsex2 a_sup_set_class f5_ceqsex2 a_wceq f4_ceqsex2 a_sup_set_class f6_ceqsex2 a_wceq f0_ceqsex2 a_wa f4_ceqsex2 p_19.42v f3_ceqsex2 a_sup_set_class f5_ceqsex2 a_wceq f4_ceqsex2 a_sup_set_class f6_ceqsex2 a_wceq f0_ceqsex2 a_w3a f4_ceqsex2 a_wex f3_ceqsex2 a_sup_set_class f5_ceqsex2 a_wceq f4_ceqsex2 a_sup_set_class f6_ceqsex2 a_wceq f0_ceqsex2 a_wa a_wa f4_ceqsex2 a_wex f3_ceqsex2 a_sup_set_class f5_ceqsex2 a_wceq f4_ceqsex2 a_sup_set_class f6_ceqsex2 a_wceq f0_ceqsex2 a_wa f4_ceqsex2 a_wex a_wa p_bitri f3_ceqsex2 a_sup_set_class f5_ceqsex2 a_wceq f4_ceqsex2 a_sup_set_class f6_ceqsex2 a_wceq f0_ceqsex2 a_w3a f4_ceqsex2 a_wex f3_ceqsex2 a_sup_set_class f5_ceqsex2 a_wceq f4_ceqsex2 a_sup_set_class f6_ceqsex2 a_wceq f0_ceqsex2 a_wa f4_ceqsex2 a_wex a_wa f3_ceqsex2 p_exbii f4_ceqsex2 a_sup_set_class f6_ceqsex2 a_wceq f3_ceqsex2 p_nfv e0_ceqsex2 f4_ceqsex2 a_sup_set_class f6_ceqsex2 a_wceq f1_ceqsex2 f3_ceqsex2 p_nfan f4_ceqsex2 a_sup_set_class f6_ceqsex2 a_wceq f1_ceqsex2 a_wa f3_ceqsex2 f4_ceqsex2 p_nfex e2_ceqsex2 e4_ceqsex2 f3_ceqsex2 a_sup_set_class f5_ceqsex2 a_wceq f0_ceqsex2 f1_ceqsex2 f4_ceqsex2 a_sup_set_class f6_ceqsex2 a_wceq p_anbi2d f3_ceqsex2 a_sup_set_class f5_ceqsex2 a_wceq f4_ceqsex2 a_sup_set_class f6_ceqsex2 a_wceq f0_ceqsex2 a_wa f4_ceqsex2 a_sup_set_class f6_ceqsex2 a_wceq f1_ceqsex2 a_wa f4_ceqsex2 p_exbidv f4_ceqsex2 a_sup_set_class f6_ceqsex2 a_wceq f0_ceqsex2 a_wa f4_ceqsex2 a_wex f4_ceqsex2 a_sup_set_class f6_ceqsex2 a_wceq f1_ceqsex2 a_wa f4_ceqsex2 a_wex f3_ceqsex2 f5_ceqsex2 p_ceqsex e1_ceqsex2 e3_ceqsex2 e5_ceqsex2 f1_ceqsex2 f2_ceqsex2 f4_ceqsex2 f6_ceqsex2 p_ceqsex f3_ceqsex2 a_sup_set_class f5_ceqsex2 a_wceq f4_ceqsex2 a_sup_set_class f6_ceqsex2 a_wceq f0_ceqsex2 a_w3a f4_ceqsex2 a_wex f3_ceqsex2 a_wex f3_ceqsex2 a_sup_set_class f5_ceqsex2 a_wceq f4_ceqsex2 a_sup_set_class f6_ceqsex2 a_wceq f0_ceqsex2 a_wa f4_ceqsex2 a_wex a_wa f3_ceqsex2 a_wex f4_ceqsex2 a_sup_set_class f6_ceqsex2 a_wceq f1_ceqsex2 a_wa f4_ceqsex2 a_wex f2_ceqsex2 p_3bitri $.
$}

$(Elimination of two existential quantifiers, using implicit
       substitution.  (Contributed by Scott Fenton, 7-Jun-2006.) $)

${
	$v ph ps ch x y A B  $.
	$d x y A  $.
	$d x y B  $.
	$d x ps  $.
	$d y ch  $.
	f0_ceqsex2v $f wff ph $.
	f1_ceqsex2v $f wff ps $.
	f2_ceqsex2v $f wff ch $.
	f3_ceqsex2v $f set x $.
	f4_ceqsex2v $f set y $.
	f5_ceqsex2v $f class A $.
	f6_ceqsex2v $f class B $.
	e0_ceqsex2v $e |- A e. _V $.
	e1_ceqsex2v $e |- B e. _V $.
	e2_ceqsex2v $e |- ( x = A -> ( ph <-> ps ) ) $.
	e3_ceqsex2v $e |- ( y = B -> ( ps <-> ch ) ) $.
	p_ceqsex2v $p |- ( E. x E. y ( x = A /\ y = B /\ ph ) <-> ch ) $= f1_ceqsex2v f3_ceqsex2v p_nfv f2_ceqsex2v f4_ceqsex2v p_nfv e0_ceqsex2v e1_ceqsex2v e2_ceqsex2v e3_ceqsex2v f0_ceqsex2v f1_ceqsex2v f2_ceqsex2v f3_ceqsex2v f4_ceqsex2v f5_ceqsex2v f6_ceqsex2v p_ceqsex2 $.
$}

$(Elimination of three existential quantifiers, using implicit
       substitution.  (Contributed by NM, 16-Aug-2011.) $)

${
	$v ph ps ch th x y z A B C  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x ps  $.
	$d y ch  $.
	$d z th  $.
	f0_ceqsex3v $f wff ph $.
	f1_ceqsex3v $f wff ps $.
	f2_ceqsex3v $f wff ch $.
	f3_ceqsex3v $f wff th $.
	f4_ceqsex3v $f set x $.
	f5_ceqsex3v $f set y $.
	f6_ceqsex3v $f set z $.
	f7_ceqsex3v $f class A $.
	f8_ceqsex3v $f class B $.
	f9_ceqsex3v $f class C $.
	e0_ceqsex3v $e |- A e. _V $.
	e1_ceqsex3v $e |- B e. _V $.
	e2_ceqsex3v $e |- C e. _V $.
	e3_ceqsex3v $e |- ( x = A -> ( ph <-> ps ) ) $.
	e4_ceqsex3v $e |- ( y = B -> ( ps <-> ch ) ) $.
	e5_ceqsex3v $e |- ( z = C -> ( ch <-> th ) ) $.
	p_ceqsex3v $p |- ( E. x E. y E. z ( ( x = A /\ y = B /\ z = C ) /\ ph ) <-> th ) $= f4_ceqsex3v a_sup_set_class f7_ceqsex3v a_wceq f5_ceqsex3v a_sup_set_class f8_ceqsex3v a_wceq f6_ceqsex3v a_sup_set_class f9_ceqsex3v a_wceq a_wa f0_ceqsex3v p_anass f4_ceqsex3v a_sup_set_class f7_ceqsex3v a_wceq f5_ceqsex3v a_sup_set_class f8_ceqsex3v a_wceq f6_ceqsex3v a_sup_set_class f9_ceqsex3v a_wceq p_3anass f4_ceqsex3v a_sup_set_class f7_ceqsex3v a_wceq f5_ceqsex3v a_sup_set_class f8_ceqsex3v a_wceq f6_ceqsex3v a_sup_set_class f9_ceqsex3v a_wceq a_w3a f4_ceqsex3v a_sup_set_class f7_ceqsex3v a_wceq f5_ceqsex3v a_sup_set_class f8_ceqsex3v a_wceq f6_ceqsex3v a_sup_set_class f9_ceqsex3v a_wceq a_wa a_wa f0_ceqsex3v p_anbi1i f5_ceqsex3v a_sup_set_class f8_ceqsex3v a_wceq f6_ceqsex3v a_sup_set_class f9_ceqsex3v a_wceq f0_ceqsex3v a_df-3an f5_ceqsex3v a_sup_set_class f8_ceqsex3v a_wceq f6_ceqsex3v a_sup_set_class f9_ceqsex3v a_wceq f0_ceqsex3v a_w3a f5_ceqsex3v a_sup_set_class f8_ceqsex3v a_wceq f6_ceqsex3v a_sup_set_class f9_ceqsex3v a_wceq a_wa f0_ceqsex3v a_wa f4_ceqsex3v a_sup_set_class f7_ceqsex3v a_wceq p_anbi2i f4_ceqsex3v a_sup_set_class f7_ceqsex3v a_wceq f5_ceqsex3v a_sup_set_class f8_ceqsex3v a_wceq f6_ceqsex3v a_sup_set_class f9_ceqsex3v a_wceq a_wa a_wa f0_ceqsex3v a_wa f4_ceqsex3v a_sup_set_class f7_ceqsex3v a_wceq f5_ceqsex3v a_sup_set_class f8_ceqsex3v a_wceq f6_ceqsex3v a_sup_set_class f9_ceqsex3v a_wceq a_wa f0_ceqsex3v a_wa a_wa f4_ceqsex3v a_sup_set_class f7_ceqsex3v a_wceq f5_ceqsex3v a_sup_set_class f8_ceqsex3v a_wceq f6_ceqsex3v a_sup_set_class f9_ceqsex3v a_wceq a_w3a f0_ceqsex3v a_wa f4_ceqsex3v a_sup_set_class f7_ceqsex3v a_wceq f5_ceqsex3v a_sup_set_class f8_ceqsex3v a_wceq f6_ceqsex3v a_sup_set_class f9_ceqsex3v a_wceq f0_ceqsex3v a_w3a a_wa p_3bitr4i f4_ceqsex3v a_sup_set_class f7_ceqsex3v a_wceq f5_ceqsex3v a_sup_set_class f8_ceqsex3v a_wceq f6_ceqsex3v a_sup_set_class f9_ceqsex3v a_wceq a_w3a f0_ceqsex3v a_wa f4_ceqsex3v a_sup_set_class f7_ceqsex3v a_wceq f5_ceqsex3v a_sup_set_class f8_ceqsex3v a_wceq f6_ceqsex3v a_sup_set_class f9_ceqsex3v a_wceq f0_ceqsex3v a_w3a a_wa f5_ceqsex3v f6_ceqsex3v p_2exbii f4_ceqsex3v a_sup_set_class f7_ceqsex3v a_wceq f5_ceqsex3v a_sup_set_class f8_ceqsex3v a_wceq f6_ceqsex3v a_sup_set_class f9_ceqsex3v a_wceq f0_ceqsex3v a_w3a f5_ceqsex3v f6_ceqsex3v p_19.42vv f4_ceqsex3v a_sup_set_class f7_ceqsex3v a_wceq f5_ceqsex3v a_sup_set_class f8_ceqsex3v a_wceq f6_ceqsex3v a_sup_set_class f9_ceqsex3v a_wceq a_w3a f0_ceqsex3v a_wa f6_ceqsex3v a_wex f5_ceqsex3v a_wex f4_ceqsex3v a_sup_set_class f7_ceqsex3v a_wceq f5_ceqsex3v a_sup_set_class f8_ceqsex3v a_wceq f6_ceqsex3v a_sup_set_class f9_ceqsex3v a_wceq f0_ceqsex3v a_w3a a_wa f6_ceqsex3v a_wex f5_ceqsex3v a_wex f4_ceqsex3v a_sup_set_class f7_ceqsex3v a_wceq f5_ceqsex3v a_sup_set_class f8_ceqsex3v a_wceq f6_ceqsex3v a_sup_set_class f9_ceqsex3v a_wceq f0_ceqsex3v a_w3a f6_ceqsex3v a_wex f5_ceqsex3v a_wex a_wa p_bitri f4_ceqsex3v a_sup_set_class f7_ceqsex3v a_wceq f5_ceqsex3v a_sup_set_class f8_ceqsex3v a_wceq f6_ceqsex3v a_sup_set_class f9_ceqsex3v a_wceq a_w3a f0_ceqsex3v a_wa f6_ceqsex3v a_wex f5_ceqsex3v a_wex f4_ceqsex3v a_sup_set_class f7_ceqsex3v a_wceq f5_ceqsex3v a_sup_set_class f8_ceqsex3v a_wceq f6_ceqsex3v a_sup_set_class f9_ceqsex3v a_wceq f0_ceqsex3v a_w3a f6_ceqsex3v a_wex f5_ceqsex3v a_wex a_wa f4_ceqsex3v p_exbii e0_ceqsex3v e3_ceqsex3v f4_ceqsex3v a_sup_set_class f7_ceqsex3v a_wceq f0_ceqsex3v f1_ceqsex3v f5_ceqsex3v a_sup_set_class f8_ceqsex3v a_wceq f6_ceqsex3v a_sup_set_class f9_ceqsex3v a_wceq p_3anbi3d f4_ceqsex3v a_sup_set_class f7_ceqsex3v a_wceq f5_ceqsex3v a_sup_set_class f8_ceqsex3v a_wceq f6_ceqsex3v a_sup_set_class f9_ceqsex3v a_wceq f0_ceqsex3v a_w3a f5_ceqsex3v a_sup_set_class f8_ceqsex3v a_wceq f6_ceqsex3v a_sup_set_class f9_ceqsex3v a_wceq f1_ceqsex3v a_w3a f5_ceqsex3v f6_ceqsex3v p_2exbidv f5_ceqsex3v a_sup_set_class f8_ceqsex3v a_wceq f6_ceqsex3v a_sup_set_class f9_ceqsex3v a_wceq f0_ceqsex3v a_w3a f6_ceqsex3v a_wex f5_ceqsex3v a_wex f5_ceqsex3v a_sup_set_class f8_ceqsex3v a_wceq f6_ceqsex3v a_sup_set_class f9_ceqsex3v a_wceq f1_ceqsex3v a_w3a f6_ceqsex3v a_wex f5_ceqsex3v a_wex f4_ceqsex3v f7_ceqsex3v p_ceqsexv e1_ceqsex3v e2_ceqsex3v e4_ceqsex3v e5_ceqsex3v f1_ceqsex3v f2_ceqsex3v f3_ceqsex3v f5_ceqsex3v f6_ceqsex3v f8_ceqsex3v f9_ceqsex3v p_ceqsex2v f4_ceqsex3v a_sup_set_class f7_ceqsex3v a_wceq f5_ceqsex3v a_sup_set_class f8_ceqsex3v a_wceq f6_ceqsex3v a_sup_set_class f9_ceqsex3v a_wceq f0_ceqsex3v a_w3a f6_ceqsex3v a_wex f5_ceqsex3v a_wex a_wa f4_ceqsex3v a_wex f5_ceqsex3v a_sup_set_class f8_ceqsex3v a_wceq f6_ceqsex3v a_sup_set_class f9_ceqsex3v a_wceq f1_ceqsex3v a_w3a f6_ceqsex3v a_wex f5_ceqsex3v a_wex f3_ceqsex3v p_bitri f4_ceqsex3v a_sup_set_class f7_ceqsex3v a_wceq f5_ceqsex3v a_sup_set_class f8_ceqsex3v a_wceq f6_ceqsex3v a_sup_set_class f9_ceqsex3v a_wceq a_w3a f0_ceqsex3v a_wa f6_ceqsex3v a_wex f5_ceqsex3v a_wex f4_ceqsex3v a_wex f4_ceqsex3v a_sup_set_class f7_ceqsex3v a_wceq f5_ceqsex3v a_sup_set_class f8_ceqsex3v a_wceq f6_ceqsex3v a_sup_set_class f9_ceqsex3v a_wceq f0_ceqsex3v a_w3a f6_ceqsex3v a_wex f5_ceqsex3v a_wex a_wa f4_ceqsex3v a_wex f3_ceqsex3v p_bitri $.
$}

$(Elimination of four existential quantifiers, using implicit
       substitution.  (Contributed by NM, 23-Sep-2011.) $)

${
	$v ph ps ch th ta x y z w A B C D  $.
	$d x y z w A  $.
	$d x y z w B  $.
	$d x y z w C  $.
	$d x y z w D  $.
	$d x ps  $.
	$d y ch  $.
	$d z th  $.
	$d w ta  $.
	f0_ceqsex4v $f wff ph $.
	f1_ceqsex4v $f wff ps $.
	f2_ceqsex4v $f wff ch $.
	f3_ceqsex4v $f wff th $.
	f4_ceqsex4v $f wff ta $.
	f5_ceqsex4v $f set x $.
	f6_ceqsex4v $f set y $.
	f7_ceqsex4v $f set z $.
	f8_ceqsex4v $f set w $.
	f9_ceqsex4v $f class A $.
	f10_ceqsex4v $f class B $.
	f11_ceqsex4v $f class C $.
	f12_ceqsex4v $f class D $.
	e0_ceqsex4v $e |- A e. _V $.
	e1_ceqsex4v $e |- B e. _V $.
	e2_ceqsex4v $e |- C e. _V $.
	e3_ceqsex4v $e |- D e. _V $.
	e4_ceqsex4v $e |- ( x = A -> ( ph <-> ps ) ) $.
	e5_ceqsex4v $e |- ( y = B -> ( ps <-> ch ) ) $.
	e6_ceqsex4v $e |- ( z = C -> ( ch <-> th ) ) $.
	e7_ceqsex4v $e |- ( w = D -> ( th <-> ta ) ) $.
	p_ceqsex4v $p |- ( E. x E. y E. z E. w ( ( x = A /\ y = B ) /\ ( z = C /\ w = D ) /\ ph ) <-> ta ) $= f5_ceqsex4v a_sup_set_class f9_ceqsex4v a_wceq f6_ceqsex4v a_sup_set_class f10_ceqsex4v a_wceq a_wa f7_ceqsex4v a_sup_set_class f11_ceqsex4v a_wceq f8_ceqsex4v a_sup_set_class f12_ceqsex4v a_wceq f0_ceqsex4v a_w3a f7_ceqsex4v f8_ceqsex4v p_19.42vv f5_ceqsex4v a_sup_set_class f9_ceqsex4v a_wceq f6_ceqsex4v a_sup_set_class f10_ceqsex4v a_wceq a_wa f7_ceqsex4v a_sup_set_class f11_ceqsex4v a_wceq f8_ceqsex4v a_sup_set_class f12_ceqsex4v a_wceq a_wa f0_ceqsex4v p_3anass f7_ceqsex4v a_sup_set_class f11_ceqsex4v a_wceq f8_ceqsex4v a_sup_set_class f12_ceqsex4v a_wceq f0_ceqsex4v a_df-3an f7_ceqsex4v a_sup_set_class f11_ceqsex4v a_wceq f8_ceqsex4v a_sup_set_class f12_ceqsex4v a_wceq f0_ceqsex4v a_w3a f7_ceqsex4v a_sup_set_class f11_ceqsex4v a_wceq f8_ceqsex4v a_sup_set_class f12_ceqsex4v a_wceq a_wa f0_ceqsex4v a_wa f5_ceqsex4v a_sup_set_class f9_ceqsex4v a_wceq f6_ceqsex4v a_sup_set_class f10_ceqsex4v a_wceq a_wa p_anbi2i f5_ceqsex4v a_sup_set_class f9_ceqsex4v a_wceq f6_ceqsex4v a_sup_set_class f10_ceqsex4v a_wceq a_wa f7_ceqsex4v a_sup_set_class f11_ceqsex4v a_wceq f8_ceqsex4v a_sup_set_class f12_ceqsex4v a_wceq a_wa f0_ceqsex4v a_w3a f5_ceqsex4v a_sup_set_class f9_ceqsex4v a_wceq f6_ceqsex4v a_sup_set_class f10_ceqsex4v a_wceq a_wa f7_ceqsex4v a_sup_set_class f11_ceqsex4v a_wceq f8_ceqsex4v a_sup_set_class f12_ceqsex4v a_wceq a_wa f0_ceqsex4v a_wa a_wa f5_ceqsex4v a_sup_set_class f9_ceqsex4v a_wceq f6_ceqsex4v a_sup_set_class f10_ceqsex4v a_wceq a_wa f7_ceqsex4v a_sup_set_class f11_ceqsex4v a_wceq f8_ceqsex4v a_sup_set_class f12_ceqsex4v a_wceq f0_ceqsex4v a_w3a a_wa p_bitr4i f5_ceqsex4v a_sup_set_class f9_ceqsex4v a_wceq f6_ceqsex4v a_sup_set_class f10_ceqsex4v a_wceq a_wa f7_ceqsex4v a_sup_set_class f11_ceqsex4v a_wceq f8_ceqsex4v a_sup_set_class f12_ceqsex4v a_wceq a_wa f0_ceqsex4v a_w3a f5_ceqsex4v a_sup_set_class f9_ceqsex4v a_wceq f6_ceqsex4v a_sup_set_class f10_ceqsex4v a_wceq a_wa f7_ceqsex4v a_sup_set_class f11_ceqsex4v a_wceq f8_ceqsex4v a_sup_set_class f12_ceqsex4v a_wceq f0_ceqsex4v a_w3a a_wa f7_ceqsex4v f8_ceqsex4v p_2exbii f5_ceqsex4v a_sup_set_class f9_ceqsex4v a_wceq f6_ceqsex4v a_sup_set_class f10_ceqsex4v a_wceq f7_ceqsex4v a_sup_set_class f11_ceqsex4v a_wceq f8_ceqsex4v a_sup_set_class f12_ceqsex4v a_wceq f0_ceqsex4v a_w3a f8_ceqsex4v a_wex f7_ceqsex4v a_wex a_df-3an f5_ceqsex4v a_sup_set_class f9_ceqsex4v a_wceq f6_ceqsex4v a_sup_set_class f10_ceqsex4v a_wceq a_wa f7_ceqsex4v a_sup_set_class f11_ceqsex4v a_wceq f8_ceqsex4v a_sup_set_class f12_ceqsex4v a_wceq f0_ceqsex4v a_w3a a_wa f8_ceqsex4v a_wex f7_ceqsex4v a_wex f5_ceqsex4v a_sup_set_class f9_ceqsex4v a_wceq f6_ceqsex4v a_sup_set_class f10_ceqsex4v a_wceq a_wa f7_ceqsex4v a_sup_set_class f11_ceqsex4v a_wceq f8_ceqsex4v a_sup_set_class f12_ceqsex4v a_wceq f0_ceqsex4v a_w3a f8_ceqsex4v a_wex f7_ceqsex4v a_wex a_wa f5_ceqsex4v a_sup_set_class f9_ceqsex4v a_wceq f6_ceqsex4v a_sup_set_class f10_ceqsex4v a_wceq a_wa f7_ceqsex4v a_sup_set_class f11_ceqsex4v a_wceq f8_ceqsex4v a_sup_set_class f12_ceqsex4v a_wceq a_wa f0_ceqsex4v a_w3a f8_ceqsex4v a_wex f7_ceqsex4v a_wex f5_ceqsex4v a_sup_set_class f9_ceqsex4v a_wceq f6_ceqsex4v a_sup_set_class f10_ceqsex4v a_wceq f7_ceqsex4v a_sup_set_class f11_ceqsex4v a_wceq f8_ceqsex4v a_sup_set_class f12_ceqsex4v a_wceq f0_ceqsex4v a_w3a f8_ceqsex4v a_wex f7_ceqsex4v a_wex a_w3a p_3bitr4i f5_ceqsex4v a_sup_set_class f9_ceqsex4v a_wceq f6_ceqsex4v a_sup_set_class f10_ceqsex4v a_wceq a_wa f7_ceqsex4v a_sup_set_class f11_ceqsex4v a_wceq f8_ceqsex4v a_sup_set_class f12_ceqsex4v a_wceq a_wa f0_ceqsex4v a_w3a f8_ceqsex4v a_wex f7_ceqsex4v a_wex f5_ceqsex4v a_sup_set_class f9_ceqsex4v a_wceq f6_ceqsex4v a_sup_set_class f10_ceqsex4v a_wceq f7_ceqsex4v a_sup_set_class f11_ceqsex4v a_wceq f8_ceqsex4v a_sup_set_class f12_ceqsex4v a_wceq f0_ceqsex4v a_w3a f8_ceqsex4v a_wex f7_ceqsex4v a_wex a_w3a f5_ceqsex4v f6_ceqsex4v p_2exbii e0_ceqsex4v e1_ceqsex4v e4_ceqsex4v f5_ceqsex4v a_sup_set_class f9_ceqsex4v a_wceq f0_ceqsex4v f1_ceqsex4v f7_ceqsex4v a_sup_set_class f11_ceqsex4v a_wceq f8_ceqsex4v a_sup_set_class f12_ceqsex4v a_wceq p_3anbi3d f5_ceqsex4v a_sup_set_class f9_ceqsex4v a_wceq f7_ceqsex4v a_sup_set_class f11_ceqsex4v a_wceq f8_ceqsex4v a_sup_set_class f12_ceqsex4v a_wceq f0_ceqsex4v a_w3a f7_ceqsex4v a_sup_set_class f11_ceqsex4v a_wceq f8_ceqsex4v a_sup_set_class f12_ceqsex4v a_wceq f1_ceqsex4v a_w3a f7_ceqsex4v f8_ceqsex4v p_2exbidv e5_ceqsex4v f6_ceqsex4v a_sup_set_class f10_ceqsex4v a_wceq f1_ceqsex4v f2_ceqsex4v f7_ceqsex4v a_sup_set_class f11_ceqsex4v a_wceq f8_ceqsex4v a_sup_set_class f12_ceqsex4v a_wceq p_3anbi3d f6_ceqsex4v a_sup_set_class f10_ceqsex4v a_wceq f7_ceqsex4v a_sup_set_class f11_ceqsex4v a_wceq f8_ceqsex4v a_sup_set_class f12_ceqsex4v a_wceq f1_ceqsex4v a_w3a f7_ceqsex4v a_sup_set_class f11_ceqsex4v a_wceq f8_ceqsex4v a_sup_set_class f12_ceqsex4v a_wceq f2_ceqsex4v a_w3a f7_ceqsex4v f8_ceqsex4v p_2exbidv f7_ceqsex4v a_sup_set_class f11_ceqsex4v a_wceq f8_ceqsex4v a_sup_set_class f12_ceqsex4v a_wceq f0_ceqsex4v a_w3a f8_ceqsex4v a_wex f7_ceqsex4v a_wex f7_ceqsex4v a_sup_set_class f11_ceqsex4v a_wceq f8_ceqsex4v a_sup_set_class f12_ceqsex4v a_wceq f1_ceqsex4v a_w3a f8_ceqsex4v a_wex f7_ceqsex4v a_wex f7_ceqsex4v a_sup_set_class f11_ceqsex4v a_wceq f8_ceqsex4v a_sup_set_class f12_ceqsex4v a_wceq f2_ceqsex4v a_w3a f8_ceqsex4v a_wex f7_ceqsex4v a_wex f5_ceqsex4v f6_ceqsex4v f9_ceqsex4v f10_ceqsex4v p_ceqsex2v e2_ceqsex4v e3_ceqsex4v e6_ceqsex4v e7_ceqsex4v f2_ceqsex4v f3_ceqsex4v f4_ceqsex4v f7_ceqsex4v f8_ceqsex4v f11_ceqsex4v f12_ceqsex4v p_ceqsex2v f5_ceqsex4v a_sup_set_class f9_ceqsex4v a_wceq f6_ceqsex4v a_sup_set_class f10_ceqsex4v a_wceq a_wa f7_ceqsex4v a_sup_set_class f11_ceqsex4v a_wceq f8_ceqsex4v a_sup_set_class f12_ceqsex4v a_wceq a_wa f0_ceqsex4v a_w3a f8_ceqsex4v a_wex f7_ceqsex4v a_wex f6_ceqsex4v a_wex f5_ceqsex4v a_wex f5_ceqsex4v a_sup_set_class f9_ceqsex4v a_wceq f6_ceqsex4v a_sup_set_class f10_ceqsex4v a_wceq f7_ceqsex4v a_sup_set_class f11_ceqsex4v a_wceq f8_ceqsex4v a_sup_set_class f12_ceqsex4v a_wceq f0_ceqsex4v a_w3a f8_ceqsex4v a_wex f7_ceqsex4v a_wex a_w3a f6_ceqsex4v a_wex f5_ceqsex4v a_wex f7_ceqsex4v a_sup_set_class f11_ceqsex4v a_wceq f8_ceqsex4v a_sup_set_class f12_ceqsex4v a_wceq f2_ceqsex4v a_w3a f8_ceqsex4v a_wex f7_ceqsex4v a_wex f4_ceqsex4v p_3bitri $.
$}

$(Elimination of six existential quantifiers, using implicit
       substitution.  (Contributed by NM, 21-Sep-2011.) $)

${
	$v ph ps ch th ta et ze x y z w v u A B C D E F  $.
	$d x y z w v u A  $.
	$d x y z w v u B  $.
	$d x y z w v u C  $.
	$d x y z w v u D  $.
	$d x y z w v u E  $.
	$d x y z w v u F  $.
	$d x ps  $.
	$d y ch  $.
	$d z th  $.
	$d w ta  $.
	$d v et  $.
	$d u ze  $.
	f0_ceqsex6v $f wff ph $.
	f1_ceqsex6v $f wff ps $.
	f2_ceqsex6v $f wff ch $.
	f3_ceqsex6v $f wff th $.
	f4_ceqsex6v $f wff ta $.
	f5_ceqsex6v $f wff et $.
	f6_ceqsex6v $f wff ze $.
	f7_ceqsex6v $f set x $.
	f8_ceqsex6v $f set y $.
	f9_ceqsex6v $f set z $.
	f10_ceqsex6v $f set w $.
	f11_ceqsex6v $f set v $.
	f12_ceqsex6v $f set u $.
	f13_ceqsex6v $f class A $.
	f14_ceqsex6v $f class B $.
	f15_ceqsex6v $f class C $.
	f16_ceqsex6v $f class D $.
	f17_ceqsex6v $f class E $.
	f18_ceqsex6v $f class F $.
	e0_ceqsex6v $e |- A e. _V $.
	e1_ceqsex6v $e |- B e. _V $.
	e2_ceqsex6v $e |- C e. _V $.
	e3_ceqsex6v $e |- D e. _V $.
	e4_ceqsex6v $e |- E e. _V $.
	e5_ceqsex6v $e |- F e. _V $.
	e6_ceqsex6v $e |- ( x = A -> ( ph <-> ps ) ) $.
	e7_ceqsex6v $e |- ( y = B -> ( ps <-> ch ) ) $.
	e8_ceqsex6v $e |- ( z = C -> ( ch <-> th ) ) $.
	e9_ceqsex6v $e |- ( w = D -> ( th <-> ta ) ) $.
	e10_ceqsex6v $e |- ( v = E -> ( ta <-> et ) ) $.
	e11_ceqsex6v $e |- ( u = F -> ( et <-> ze ) ) $.
	p_ceqsex6v $p |- ( E. x E. y E. z E. w E. v E. u ( ( x = A /\ y = B /\ z = C ) /\ ( w = D /\ v = E /\ u = F ) /\ ph ) <-> ze ) $= f7_ceqsex6v a_sup_set_class f13_ceqsex6v a_wceq f8_ceqsex6v a_sup_set_class f14_ceqsex6v a_wceq f9_ceqsex6v a_sup_set_class f15_ceqsex6v a_wceq a_w3a f10_ceqsex6v a_sup_set_class f16_ceqsex6v a_wceq f11_ceqsex6v a_sup_set_class f17_ceqsex6v a_wceq f12_ceqsex6v a_sup_set_class f18_ceqsex6v a_wceq a_w3a f0_ceqsex6v p_3anass f7_ceqsex6v a_sup_set_class f13_ceqsex6v a_wceq f8_ceqsex6v a_sup_set_class f14_ceqsex6v a_wceq f9_ceqsex6v a_sup_set_class f15_ceqsex6v a_wceq a_w3a f10_ceqsex6v a_sup_set_class f16_ceqsex6v a_wceq f11_ceqsex6v a_sup_set_class f17_ceqsex6v a_wceq f12_ceqsex6v a_sup_set_class f18_ceqsex6v a_wceq a_w3a f0_ceqsex6v a_w3a f7_ceqsex6v a_sup_set_class f13_ceqsex6v a_wceq f8_ceqsex6v a_sup_set_class f14_ceqsex6v a_wceq f9_ceqsex6v a_sup_set_class f15_ceqsex6v a_wceq a_w3a f10_ceqsex6v a_sup_set_class f16_ceqsex6v a_wceq f11_ceqsex6v a_sup_set_class f17_ceqsex6v a_wceq f12_ceqsex6v a_sup_set_class f18_ceqsex6v a_wceq a_w3a f0_ceqsex6v a_wa a_wa f10_ceqsex6v f11_ceqsex6v f12_ceqsex6v p_3exbii f7_ceqsex6v a_sup_set_class f13_ceqsex6v a_wceq f8_ceqsex6v a_sup_set_class f14_ceqsex6v a_wceq f9_ceqsex6v a_sup_set_class f15_ceqsex6v a_wceq a_w3a f10_ceqsex6v a_sup_set_class f16_ceqsex6v a_wceq f11_ceqsex6v a_sup_set_class f17_ceqsex6v a_wceq f12_ceqsex6v a_sup_set_class f18_ceqsex6v a_wceq a_w3a f0_ceqsex6v a_wa f10_ceqsex6v f11_ceqsex6v f12_ceqsex6v p_19.42vvv f7_ceqsex6v a_sup_set_class f13_ceqsex6v a_wceq f8_ceqsex6v a_sup_set_class f14_ceqsex6v a_wceq f9_ceqsex6v a_sup_set_class f15_ceqsex6v a_wceq a_w3a f10_ceqsex6v a_sup_set_class f16_ceqsex6v a_wceq f11_ceqsex6v a_sup_set_class f17_ceqsex6v a_wceq f12_ceqsex6v a_sup_set_class f18_ceqsex6v a_wceq a_w3a f0_ceqsex6v a_w3a f12_ceqsex6v a_wex f11_ceqsex6v a_wex f10_ceqsex6v a_wex f7_ceqsex6v a_sup_set_class f13_ceqsex6v a_wceq f8_ceqsex6v a_sup_set_class f14_ceqsex6v a_wceq f9_ceqsex6v a_sup_set_class f15_ceqsex6v a_wceq a_w3a f10_ceqsex6v a_sup_set_class f16_ceqsex6v a_wceq f11_ceqsex6v a_sup_set_class f17_ceqsex6v a_wceq f12_ceqsex6v a_sup_set_class f18_ceqsex6v a_wceq a_w3a f0_ceqsex6v a_wa a_wa f12_ceqsex6v a_wex f11_ceqsex6v a_wex f10_ceqsex6v a_wex f7_ceqsex6v a_sup_set_class f13_ceqsex6v a_wceq f8_ceqsex6v a_sup_set_class f14_ceqsex6v a_wceq f9_ceqsex6v a_sup_set_class f15_ceqsex6v a_wceq a_w3a f10_ceqsex6v a_sup_set_class f16_ceqsex6v a_wceq f11_ceqsex6v a_sup_set_class f17_ceqsex6v a_wceq f12_ceqsex6v a_sup_set_class f18_ceqsex6v a_wceq a_w3a f0_ceqsex6v a_wa f12_ceqsex6v a_wex f11_ceqsex6v a_wex f10_ceqsex6v a_wex a_wa p_bitri f7_ceqsex6v a_sup_set_class f13_ceqsex6v a_wceq f8_ceqsex6v a_sup_set_class f14_ceqsex6v a_wceq f9_ceqsex6v a_sup_set_class f15_ceqsex6v a_wceq a_w3a f10_ceqsex6v a_sup_set_class f16_ceqsex6v a_wceq f11_ceqsex6v a_sup_set_class f17_ceqsex6v a_wceq f12_ceqsex6v a_sup_set_class f18_ceqsex6v a_wceq a_w3a f0_ceqsex6v a_w3a f12_ceqsex6v a_wex f11_ceqsex6v a_wex f10_ceqsex6v a_wex f7_ceqsex6v a_sup_set_class f13_ceqsex6v a_wceq f8_ceqsex6v a_sup_set_class f14_ceqsex6v a_wceq f9_ceqsex6v a_sup_set_class f15_ceqsex6v a_wceq a_w3a f10_ceqsex6v a_sup_set_class f16_ceqsex6v a_wceq f11_ceqsex6v a_sup_set_class f17_ceqsex6v a_wceq f12_ceqsex6v a_sup_set_class f18_ceqsex6v a_wceq a_w3a f0_ceqsex6v a_wa f12_ceqsex6v a_wex f11_ceqsex6v a_wex f10_ceqsex6v a_wex a_wa f7_ceqsex6v f8_ceqsex6v f9_ceqsex6v p_3exbii e0_ceqsex6v e1_ceqsex6v e2_ceqsex6v e6_ceqsex6v f7_ceqsex6v a_sup_set_class f13_ceqsex6v a_wceq f0_ceqsex6v f1_ceqsex6v f10_ceqsex6v a_sup_set_class f16_ceqsex6v a_wceq f11_ceqsex6v a_sup_set_class f17_ceqsex6v a_wceq f12_ceqsex6v a_sup_set_class f18_ceqsex6v a_wceq a_w3a p_anbi2d f7_ceqsex6v a_sup_set_class f13_ceqsex6v a_wceq f10_ceqsex6v a_sup_set_class f16_ceqsex6v a_wceq f11_ceqsex6v a_sup_set_class f17_ceqsex6v a_wceq f12_ceqsex6v a_sup_set_class f18_ceqsex6v a_wceq a_w3a f0_ceqsex6v a_wa f10_ceqsex6v a_sup_set_class f16_ceqsex6v a_wceq f11_ceqsex6v a_sup_set_class f17_ceqsex6v a_wceq f12_ceqsex6v a_sup_set_class f18_ceqsex6v a_wceq a_w3a f1_ceqsex6v a_wa f10_ceqsex6v f11_ceqsex6v f12_ceqsex6v p_3exbidv e7_ceqsex6v f8_ceqsex6v a_sup_set_class f14_ceqsex6v a_wceq f1_ceqsex6v f2_ceqsex6v f10_ceqsex6v a_sup_set_class f16_ceqsex6v a_wceq f11_ceqsex6v a_sup_set_class f17_ceqsex6v a_wceq f12_ceqsex6v a_sup_set_class f18_ceqsex6v a_wceq a_w3a p_anbi2d f8_ceqsex6v a_sup_set_class f14_ceqsex6v a_wceq f10_ceqsex6v a_sup_set_class f16_ceqsex6v a_wceq f11_ceqsex6v a_sup_set_class f17_ceqsex6v a_wceq f12_ceqsex6v a_sup_set_class f18_ceqsex6v a_wceq a_w3a f1_ceqsex6v a_wa f10_ceqsex6v a_sup_set_class f16_ceqsex6v a_wceq f11_ceqsex6v a_sup_set_class f17_ceqsex6v a_wceq f12_ceqsex6v a_sup_set_class f18_ceqsex6v a_wceq a_w3a f2_ceqsex6v a_wa f10_ceqsex6v f11_ceqsex6v f12_ceqsex6v p_3exbidv e8_ceqsex6v f9_ceqsex6v a_sup_set_class f15_ceqsex6v a_wceq f2_ceqsex6v f3_ceqsex6v f10_ceqsex6v a_sup_set_class f16_ceqsex6v a_wceq f11_ceqsex6v a_sup_set_class f17_ceqsex6v a_wceq f12_ceqsex6v a_sup_set_class f18_ceqsex6v a_wceq a_w3a p_anbi2d f9_ceqsex6v a_sup_set_class f15_ceqsex6v a_wceq f10_ceqsex6v a_sup_set_class f16_ceqsex6v a_wceq f11_ceqsex6v a_sup_set_class f17_ceqsex6v a_wceq f12_ceqsex6v a_sup_set_class f18_ceqsex6v a_wceq a_w3a f2_ceqsex6v a_wa f10_ceqsex6v a_sup_set_class f16_ceqsex6v a_wceq f11_ceqsex6v a_sup_set_class f17_ceqsex6v a_wceq f12_ceqsex6v a_sup_set_class f18_ceqsex6v a_wceq a_w3a f3_ceqsex6v a_wa f10_ceqsex6v f11_ceqsex6v f12_ceqsex6v p_3exbidv f10_ceqsex6v a_sup_set_class f16_ceqsex6v a_wceq f11_ceqsex6v a_sup_set_class f17_ceqsex6v a_wceq f12_ceqsex6v a_sup_set_class f18_ceqsex6v a_wceq a_w3a f0_ceqsex6v a_wa f12_ceqsex6v a_wex f11_ceqsex6v a_wex f10_ceqsex6v a_wex f10_ceqsex6v a_sup_set_class f16_ceqsex6v a_wceq f11_ceqsex6v a_sup_set_class f17_ceqsex6v a_wceq f12_ceqsex6v a_sup_set_class f18_ceqsex6v a_wceq a_w3a f1_ceqsex6v a_wa f12_ceqsex6v a_wex f11_ceqsex6v a_wex f10_ceqsex6v a_wex f10_ceqsex6v a_sup_set_class f16_ceqsex6v a_wceq f11_ceqsex6v a_sup_set_class f17_ceqsex6v a_wceq f12_ceqsex6v a_sup_set_class f18_ceqsex6v a_wceq a_w3a f2_ceqsex6v a_wa f12_ceqsex6v a_wex f11_ceqsex6v a_wex f10_ceqsex6v a_wex f10_ceqsex6v a_sup_set_class f16_ceqsex6v a_wceq f11_ceqsex6v a_sup_set_class f17_ceqsex6v a_wceq f12_ceqsex6v a_sup_set_class f18_ceqsex6v a_wceq a_w3a f3_ceqsex6v a_wa f12_ceqsex6v a_wex f11_ceqsex6v a_wex f10_ceqsex6v a_wex f7_ceqsex6v f8_ceqsex6v f9_ceqsex6v f13_ceqsex6v f14_ceqsex6v f15_ceqsex6v p_ceqsex3v e3_ceqsex6v e4_ceqsex6v e5_ceqsex6v e9_ceqsex6v e10_ceqsex6v e11_ceqsex6v f3_ceqsex6v f4_ceqsex6v f5_ceqsex6v f6_ceqsex6v f10_ceqsex6v f11_ceqsex6v f12_ceqsex6v f16_ceqsex6v f17_ceqsex6v f18_ceqsex6v p_ceqsex3v f7_ceqsex6v a_sup_set_class f13_ceqsex6v a_wceq f8_ceqsex6v a_sup_set_class f14_ceqsex6v a_wceq f9_ceqsex6v a_sup_set_class f15_ceqsex6v a_wceq a_w3a f10_ceqsex6v a_sup_set_class f16_ceqsex6v a_wceq f11_ceqsex6v a_sup_set_class f17_ceqsex6v a_wceq f12_ceqsex6v a_sup_set_class f18_ceqsex6v a_wceq a_w3a f0_ceqsex6v a_wa f12_ceqsex6v a_wex f11_ceqsex6v a_wex f10_ceqsex6v a_wex a_wa f9_ceqsex6v a_wex f8_ceqsex6v a_wex f7_ceqsex6v a_wex f10_ceqsex6v a_sup_set_class f16_ceqsex6v a_wceq f11_ceqsex6v a_sup_set_class f17_ceqsex6v a_wceq f12_ceqsex6v a_sup_set_class f18_ceqsex6v a_wceq a_w3a f3_ceqsex6v a_wa f12_ceqsex6v a_wex f11_ceqsex6v a_wex f10_ceqsex6v a_wex f6_ceqsex6v p_bitri f7_ceqsex6v a_sup_set_class f13_ceqsex6v a_wceq f8_ceqsex6v a_sup_set_class f14_ceqsex6v a_wceq f9_ceqsex6v a_sup_set_class f15_ceqsex6v a_wceq a_w3a f10_ceqsex6v a_sup_set_class f16_ceqsex6v a_wceq f11_ceqsex6v a_sup_set_class f17_ceqsex6v a_wceq f12_ceqsex6v a_sup_set_class f18_ceqsex6v a_wceq a_w3a f0_ceqsex6v a_w3a f12_ceqsex6v a_wex f11_ceqsex6v a_wex f10_ceqsex6v a_wex f9_ceqsex6v a_wex f8_ceqsex6v a_wex f7_ceqsex6v a_wex f7_ceqsex6v a_sup_set_class f13_ceqsex6v a_wceq f8_ceqsex6v a_sup_set_class f14_ceqsex6v a_wceq f9_ceqsex6v a_sup_set_class f15_ceqsex6v a_wceq a_w3a f10_ceqsex6v a_sup_set_class f16_ceqsex6v a_wceq f11_ceqsex6v a_sup_set_class f17_ceqsex6v a_wceq f12_ceqsex6v a_sup_set_class f18_ceqsex6v a_wceq a_w3a f0_ceqsex6v a_wa f12_ceqsex6v a_wex f11_ceqsex6v a_wex f10_ceqsex6v a_wex a_wa f9_ceqsex6v a_wex f8_ceqsex6v a_wex f7_ceqsex6v a_wex f6_ceqsex6v p_bitri $.
$}

$(Elimination of eight existential quantifiers, using implicit
       substitution.  (Contributed by NM, 23-Sep-2011.) $)

${
	$v ph ps ch th ta et ze si rh x y z w v u t A B C D E F G H s  $.
	$d x y z w v u t s A  $.
	$d x y z w v u t s B  $.
	$d x y z w v u t s C  $.
	$d x y z w v u t s D  $.
	$d x y z w v u t s E  $.
	$d x y z w v u t s F  $.
	$d x y z w v u t s G  $.
	$d x y z w v u t s H  $.
	$d x ps  $.
	$d y ch  $.
	$d z th  $.
	$d w ta  $.
	$d v et  $.
	$d u ze  $.
	$d t si  $.
	$d s rh  $.
	f0_ceqsex8v $f wff ph $.
	f1_ceqsex8v $f wff ps $.
	f2_ceqsex8v $f wff ch $.
	f3_ceqsex8v $f wff th $.
	f4_ceqsex8v $f wff ta $.
	f5_ceqsex8v $f wff et $.
	f6_ceqsex8v $f wff ze $.
	f7_ceqsex8v $f wff si $.
	f8_ceqsex8v $f wff rh $.
	f9_ceqsex8v $f set x $.
	f10_ceqsex8v $f set y $.
	f11_ceqsex8v $f set z $.
	f12_ceqsex8v $f set w $.
	f13_ceqsex8v $f set v $.
	f14_ceqsex8v $f set u $.
	f15_ceqsex8v $f set t $.
	f16_ceqsex8v $f class A $.
	f17_ceqsex8v $f class B $.
	f18_ceqsex8v $f class C $.
	f19_ceqsex8v $f class D $.
	f20_ceqsex8v $f class E $.
	f21_ceqsex8v $f class F $.
	f22_ceqsex8v $f class G $.
	f23_ceqsex8v $f class H $.
	f24_ceqsex8v $f set s $.
	e0_ceqsex8v $e |- A e. _V $.
	e1_ceqsex8v $e |- B e. _V $.
	e2_ceqsex8v $e |- C e. _V $.
	e3_ceqsex8v $e |- D e. _V $.
	e4_ceqsex8v $e |- E e. _V $.
	e5_ceqsex8v $e |- F e. _V $.
	e6_ceqsex8v $e |- G e. _V $.
	e7_ceqsex8v $e |- H e. _V $.
	e8_ceqsex8v $e |- ( x = A -> ( ph <-> ps ) ) $.
	e9_ceqsex8v $e |- ( y = B -> ( ps <-> ch ) ) $.
	e10_ceqsex8v $e |- ( z = C -> ( ch <-> th ) ) $.
	e11_ceqsex8v $e |- ( w = D -> ( th <-> ta ) ) $.
	e12_ceqsex8v $e |- ( v = E -> ( ta <-> et ) ) $.
	e13_ceqsex8v $e |- ( u = F -> ( et <-> ze ) ) $.
	e14_ceqsex8v $e |- ( t = G -> ( ze <-> si ) ) $.
	e15_ceqsex8v $e |- ( s = H -> ( si <-> rh ) ) $.
	p_ceqsex8v $p |- ( E. x E. y E. z E. w E. v E. u E. t E. s ( ( ( x = A /\ y = B ) /\ ( z = C /\ w = D ) ) /\ ( ( v = E /\ u = F ) /\ ( t = G /\ s = H ) ) /\ ph ) <-> rh ) $= f9_ceqsex8v a_sup_set_class f16_ceqsex8v a_wceq f10_ceqsex8v a_sup_set_class f17_ceqsex8v a_wceq a_wa f11_ceqsex8v a_sup_set_class f18_ceqsex8v a_wceq f12_ceqsex8v a_sup_set_class f19_ceqsex8v a_wceq a_wa a_wa f13_ceqsex8v a_sup_set_class f20_ceqsex8v a_wceq f14_ceqsex8v a_sup_set_class f21_ceqsex8v a_wceq a_wa f15_ceqsex8v a_sup_set_class f22_ceqsex8v a_wceq f24_ceqsex8v a_sup_set_class f23_ceqsex8v a_wceq a_wa f0_ceqsex8v a_w3a f15_ceqsex8v f24_ceqsex8v p_19.42vv f9_ceqsex8v a_sup_set_class f16_ceqsex8v a_wceq f10_ceqsex8v a_sup_set_class f17_ceqsex8v a_wceq a_wa f11_ceqsex8v a_sup_set_class f18_ceqsex8v a_wceq f12_ceqsex8v a_sup_set_class f19_ceqsex8v a_wceq a_wa a_wa f13_ceqsex8v a_sup_set_class f20_ceqsex8v a_wceq f14_ceqsex8v a_sup_set_class f21_ceqsex8v a_wceq a_wa f15_ceqsex8v a_sup_set_class f22_ceqsex8v a_wceq f24_ceqsex8v a_sup_set_class f23_ceqsex8v a_wceq a_wa f0_ceqsex8v a_w3a a_wa f24_ceqsex8v a_wex f15_ceqsex8v a_wex f9_ceqsex8v a_sup_set_class f16_ceqsex8v a_wceq f10_ceqsex8v a_sup_set_class f17_ceqsex8v a_wceq a_wa f11_ceqsex8v a_sup_set_class f18_ceqsex8v a_wceq f12_ceqsex8v a_sup_set_class f19_ceqsex8v a_wceq a_wa a_wa f13_ceqsex8v a_sup_set_class f20_ceqsex8v a_wceq f14_ceqsex8v a_sup_set_class f21_ceqsex8v a_wceq a_wa f15_ceqsex8v a_sup_set_class f22_ceqsex8v a_wceq f24_ceqsex8v a_sup_set_class f23_ceqsex8v a_wceq a_wa f0_ceqsex8v a_w3a f24_ceqsex8v a_wex f15_ceqsex8v a_wex a_wa f13_ceqsex8v f14_ceqsex8v p_2exbii f9_ceqsex8v a_sup_set_class f16_ceqsex8v a_wceq f10_ceqsex8v a_sup_set_class f17_ceqsex8v a_wceq a_wa f11_ceqsex8v a_sup_set_class f18_ceqsex8v a_wceq f12_ceqsex8v a_sup_set_class f19_ceqsex8v a_wceq a_wa a_wa f13_ceqsex8v a_sup_set_class f20_ceqsex8v a_wceq f14_ceqsex8v a_sup_set_class f21_ceqsex8v a_wceq a_wa f15_ceqsex8v a_sup_set_class f22_ceqsex8v a_wceq f24_ceqsex8v a_sup_set_class f23_ceqsex8v a_wceq a_wa f0_ceqsex8v a_w3a f24_ceqsex8v a_wex f15_ceqsex8v a_wex f13_ceqsex8v f14_ceqsex8v p_19.42vv f9_ceqsex8v a_sup_set_class f16_ceqsex8v a_wceq f10_ceqsex8v a_sup_set_class f17_ceqsex8v a_wceq a_wa f11_ceqsex8v a_sup_set_class f18_ceqsex8v a_wceq f12_ceqsex8v a_sup_set_class f19_ceqsex8v a_wceq a_wa a_wa f13_ceqsex8v a_sup_set_class f20_ceqsex8v a_wceq f14_ceqsex8v a_sup_set_class f21_ceqsex8v a_wceq a_wa f15_ceqsex8v a_sup_set_class f22_ceqsex8v a_wceq f24_ceqsex8v a_sup_set_class f23_ceqsex8v a_wceq a_wa f0_ceqsex8v a_w3a a_wa f24_ceqsex8v a_wex f15_ceqsex8v a_wex f14_ceqsex8v a_wex f13_ceqsex8v a_wex f9_ceqsex8v a_sup_set_class f16_ceqsex8v a_wceq f10_ceqsex8v a_sup_set_class f17_ceqsex8v a_wceq a_wa f11_ceqsex8v a_sup_set_class f18_ceqsex8v a_wceq f12_ceqsex8v a_sup_set_class f19_ceqsex8v a_wceq a_wa a_wa f13_ceqsex8v a_sup_set_class f20_ceqsex8v a_wceq f14_ceqsex8v a_sup_set_class f21_ceqsex8v a_wceq a_wa f15_ceqsex8v a_sup_set_class f22_ceqsex8v a_wceq f24_ceqsex8v a_sup_set_class f23_ceqsex8v a_wceq a_wa f0_ceqsex8v a_w3a f24_ceqsex8v a_wex f15_ceqsex8v a_wex a_wa f14_ceqsex8v a_wex f13_ceqsex8v a_wex f9_ceqsex8v a_sup_set_class f16_ceqsex8v a_wceq f10_ceqsex8v a_sup_set_class f17_ceqsex8v a_wceq a_wa f11_ceqsex8v a_sup_set_class f18_ceqsex8v a_wceq f12_ceqsex8v a_sup_set_class f19_ceqsex8v a_wceq a_wa a_wa f13_ceqsex8v a_sup_set_class f20_ceqsex8v a_wceq f14_ceqsex8v a_sup_set_class f21_ceqsex8v a_wceq a_wa f15_ceqsex8v a_sup_set_class f22_ceqsex8v a_wceq f24_ceqsex8v a_sup_set_class f23_ceqsex8v a_wceq a_wa f0_ceqsex8v a_w3a f24_ceqsex8v a_wex f15_ceqsex8v a_wex f14_ceqsex8v a_wex f13_ceqsex8v a_wex a_wa p_bitri f9_ceqsex8v a_sup_set_class f16_ceqsex8v a_wceq f10_ceqsex8v a_sup_set_class f17_ceqsex8v a_wceq a_wa f11_ceqsex8v a_sup_set_class f18_ceqsex8v a_wceq f12_ceqsex8v a_sup_set_class f19_ceqsex8v a_wceq a_wa a_wa f13_ceqsex8v a_sup_set_class f20_ceqsex8v a_wceq f14_ceqsex8v a_sup_set_class f21_ceqsex8v a_wceq a_wa f15_ceqsex8v a_sup_set_class f22_ceqsex8v a_wceq f24_ceqsex8v a_sup_set_class f23_ceqsex8v a_wceq a_wa a_wa f0_ceqsex8v p_3anass f13_ceqsex8v a_sup_set_class f20_ceqsex8v a_wceq f14_ceqsex8v a_sup_set_class f21_ceqsex8v a_wceq a_wa f15_ceqsex8v a_sup_set_class f22_ceqsex8v a_wceq f24_ceqsex8v a_sup_set_class f23_ceqsex8v a_wceq a_wa f0_ceqsex8v a_df-3an f13_ceqsex8v a_sup_set_class f20_ceqsex8v a_wceq f14_ceqsex8v a_sup_set_class f21_ceqsex8v a_wceq a_wa f15_ceqsex8v a_sup_set_class f22_ceqsex8v a_wceq f24_ceqsex8v a_sup_set_class f23_ceqsex8v a_wceq a_wa f0_ceqsex8v a_w3a f13_ceqsex8v a_sup_set_class f20_ceqsex8v a_wceq f14_ceqsex8v a_sup_set_class f21_ceqsex8v a_wceq a_wa f15_ceqsex8v a_sup_set_class f22_ceqsex8v a_wceq f24_ceqsex8v a_sup_set_class f23_ceqsex8v a_wceq a_wa a_wa f0_ceqsex8v a_wa f9_ceqsex8v a_sup_set_class f16_ceqsex8v a_wceq f10_ceqsex8v a_sup_set_class f17_ceqsex8v a_wceq a_wa f11_ceqsex8v a_sup_set_class f18_ceqsex8v a_wceq f12_ceqsex8v a_sup_set_class f19_ceqsex8v a_wceq a_wa a_wa p_anbi2i f9_ceqsex8v a_sup_set_class f16_ceqsex8v a_wceq f10_ceqsex8v a_sup_set_class f17_ceqsex8v a_wceq a_wa f11_ceqsex8v a_sup_set_class f18_ceqsex8v a_wceq f12_ceqsex8v a_sup_set_class f19_ceqsex8v a_wceq a_wa a_wa f13_ceqsex8v a_sup_set_class f20_ceqsex8v a_wceq f14_ceqsex8v a_sup_set_class f21_ceqsex8v a_wceq a_wa f15_ceqsex8v a_sup_set_class f22_ceqsex8v a_wceq f24_ceqsex8v a_sup_set_class f23_ceqsex8v a_wceq a_wa a_wa f0_ceqsex8v a_w3a f9_ceqsex8v a_sup_set_class f16_ceqsex8v a_wceq f10_ceqsex8v a_sup_set_class f17_ceqsex8v a_wceq a_wa f11_ceqsex8v a_sup_set_class f18_ceqsex8v a_wceq f12_ceqsex8v a_sup_set_class f19_ceqsex8v a_wceq a_wa a_wa f13_ceqsex8v a_sup_set_class f20_ceqsex8v a_wceq f14_ceqsex8v a_sup_set_class f21_ceqsex8v a_wceq a_wa f15_ceqsex8v a_sup_set_class f22_ceqsex8v a_wceq f24_ceqsex8v a_sup_set_class f23_ceqsex8v a_wceq a_wa a_wa f0_ceqsex8v a_wa a_wa f9_ceqsex8v a_sup_set_class f16_ceqsex8v a_wceq f10_ceqsex8v a_sup_set_class f17_ceqsex8v a_wceq a_wa f11_ceqsex8v a_sup_set_class f18_ceqsex8v a_wceq f12_ceqsex8v a_sup_set_class f19_ceqsex8v a_wceq a_wa a_wa f13_ceqsex8v a_sup_set_class f20_ceqsex8v a_wceq f14_ceqsex8v a_sup_set_class f21_ceqsex8v a_wceq a_wa f15_ceqsex8v a_sup_set_class f22_ceqsex8v a_wceq f24_ceqsex8v a_sup_set_class f23_ceqsex8v a_wceq a_wa f0_ceqsex8v a_w3a a_wa p_bitr4i f9_ceqsex8v a_sup_set_class f16_ceqsex8v a_wceq f10_ceqsex8v a_sup_set_class f17_ceqsex8v a_wceq a_wa f11_ceqsex8v a_sup_set_class f18_ceqsex8v a_wceq f12_ceqsex8v a_sup_set_class f19_ceqsex8v a_wceq a_wa a_wa f13_ceqsex8v a_sup_set_class f20_ceqsex8v a_wceq f14_ceqsex8v a_sup_set_class f21_ceqsex8v a_wceq a_wa f15_ceqsex8v a_sup_set_class f22_ceqsex8v a_wceq f24_ceqsex8v a_sup_set_class f23_ceqsex8v a_wceq a_wa a_wa f0_ceqsex8v a_w3a f9_ceqsex8v a_sup_set_class f16_ceqsex8v a_wceq f10_ceqsex8v a_sup_set_class f17_ceqsex8v a_wceq a_wa f11_ceqsex8v a_sup_set_class f18_ceqsex8v a_wceq f12_ceqsex8v a_sup_set_class f19_ceqsex8v a_wceq a_wa a_wa f13_ceqsex8v a_sup_set_class f20_ceqsex8v a_wceq f14_ceqsex8v a_sup_set_class f21_ceqsex8v a_wceq a_wa f15_ceqsex8v a_sup_set_class f22_ceqsex8v a_wceq f24_ceqsex8v a_sup_set_class f23_ceqsex8v a_wceq a_wa f0_ceqsex8v a_w3a a_wa f15_ceqsex8v f24_ceqsex8v p_2exbii f9_ceqsex8v a_sup_set_class f16_ceqsex8v a_wceq f10_ceqsex8v a_sup_set_class f17_ceqsex8v a_wceq a_wa f11_ceqsex8v a_sup_set_class f18_ceqsex8v a_wceq f12_ceqsex8v a_sup_set_class f19_ceqsex8v a_wceq a_wa a_wa f13_ceqsex8v a_sup_set_class f20_ceqsex8v a_wceq f14_ceqsex8v a_sup_set_class f21_ceqsex8v a_wceq a_wa f15_ceqsex8v a_sup_set_class f22_ceqsex8v a_wceq f24_ceqsex8v a_sup_set_class f23_ceqsex8v a_wceq a_wa a_wa f0_ceqsex8v a_w3a f24_ceqsex8v a_wex f15_ceqsex8v a_wex f9_ceqsex8v a_sup_set_class f16_ceqsex8v a_wceq f10_ceqsex8v a_sup_set_class f17_ceqsex8v a_wceq a_wa f11_ceqsex8v a_sup_set_class f18_ceqsex8v a_wceq f12_ceqsex8v a_sup_set_class f19_ceqsex8v a_wceq a_wa a_wa f13_ceqsex8v a_sup_set_class f20_ceqsex8v a_wceq f14_ceqsex8v a_sup_set_class f21_ceqsex8v a_wceq a_wa f15_ceqsex8v a_sup_set_class f22_ceqsex8v a_wceq f24_ceqsex8v a_sup_set_class f23_ceqsex8v a_wceq a_wa f0_ceqsex8v a_w3a a_wa f24_ceqsex8v a_wex f15_ceqsex8v a_wex f13_ceqsex8v f14_ceqsex8v p_2exbii f9_ceqsex8v a_sup_set_class f16_ceqsex8v a_wceq f10_ceqsex8v a_sup_set_class f17_ceqsex8v a_wceq a_wa f11_ceqsex8v a_sup_set_class f18_ceqsex8v a_wceq f12_ceqsex8v a_sup_set_class f19_ceqsex8v a_wceq a_wa f13_ceqsex8v a_sup_set_class f20_ceqsex8v a_wceq f14_ceqsex8v a_sup_set_class f21_ceqsex8v a_wceq a_wa f15_ceqsex8v a_sup_set_class f22_ceqsex8v a_wceq f24_ceqsex8v a_sup_set_class f23_ceqsex8v a_wceq a_wa f0_ceqsex8v a_w3a f24_ceqsex8v a_wex f15_ceqsex8v a_wex f14_ceqsex8v a_wex f13_ceqsex8v a_wex a_df-3an f9_ceqsex8v a_sup_set_class f16_ceqsex8v a_wceq f10_ceqsex8v a_sup_set_class f17_ceqsex8v a_wceq a_wa f11_ceqsex8v a_sup_set_class f18_ceqsex8v a_wceq f12_ceqsex8v a_sup_set_class f19_ceqsex8v a_wceq a_wa a_wa f13_ceqsex8v a_sup_set_class f20_ceqsex8v a_wceq f14_ceqsex8v a_sup_set_class f21_ceqsex8v a_wceq a_wa f15_ceqsex8v a_sup_set_class f22_ceqsex8v a_wceq f24_ceqsex8v a_sup_set_class f23_ceqsex8v a_wceq a_wa f0_ceqsex8v a_w3a a_wa f24_ceqsex8v a_wex f15_ceqsex8v a_wex f14_ceqsex8v a_wex f13_ceqsex8v a_wex f9_ceqsex8v a_sup_set_class f16_ceqsex8v a_wceq f10_ceqsex8v a_sup_set_class f17_ceqsex8v a_wceq a_wa f11_ceqsex8v a_sup_set_class f18_ceqsex8v a_wceq f12_ceqsex8v a_sup_set_class f19_ceqsex8v a_wceq a_wa a_wa f13_ceqsex8v a_sup_set_class f20_ceqsex8v a_wceq f14_ceqsex8v a_sup_set_class f21_ceqsex8v a_wceq a_wa f15_ceqsex8v a_sup_set_class f22_ceqsex8v a_wceq f24_ceqsex8v a_sup_set_class f23_ceqsex8v a_wceq a_wa f0_ceqsex8v a_w3a f24_ceqsex8v a_wex f15_ceqsex8v a_wex f14_ceqsex8v a_wex f13_ceqsex8v a_wex a_wa f9_ceqsex8v a_sup_set_class f16_ceqsex8v a_wceq f10_ceqsex8v a_sup_set_class f17_ceqsex8v a_wceq a_wa f11_ceqsex8v a_sup_set_class f18_ceqsex8v a_wceq f12_ceqsex8v a_sup_set_class f19_ceqsex8v a_wceq a_wa a_wa f13_ceqsex8v a_sup_set_class f20_ceqsex8v a_wceq f14_ceqsex8v a_sup_set_class f21_ceqsex8v a_wceq a_wa f15_ceqsex8v a_sup_set_class f22_ceqsex8v a_wceq f24_ceqsex8v a_sup_set_class f23_ceqsex8v a_wceq a_wa a_wa f0_ceqsex8v a_w3a f24_ceqsex8v a_wex f15_ceqsex8v a_wex f14_ceqsex8v a_wex f13_ceqsex8v a_wex f9_ceqsex8v a_sup_set_class f16_ceqsex8v a_wceq f10_ceqsex8v a_sup_set_class f17_ceqsex8v a_wceq a_wa f11_ceqsex8v a_sup_set_class f18_ceqsex8v a_wceq f12_ceqsex8v a_sup_set_class f19_ceqsex8v a_wceq a_wa f13_ceqsex8v a_sup_set_class f20_ceqsex8v a_wceq f14_ceqsex8v a_sup_set_class f21_ceqsex8v a_wceq a_wa f15_ceqsex8v a_sup_set_class f22_ceqsex8v a_wceq f24_ceqsex8v a_sup_set_class f23_ceqsex8v a_wceq a_wa f0_ceqsex8v a_w3a f24_ceqsex8v a_wex f15_ceqsex8v a_wex f14_ceqsex8v a_wex f13_ceqsex8v a_wex a_w3a p_3bitr4i f9_ceqsex8v a_sup_set_class f16_ceqsex8v a_wceq f10_ceqsex8v a_sup_set_class f17_ceqsex8v a_wceq a_wa f11_ceqsex8v a_sup_set_class f18_ceqsex8v a_wceq f12_ceqsex8v a_sup_set_class f19_ceqsex8v a_wceq a_wa a_wa f13_ceqsex8v a_sup_set_class f20_ceqsex8v a_wceq f14_ceqsex8v a_sup_set_class f21_ceqsex8v a_wceq a_wa f15_ceqsex8v a_sup_set_class f22_ceqsex8v a_wceq f24_ceqsex8v a_sup_set_class f23_ceqsex8v a_wceq a_wa a_wa f0_ceqsex8v a_w3a f24_ceqsex8v a_wex f15_ceqsex8v a_wex f14_ceqsex8v a_wex f13_ceqsex8v a_wex f9_ceqsex8v a_sup_set_class f16_ceqsex8v a_wceq f10_ceqsex8v a_sup_set_class f17_ceqsex8v a_wceq a_wa f11_ceqsex8v a_sup_set_class f18_ceqsex8v a_wceq f12_ceqsex8v a_sup_set_class f19_ceqsex8v a_wceq a_wa f13_ceqsex8v a_sup_set_class f20_ceqsex8v a_wceq f14_ceqsex8v a_sup_set_class f21_ceqsex8v a_wceq a_wa f15_ceqsex8v a_sup_set_class f22_ceqsex8v a_wceq f24_ceqsex8v a_sup_set_class f23_ceqsex8v a_wceq a_wa f0_ceqsex8v a_w3a f24_ceqsex8v a_wex f15_ceqsex8v a_wex f14_ceqsex8v a_wex f13_ceqsex8v a_wex a_w3a f11_ceqsex8v f12_ceqsex8v p_2exbii f9_ceqsex8v a_sup_set_class f16_ceqsex8v a_wceq f10_ceqsex8v a_sup_set_class f17_ceqsex8v a_wceq a_wa f11_ceqsex8v a_sup_set_class f18_ceqsex8v a_wceq f12_ceqsex8v a_sup_set_class f19_ceqsex8v a_wceq a_wa a_wa f13_ceqsex8v a_sup_set_class f20_ceqsex8v a_wceq f14_ceqsex8v a_sup_set_class f21_ceqsex8v a_wceq a_wa f15_ceqsex8v a_sup_set_class f22_ceqsex8v a_wceq f24_ceqsex8v a_sup_set_class f23_ceqsex8v a_wceq a_wa a_wa f0_ceqsex8v a_w3a f24_ceqsex8v a_wex f15_ceqsex8v a_wex f14_ceqsex8v a_wex f13_ceqsex8v a_wex f12_ceqsex8v a_wex f11_ceqsex8v a_wex f9_ceqsex8v a_sup_set_class f16_ceqsex8v a_wceq f10_ceqsex8v a_sup_set_class f17_ceqsex8v a_wceq a_wa f11_ceqsex8v a_sup_set_class f18_ceqsex8v a_wceq f12_ceqsex8v a_sup_set_class f19_ceqsex8v a_wceq a_wa f13_ceqsex8v a_sup_set_class f20_ceqsex8v a_wceq f14_ceqsex8v a_sup_set_class f21_ceqsex8v a_wceq a_wa f15_ceqsex8v a_sup_set_class f22_ceqsex8v a_wceq f24_ceqsex8v a_sup_set_class f23_ceqsex8v a_wceq a_wa f0_ceqsex8v a_w3a f24_ceqsex8v a_wex f15_ceqsex8v a_wex f14_ceqsex8v a_wex f13_ceqsex8v a_wex a_w3a f12_ceqsex8v a_wex f11_ceqsex8v a_wex f9_ceqsex8v f10_ceqsex8v p_2exbii e0_ceqsex8v e1_ceqsex8v e2_ceqsex8v e3_ceqsex8v e8_ceqsex8v f9_ceqsex8v a_sup_set_class f16_ceqsex8v a_wceq f0_ceqsex8v f1_ceqsex8v f13_ceqsex8v a_sup_set_class f20_ceqsex8v a_wceq f14_ceqsex8v a_sup_set_class f21_ceqsex8v a_wceq a_wa f15_ceqsex8v a_sup_set_class f22_ceqsex8v a_wceq f24_ceqsex8v a_sup_set_class f23_ceqsex8v a_wceq a_wa p_3anbi3d f9_ceqsex8v a_sup_set_class f16_ceqsex8v a_wceq f13_ceqsex8v a_sup_set_class f20_ceqsex8v a_wceq f14_ceqsex8v a_sup_set_class f21_ceqsex8v a_wceq a_wa f15_ceqsex8v a_sup_set_class f22_ceqsex8v a_wceq f24_ceqsex8v a_sup_set_class f23_ceqsex8v a_wceq a_wa f0_ceqsex8v a_w3a f13_ceqsex8v a_sup_set_class f20_ceqsex8v a_wceq f14_ceqsex8v a_sup_set_class f21_ceqsex8v a_wceq a_wa f15_ceqsex8v a_sup_set_class f22_ceqsex8v a_wceq f24_ceqsex8v a_sup_set_class f23_ceqsex8v a_wceq a_wa f1_ceqsex8v a_w3a f13_ceqsex8v f14_ceqsex8v f15_ceqsex8v f24_ceqsex8v p_4exbidv e9_ceqsex8v f10_ceqsex8v a_sup_set_class f17_ceqsex8v a_wceq f1_ceqsex8v f2_ceqsex8v f13_ceqsex8v a_sup_set_class f20_ceqsex8v a_wceq f14_ceqsex8v a_sup_set_class f21_ceqsex8v a_wceq a_wa f15_ceqsex8v a_sup_set_class f22_ceqsex8v a_wceq f24_ceqsex8v a_sup_set_class f23_ceqsex8v a_wceq a_wa p_3anbi3d f10_ceqsex8v a_sup_set_class f17_ceqsex8v a_wceq f13_ceqsex8v a_sup_set_class f20_ceqsex8v a_wceq f14_ceqsex8v a_sup_set_class f21_ceqsex8v a_wceq a_wa f15_ceqsex8v a_sup_set_class f22_ceqsex8v a_wceq f24_ceqsex8v a_sup_set_class f23_ceqsex8v a_wceq a_wa f1_ceqsex8v a_w3a f13_ceqsex8v a_sup_set_class f20_ceqsex8v a_wceq f14_ceqsex8v a_sup_set_class f21_ceqsex8v a_wceq a_wa f15_ceqsex8v a_sup_set_class f22_ceqsex8v a_wceq f24_ceqsex8v a_sup_set_class f23_ceqsex8v a_wceq a_wa f2_ceqsex8v a_w3a f13_ceqsex8v f14_ceqsex8v f15_ceqsex8v f24_ceqsex8v p_4exbidv e10_ceqsex8v f11_ceqsex8v a_sup_set_class f18_ceqsex8v a_wceq f2_ceqsex8v f3_ceqsex8v f13_ceqsex8v a_sup_set_class f20_ceqsex8v a_wceq f14_ceqsex8v a_sup_set_class f21_ceqsex8v a_wceq a_wa f15_ceqsex8v a_sup_set_class f22_ceqsex8v a_wceq f24_ceqsex8v a_sup_set_class f23_ceqsex8v a_wceq a_wa p_3anbi3d f11_ceqsex8v a_sup_set_class f18_ceqsex8v a_wceq f13_ceqsex8v a_sup_set_class f20_ceqsex8v a_wceq f14_ceqsex8v a_sup_set_class f21_ceqsex8v a_wceq a_wa f15_ceqsex8v a_sup_set_class f22_ceqsex8v a_wceq f24_ceqsex8v a_sup_set_class f23_ceqsex8v a_wceq a_wa f2_ceqsex8v a_w3a f13_ceqsex8v a_sup_set_class f20_ceqsex8v a_wceq f14_ceqsex8v a_sup_set_class f21_ceqsex8v a_wceq a_wa f15_ceqsex8v a_sup_set_class f22_ceqsex8v a_wceq f24_ceqsex8v a_sup_set_class f23_ceqsex8v a_wceq a_wa f3_ceqsex8v a_w3a f13_ceqsex8v f14_ceqsex8v f15_ceqsex8v f24_ceqsex8v p_4exbidv e11_ceqsex8v f12_ceqsex8v a_sup_set_class f19_ceqsex8v a_wceq f3_ceqsex8v f4_ceqsex8v f13_ceqsex8v a_sup_set_class f20_ceqsex8v a_wceq f14_ceqsex8v a_sup_set_class f21_ceqsex8v a_wceq a_wa f15_ceqsex8v a_sup_set_class f22_ceqsex8v a_wceq f24_ceqsex8v a_sup_set_class f23_ceqsex8v a_wceq a_wa p_3anbi3d f12_ceqsex8v a_sup_set_class f19_ceqsex8v a_wceq f13_ceqsex8v a_sup_set_class f20_ceqsex8v a_wceq f14_ceqsex8v a_sup_set_class f21_ceqsex8v a_wceq a_wa f15_ceqsex8v a_sup_set_class f22_ceqsex8v a_wceq f24_ceqsex8v a_sup_set_class f23_ceqsex8v a_wceq a_wa f3_ceqsex8v a_w3a f13_ceqsex8v a_sup_set_class f20_ceqsex8v a_wceq f14_ceqsex8v a_sup_set_class f21_ceqsex8v a_wceq a_wa f15_ceqsex8v a_sup_set_class f22_ceqsex8v a_wceq f24_ceqsex8v a_sup_set_class f23_ceqsex8v a_wceq a_wa f4_ceqsex8v a_w3a f13_ceqsex8v f14_ceqsex8v f15_ceqsex8v f24_ceqsex8v p_4exbidv f13_ceqsex8v a_sup_set_class f20_ceqsex8v a_wceq f14_ceqsex8v a_sup_set_class f21_ceqsex8v a_wceq a_wa f15_ceqsex8v a_sup_set_class f22_ceqsex8v a_wceq f24_ceqsex8v a_sup_set_class f23_ceqsex8v a_wceq a_wa f0_ceqsex8v a_w3a f24_ceqsex8v a_wex f15_ceqsex8v a_wex f14_ceqsex8v a_wex f13_ceqsex8v a_wex f13_ceqsex8v a_sup_set_class f20_ceqsex8v a_wceq f14_ceqsex8v a_sup_set_class f21_ceqsex8v a_wceq a_wa f15_ceqsex8v a_sup_set_class f22_ceqsex8v a_wceq f24_ceqsex8v a_sup_set_class f23_ceqsex8v a_wceq a_wa f1_ceqsex8v a_w3a f24_ceqsex8v a_wex f15_ceqsex8v a_wex f14_ceqsex8v a_wex f13_ceqsex8v a_wex f13_ceqsex8v a_sup_set_class f20_ceqsex8v a_wceq f14_ceqsex8v a_sup_set_class f21_ceqsex8v a_wceq a_wa f15_ceqsex8v a_sup_set_class f22_ceqsex8v a_wceq f24_ceqsex8v a_sup_set_class f23_ceqsex8v a_wceq a_wa f2_ceqsex8v a_w3a f24_ceqsex8v a_wex f15_ceqsex8v a_wex f14_ceqsex8v a_wex f13_ceqsex8v a_wex f13_ceqsex8v a_sup_set_class f20_ceqsex8v a_wceq f14_ceqsex8v a_sup_set_class f21_ceqsex8v a_wceq a_wa f15_ceqsex8v a_sup_set_class f22_ceqsex8v a_wceq f24_ceqsex8v a_sup_set_class f23_ceqsex8v a_wceq a_wa f3_ceqsex8v a_w3a f24_ceqsex8v a_wex f15_ceqsex8v a_wex f14_ceqsex8v a_wex f13_ceqsex8v a_wex f13_ceqsex8v a_sup_set_class f20_ceqsex8v a_wceq f14_ceqsex8v a_sup_set_class f21_ceqsex8v a_wceq a_wa f15_ceqsex8v a_sup_set_class f22_ceqsex8v a_wceq f24_ceqsex8v a_sup_set_class f23_ceqsex8v a_wceq a_wa f4_ceqsex8v a_w3a f24_ceqsex8v a_wex f15_ceqsex8v a_wex f14_ceqsex8v a_wex f13_ceqsex8v a_wex f9_ceqsex8v f10_ceqsex8v f11_ceqsex8v f12_ceqsex8v f16_ceqsex8v f17_ceqsex8v f18_ceqsex8v f19_ceqsex8v p_ceqsex4v e4_ceqsex8v e5_ceqsex8v e6_ceqsex8v e7_ceqsex8v e12_ceqsex8v e13_ceqsex8v e14_ceqsex8v e15_ceqsex8v f4_ceqsex8v f5_ceqsex8v f6_ceqsex8v f7_ceqsex8v f8_ceqsex8v f13_ceqsex8v f14_ceqsex8v f15_ceqsex8v f24_ceqsex8v f20_ceqsex8v f21_ceqsex8v f22_ceqsex8v f23_ceqsex8v p_ceqsex4v f9_ceqsex8v a_sup_set_class f16_ceqsex8v a_wceq f10_ceqsex8v a_sup_set_class f17_ceqsex8v a_wceq a_wa f11_ceqsex8v a_sup_set_class f18_ceqsex8v a_wceq f12_ceqsex8v a_sup_set_class f19_ceqsex8v a_wceq a_wa f13_ceqsex8v a_sup_set_class f20_ceqsex8v a_wceq f14_ceqsex8v a_sup_set_class f21_ceqsex8v a_wceq a_wa f15_ceqsex8v a_sup_set_class f22_ceqsex8v a_wceq f24_ceqsex8v a_sup_set_class f23_ceqsex8v a_wceq a_wa f0_ceqsex8v a_w3a f24_ceqsex8v a_wex f15_ceqsex8v a_wex f14_ceqsex8v a_wex f13_ceqsex8v a_wex a_w3a f12_ceqsex8v a_wex f11_ceqsex8v a_wex f10_ceqsex8v a_wex f9_ceqsex8v a_wex f13_ceqsex8v a_sup_set_class f20_ceqsex8v a_wceq f14_ceqsex8v a_sup_set_class f21_ceqsex8v a_wceq a_wa f15_ceqsex8v a_sup_set_class f22_ceqsex8v a_wceq f24_ceqsex8v a_sup_set_class f23_ceqsex8v a_wceq a_wa f4_ceqsex8v a_w3a f24_ceqsex8v a_wex f15_ceqsex8v a_wex f14_ceqsex8v a_wex f13_ceqsex8v a_wex f8_ceqsex8v p_bitri f9_ceqsex8v a_sup_set_class f16_ceqsex8v a_wceq f10_ceqsex8v a_sup_set_class f17_ceqsex8v a_wceq a_wa f11_ceqsex8v a_sup_set_class f18_ceqsex8v a_wceq f12_ceqsex8v a_sup_set_class f19_ceqsex8v a_wceq a_wa a_wa f13_ceqsex8v a_sup_set_class f20_ceqsex8v a_wceq f14_ceqsex8v a_sup_set_class f21_ceqsex8v a_wceq a_wa f15_ceqsex8v a_sup_set_class f22_ceqsex8v a_wceq f24_ceqsex8v a_sup_set_class f23_ceqsex8v a_wceq a_wa a_wa f0_ceqsex8v a_w3a f24_ceqsex8v a_wex f15_ceqsex8v a_wex f14_ceqsex8v a_wex f13_ceqsex8v a_wex f12_ceqsex8v a_wex f11_ceqsex8v a_wex f10_ceqsex8v a_wex f9_ceqsex8v a_wex f9_ceqsex8v a_sup_set_class f16_ceqsex8v a_wceq f10_ceqsex8v a_sup_set_class f17_ceqsex8v a_wceq a_wa f11_ceqsex8v a_sup_set_class f18_ceqsex8v a_wceq f12_ceqsex8v a_sup_set_class f19_ceqsex8v a_wceq a_wa f13_ceqsex8v a_sup_set_class f20_ceqsex8v a_wceq f14_ceqsex8v a_sup_set_class f21_ceqsex8v a_wceq a_wa f15_ceqsex8v a_sup_set_class f22_ceqsex8v a_wceq f24_ceqsex8v a_sup_set_class f23_ceqsex8v a_wceq a_wa f0_ceqsex8v a_w3a f24_ceqsex8v a_wex f15_ceqsex8v a_wex f14_ceqsex8v a_wex f13_ceqsex8v a_wex a_w3a f12_ceqsex8v a_wex f11_ceqsex8v a_wex f10_ceqsex8v a_wex f9_ceqsex8v a_wex f8_ceqsex8v p_bitri $.
$}

$(Change of bound variable using implicit substitution.  (Contributed by
       NM, 17-May-1996.)  (Proof shortened by Andrew Salmon, 8-Jun-2011.) $)

${
	$v ph ps ch th x y A  $.
	$d x ps  $.
	$d y ph  $.
	$d x th  $.
	$d y ch  $.
	$d y A  $.
	f0_gencbvex $f wff ph $.
	f1_gencbvex $f wff ps $.
	f2_gencbvex $f wff ch $.
	f3_gencbvex $f wff th $.
	f4_gencbvex $f set x $.
	f5_gencbvex $f set y $.
	f6_gencbvex $f class A $.
	e0_gencbvex $e |- A e. _V $.
	e1_gencbvex $e |- ( A = y -> ( ph <-> ps ) ) $.
	e2_gencbvex $e |- ( A = y -> ( ch <-> th ) ) $.
	e3_gencbvex $e |- ( th <-> E. x ( ch /\ A = y ) ) $.
	p_gencbvex $p |- ( E. x ( ch /\ ph ) <-> E. y ( th /\ ps ) ) $= f5_gencbvex a_sup_set_class f6_gencbvex a_wceq f3_gencbvex f1_gencbvex a_wa a_wa f4_gencbvex f5_gencbvex p_excom e0_gencbvex e2_gencbvex e1_gencbvex f6_gencbvex f5_gencbvex a_sup_set_class a_wceq f2_gencbvex f3_gencbvex f0_gencbvex f1_gencbvex p_anbi12d f6_gencbvex f5_gencbvex a_sup_set_class a_wceq f2_gencbvex f0_gencbvex a_wa f3_gencbvex f1_gencbvex a_wa p_bicomd f3_gencbvex f1_gencbvex a_wa f2_gencbvex f0_gencbvex a_wa a_wb f6_gencbvex f5_gencbvex a_sup_set_class p_eqcoms f3_gencbvex f1_gencbvex a_wa f2_gencbvex f0_gencbvex a_wa f5_gencbvex f6_gencbvex p_ceqsexv f5_gencbvex a_sup_set_class f6_gencbvex a_wceq f3_gencbvex f1_gencbvex a_wa a_wa f5_gencbvex a_wex f2_gencbvex f0_gencbvex a_wa f4_gencbvex p_exbii f5_gencbvex a_sup_set_class f6_gencbvex a_wceq f3_gencbvex f1_gencbvex a_wa f4_gencbvex p_19.41v f5_gencbvex a_sup_set_class f6_gencbvex a_wceq f4_gencbvex a_wex f3_gencbvex f1_gencbvex a_wa p_simpr e3_gencbvex f6_gencbvex f5_gencbvex a_sup_set_class p_eqcom f6_gencbvex f5_gencbvex a_sup_set_class a_wceq f5_gencbvex a_sup_set_class f6_gencbvex a_wceq p_biimpi f6_gencbvex f5_gencbvex a_sup_set_class a_wceq f5_gencbvex a_sup_set_class f6_gencbvex a_wceq f2_gencbvex p_adantl f2_gencbvex f6_gencbvex f5_gencbvex a_sup_set_class a_wceq a_wa f5_gencbvex a_sup_set_class f6_gencbvex a_wceq f4_gencbvex p_eximi f3_gencbvex f2_gencbvex f6_gencbvex f5_gencbvex a_sup_set_class a_wceq a_wa f4_gencbvex a_wex f5_gencbvex a_sup_set_class f6_gencbvex a_wceq f4_gencbvex a_wex p_sylbi f3_gencbvex f5_gencbvex a_sup_set_class f6_gencbvex a_wceq f4_gencbvex a_wex f1_gencbvex p_adantr f3_gencbvex f1_gencbvex a_wa f5_gencbvex a_sup_set_class f6_gencbvex a_wceq f4_gencbvex a_wex p_ancri f5_gencbvex a_sup_set_class f6_gencbvex a_wceq f4_gencbvex a_wex f3_gencbvex f1_gencbvex a_wa a_wa f3_gencbvex f1_gencbvex a_wa p_impbii f5_gencbvex a_sup_set_class f6_gencbvex a_wceq f3_gencbvex f1_gencbvex a_wa a_wa f4_gencbvex a_wex f5_gencbvex a_sup_set_class f6_gencbvex a_wceq f4_gencbvex a_wex f3_gencbvex f1_gencbvex a_wa a_wa f3_gencbvex f1_gencbvex a_wa p_bitri f5_gencbvex a_sup_set_class f6_gencbvex a_wceq f3_gencbvex f1_gencbvex a_wa a_wa f4_gencbvex a_wex f3_gencbvex f1_gencbvex a_wa f5_gencbvex p_exbii f5_gencbvex a_sup_set_class f6_gencbvex a_wceq f3_gencbvex f1_gencbvex a_wa a_wa f5_gencbvex a_wex f4_gencbvex a_wex f5_gencbvex a_sup_set_class f6_gencbvex a_wceq f3_gencbvex f1_gencbvex a_wa a_wa f4_gencbvex a_wex f5_gencbvex a_wex f2_gencbvex f0_gencbvex a_wa f4_gencbvex a_wex f3_gencbvex f1_gencbvex a_wa f5_gencbvex a_wex p_3bitr3i $.
$}

$(Restatement of ~ gencbvex with weaker hypotheses.  (Contributed by
       Jeffrey Hankins, 6-Dec-2006.) $)

${
	$v ph ps ch th x y A  $.
	$d x ps  $.
	$d y ph  $.
	$d x th  $.
	$d y ch  $.
	$d y A  $.
	f0_gencbvex2 $f wff ph $.
	f1_gencbvex2 $f wff ps $.
	f2_gencbvex2 $f wff ch $.
	f3_gencbvex2 $f wff th $.
	f4_gencbvex2 $f set x $.
	f5_gencbvex2 $f set y $.
	f6_gencbvex2 $f class A $.
	e0_gencbvex2 $e |- A e. _V $.
	e1_gencbvex2 $e |- ( A = y -> ( ph <-> ps ) ) $.
	e2_gencbvex2 $e |- ( A = y -> ( ch <-> th ) ) $.
	e3_gencbvex2 $e |- ( th -> E. x ( ch /\ A = y ) ) $.
	p_gencbvex2 $p |- ( E. x ( ch /\ ph ) <-> E. y ( th /\ ps ) ) $= e0_gencbvex2 e1_gencbvex2 e2_gencbvex2 e3_gencbvex2 e2_gencbvex2 f6_gencbvex2 f5_gencbvex2 a_sup_set_class a_wceq f2_gencbvex2 f3_gencbvex2 p_biimpac f2_gencbvex2 f6_gencbvex2 f5_gencbvex2 a_sup_set_class a_wceq a_wa f3_gencbvex2 f4_gencbvex2 p_exlimiv f3_gencbvex2 f2_gencbvex2 f6_gencbvex2 f5_gencbvex2 a_sup_set_class a_wceq a_wa f4_gencbvex2 a_wex p_impbii f0_gencbvex2 f1_gencbvex2 f2_gencbvex2 f3_gencbvex2 f4_gencbvex2 f5_gencbvex2 f6_gencbvex2 p_gencbvex $.
$}

$(Change of bound variable using implicit substitution.  (Contributed by
       NM, 17-May-1996.) $)

${
	$v ph ps ch th x y A  $.
	$d x ps  $.
	$d y ph  $.
	$d x th  $.
	$d y ch  $.
	$d y A  $.
	f0_gencbval $f wff ph $.
	f1_gencbval $f wff ps $.
	f2_gencbval $f wff ch $.
	f3_gencbval $f wff th $.
	f4_gencbval $f set x $.
	f5_gencbval $f set y $.
	f6_gencbval $f class A $.
	e0_gencbval $e |- A e. _V $.
	e1_gencbval $e |- ( A = y -> ( ph <-> ps ) ) $.
	e2_gencbval $e |- ( A = y -> ( ch <-> th ) ) $.
	e3_gencbval $e |- ( th <-> E. x ( ch /\ A = y ) ) $.
	p_gencbval $p |- ( A. x ( ch -> ph ) <-> A. y ( th -> ps ) ) $= e0_gencbval e1_gencbval f6_gencbval f5_gencbval a_sup_set_class a_wceq f0_gencbval f1_gencbval p_notbid e2_gencbval e3_gencbval f0_gencbval a_wn f1_gencbval a_wn f2_gencbval f3_gencbval f4_gencbval f5_gencbval f6_gencbval p_gencbvex f2_gencbval f0_gencbval f4_gencbval p_exanali f3_gencbval f1_gencbval f5_gencbval p_exanali f2_gencbval f0_gencbval a_wn a_wa f4_gencbval a_wex f3_gencbval f1_gencbval a_wn a_wa f5_gencbval a_wex f2_gencbval f0_gencbval a_wi f4_gencbval a_wal a_wn f3_gencbval f1_gencbval a_wi f5_gencbval a_wal a_wn p_3bitr3i f2_gencbval f0_gencbval a_wi f4_gencbval a_wal f3_gencbval f1_gencbval a_wi f5_gencbval a_wal p_con4bii $.
$}

$(Introduce an explicit substitution into an implicit substitution
       hypothesis.  See also ~ csbhypf .  (Contributed by Raph Levien,
       10-Apr-2004.) $)

${
	$v ph ps x y A  $.
	$d A x  $.
	$d x y  $.
	f0_sbhypf $f wff ph $.
	f1_sbhypf $f wff ps $.
	f2_sbhypf $f set x $.
	f3_sbhypf $f set y $.
	f4_sbhypf $f class A $.
	e0_sbhypf $e |- F/ x ps $.
	e1_sbhypf $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_sbhypf $p |- ( y = A -> ( [ y / x ] ph <-> ps ) ) $= f3_sbhypf p_vex f2_sbhypf a_sup_set_class f3_sbhypf a_sup_set_class f4_sbhypf p_eqeq1 f2_sbhypf a_sup_set_class f4_sbhypf a_wceq f3_sbhypf a_sup_set_class f4_sbhypf a_wceq f2_sbhypf f3_sbhypf a_sup_set_class p_ceqsexv f0_sbhypf f2_sbhypf f3_sbhypf p_nfs1v e0_sbhypf f0_sbhypf f2_sbhypf f3_sbhypf a_wsb f1_sbhypf f2_sbhypf p_nfbi f0_sbhypf f2_sbhypf f3_sbhypf p_sbequ12 f2_sbhypf a_sup_set_class f3_sbhypf a_sup_set_class a_wceq f0_sbhypf f0_sbhypf f2_sbhypf f3_sbhypf a_wsb p_bicomd e1_sbhypf f2_sbhypf a_sup_set_class f3_sbhypf a_sup_set_class a_wceq f0_sbhypf f2_sbhypf f3_sbhypf a_wsb f0_sbhypf f2_sbhypf a_sup_set_class f4_sbhypf a_wceq f1_sbhypf p_sylan9bb f2_sbhypf a_sup_set_class f3_sbhypf a_sup_set_class a_wceq f2_sbhypf a_sup_set_class f4_sbhypf a_wceq a_wa f0_sbhypf f2_sbhypf f3_sbhypf a_wsb f1_sbhypf a_wb f2_sbhypf p_exlimi f3_sbhypf a_sup_set_class f4_sbhypf a_wceq f2_sbhypf a_sup_set_class f3_sbhypf a_sup_set_class a_wceq f2_sbhypf a_sup_set_class f4_sbhypf a_wceq a_wa f2_sbhypf a_wex f0_sbhypf f2_sbhypf f3_sbhypf a_wsb f1_sbhypf a_wb p_sylbir $.
$}

$(Closed theorem form of ~ vtoclgf .  (Contributed by NM, 17-Feb-2013.)
       (Revised by Mario Carneiro, 12-Oct-2016.) $)

${
	$v ph ps x A V  $.
	$d z A  $.
	$d x z  $.
	$d z  $.
	f0_vtoclgft $f wff ph $.
	f1_vtoclgft $f wff ps $.
	f2_vtoclgft $f set x $.
	f3_vtoclgft $f class A $.
	f4_vtoclgft $f class V $.
	i0_vtoclgft $f set z $.
	p_vtoclgft $p |- ( ( ( F/_ x A /\ F/ x ps ) /\ ( A. x ( x = A -> ( ph <-> ps ) ) /\ A. x ph ) /\ A e. V ) -> ps ) $= f3_vtoclgft f4_vtoclgft p_elex i0_vtoclgft f3_vtoclgft a_cvv p_elisset f3_vtoclgft a_cvv a_wcel f2_vtoclgft f3_vtoclgft a_wnfc f1_vtoclgft f2_vtoclgft a_wnf a_wa i0_vtoclgft a_sup_set_class f3_vtoclgft a_wceq i0_vtoclgft a_wex f2_vtoclgft a_sup_set_class f3_vtoclgft a_wceq f0_vtoclgft f1_vtoclgft a_wb a_wi f2_vtoclgft a_wal f0_vtoclgft f2_vtoclgft a_wal a_wa p_3ad2ant3 f2_vtoclgft f3_vtoclgft p_nfnfc1 f2_vtoclgft f3_vtoclgft a_wnfc f2_vtoclgft i0_vtoclgft a_sup_set_class p_nfcvd f2_vtoclgft f3_vtoclgft a_wnfc p_id f2_vtoclgft f3_vtoclgft a_wnfc f2_vtoclgft i0_vtoclgft a_sup_set_class f3_vtoclgft p_nfeqd i0_vtoclgft a_sup_set_class f2_vtoclgft a_sup_set_class f3_vtoclgft p_eqeq1 i0_vtoclgft a_sup_set_class f2_vtoclgft a_sup_set_class a_wceq i0_vtoclgft a_sup_set_class f3_vtoclgft a_wceq f2_vtoclgft a_sup_set_class f3_vtoclgft a_wceq a_wb a_wi f2_vtoclgft f3_vtoclgft a_wnfc p_a1i f2_vtoclgft f3_vtoclgft a_wnfc i0_vtoclgft a_sup_set_class f3_vtoclgft a_wceq f2_vtoclgft a_sup_set_class f3_vtoclgft a_wceq i0_vtoclgft f2_vtoclgft p_cbvexd f2_vtoclgft f3_vtoclgft a_wnfc i0_vtoclgft a_sup_set_class f3_vtoclgft a_wceq i0_vtoclgft a_wex f2_vtoclgft a_sup_set_class f3_vtoclgft a_wceq f2_vtoclgft a_wex a_wb f1_vtoclgft f2_vtoclgft a_wnf f2_vtoclgft a_sup_set_class f3_vtoclgft a_wceq f0_vtoclgft f1_vtoclgft a_wb a_wi f2_vtoclgft a_wal f0_vtoclgft f2_vtoclgft a_wal a_wa p_ad2antrr f2_vtoclgft f3_vtoclgft a_wnfc f1_vtoclgft f2_vtoclgft a_wnf a_wa f2_vtoclgft a_sup_set_class f3_vtoclgft a_wceq f0_vtoclgft f1_vtoclgft a_wb a_wi f2_vtoclgft a_wal f0_vtoclgft f2_vtoclgft a_wal a_wa i0_vtoclgft a_sup_set_class f3_vtoclgft a_wceq i0_vtoclgft a_wex f2_vtoclgft a_sup_set_class f3_vtoclgft a_wceq f2_vtoclgft a_wex a_wb f3_vtoclgft a_cvv a_wcel p_3adant3 f2_vtoclgft f3_vtoclgft a_wnfc f1_vtoclgft f2_vtoclgft a_wnf a_wa f2_vtoclgft a_sup_set_class f3_vtoclgft a_wceq f0_vtoclgft f1_vtoclgft a_wb a_wi f2_vtoclgft a_wal f0_vtoclgft f2_vtoclgft a_wal a_wa f3_vtoclgft a_cvv a_wcel a_w3a i0_vtoclgft a_sup_set_class f3_vtoclgft a_wceq i0_vtoclgft a_wex f2_vtoclgft a_sup_set_class f3_vtoclgft a_wceq f2_vtoclgft a_wex p_mpbid f0_vtoclgft f1_vtoclgft p_bi1 f0_vtoclgft f1_vtoclgft a_wb f0_vtoclgft f1_vtoclgft a_wi f2_vtoclgft a_sup_set_class f3_vtoclgft a_wceq p_imim2i f2_vtoclgft a_sup_set_class f3_vtoclgft a_wceq f0_vtoclgft f1_vtoclgft a_wb a_wi f2_vtoclgft a_sup_set_class f3_vtoclgft a_wceq f0_vtoclgft f1_vtoclgft p_com23 f2_vtoclgft a_sup_set_class f3_vtoclgft a_wceq f0_vtoclgft f1_vtoclgft a_wb a_wi f0_vtoclgft f2_vtoclgft a_sup_set_class f3_vtoclgft a_wceq f1_vtoclgft a_wi p_imp f2_vtoclgft a_sup_set_class f3_vtoclgft a_wceq f0_vtoclgft f1_vtoclgft a_wb a_wi f0_vtoclgft f2_vtoclgft a_sup_set_class f3_vtoclgft a_wceq f1_vtoclgft a_wi f2_vtoclgft p_alanimi f2_vtoclgft a_sup_set_class f3_vtoclgft a_wceq f0_vtoclgft f1_vtoclgft a_wb a_wi f2_vtoclgft a_wal f0_vtoclgft f2_vtoclgft a_wal a_wa f2_vtoclgft f3_vtoclgft a_wnfc f1_vtoclgft f2_vtoclgft a_wnf a_wa f2_vtoclgft a_sup_set_class f3_vtoclgft a_wceq f1_vtoclgft a_wi f2_vtoclgft a_wal f3_vtoclgft a_cvv a_wcel p_3ad2ant2 f2_vtoclgft f3_vtoclgft a_wnfc f1_vtoclgft f2_vtoclgft a_wnf f2_vtoclgft a_sup_set_class f3_vtoclgft a_wceq f0_vtoclgft f1_vtoclgft a_wb a_wi f2_vtoclgft a_wal f0_vtoclgft f2_vtoclgft a_wal a_wa f3_vtoclgft a_cvv a_wcel p_simp1r f2_vtoclgft a_sup_set_class f3_vtoclgft a_wceq f1_vtoclgft f2_vtoclgft p_19.23t f2_vtoclgft f3_vtoclgft a_wnfc f1_vtoclgft f2_vtoclgft a_wnf a_wa f2_vtoclgft a_sup_set_class f3_vtoclgft a_wceq f0_vtoclgft f1_vtoclgft a_wb a_wi f2_vtoclgft a_wal f0_vtoclgft f2_vtoclgft a_wal a_wa f3_vtoclgft a_cvv a_wcel a_w3a f1_vtoclgft f2_vtoclgft a_wnf f2_vtoclgft a_sup_set_class f3_vtoclgft a_wceq f1_vtoclgft a_wi f2_vtoclgft a_wal f2_vtoclgft a_sup_set_class f3_vtoclgft a_wceq f2_vtoclgft a_wex f1_vtoclgft a_wi a_wb p_syl f2_vtoclgft f3_vtoclgft a_wnfc f1_vtoclgft f2_vtoclgft a_wnf a_wa f2_vtoclgft a_sup_set_class f3_vtoclgft a_wceq f0_vtoclgft f1_vtoclgft a_wb a_wi f2_vtoclgft a_wal f0_vtoclgft f2_vtoclgft a_wal a_wa f3_vtoclgft a_cvv a_wcel a_w3a f2_vtoclgft a_sup_set_class f3_vtoclgft a_wceq f1_vtoclgft a_wi f2_vtoclgft a_wal f2_vtoclgft a_sup_set_class f3_vtoclgft a_wceq f2_vtoclgft a_wex f1_vtoclgft a_wi p_mpbid f2_vtoclgft f3_vtoclgft a_wnfc f1_vtoclgft f2_vtoclgft a_wnf a_wa f2_vtoclgft a_sup_set_class f3_vtoclgft a_wceq f0_vtoclgft f1_vtoclgft a_wb a_wi f2_vtoclgft a_wal f0_vtoclgft f2_vtoclgft a_wal a_wa f3_vtoclgft a_cvv a_wcel a_w3a f2_vtoclgft a_sup_set_class f3_vtoclgft a_wceq f2_vtoclgft a_wex f1_vtoclgft p_mpd f3_vtoclgft f4_vtoclgft a_wcel f2_vtoclgft f3_vtoclgft a_wnfc f1_vtoclgft f2_vtoclgft a_wnf a_wa f2_vtoclgft a_sup_set_class f3_vtoclgft a_wceq f0_vtoclgft f1_vtoclgft a_wb a_wi f2_vtoclgft a_wal f0_vtoclgft f2_vtoclgft a_wal a_wa f3_vtoclgft a_cvv a_wcel f1_vtoclgft p_syl3an3 $.
$}

$(Implicit substitution of a class for a set variable.  (Contributed by
         Mario Carneiro, 15-Oct-2016.) $)

${
	$v ph ps ch x A V  $.
	f0_vtocldf $f wff ph $.
	f1_vtocldf $f wff ps $.
	f2_vtocldf $f wff ch $.
	f3_vtocldf $f set x $.
	f4_vtocldf $f class A $.
	f5_vtocldf $f class V $.
	e0_vtocldf $e |- ( ph -> A e. V ) $.
	e1_vtocldf $e |- ( ( ph /\ x = A ) -> ( ps <-> ch ) ) $.
	e2_vtocldf $e |- ( ph -> ps ) $.
	e3_vtocldf $e |- F/ x ph $.
	e4_vtocldf $e |- ( ph -> F/_ x A ) $.
	e5_vtocldf $e |- ( ph -> F/ x ch ) $.
	p_vtocldf $p |- ( ph -> ch ) $= e4_vtocldf e5_vtocldf e3_vtocldf e1_vtocldf f0_vtocldf f3_vtocldf a_sup_set_class f4_vtocldf a_wceq f1_vtocldf f2_vtocldf a_wb p_ex f0_vtocldf f3_vtocldf a_sup_set_class f4_vtocldf a_wceq f1_vtocldf f2_vtocldf a_wb a_wi f3_vtocldf p_alrimi e3_vtocldf e2_vtocldf f0_vtocldf f1_vtocldf f3_vtocldf p_alrimi e0_vtocldf f1_vtocldf f2_vtocldf f3_vtocldf f4_vtocldf f5_vtocldf p_vtoclgft f0_vtocldf f3_vtocldf f4_vtocldf a_wnfc f2_vtocldf f3_vtocldf a_wnf f3_vtocldf a_sup_set_class f4_vtocldf a_wceq f1_vtocldf f2_vtocldf a_wb a_wi f3_vtocldf a_wal f1_vtocldf f3_vtocldf a_wal f4_vtocldf f5_vtocldf a_wcel f2_vtocldf p_syl221anc $.
$}

$(Implicit substitution of a class for a set variable.  (Contributed by
       Mario Carneiro, 15-Oct-2016.) $)

${
	$v ph ps ch x A V  $.
	$d x A  $.
	$d x ph  $.
	$d x ch  $.
	f0_vtocld $f wff ph $.
	f1_vtocld $f wff ps $.
	f2_vtocld $f wff ch $.
	f3_vtocld $f set x $.
	f4_vtocld $f class A $.
	f5_vtocld $f class V $.
	e0_vtocld $e |- ( ph -> A e. V ) $.
	e1_vtocld $e |- ( ( ph /\ x = A ) -> ( ps <-> ch ) ) $.
	e2_vtocld $e |- ( ph -> ps ) $.
	p_vtocld $p |- ( ph -> ch ) $= e0_vtocld e1_vtocld e2_vtocld f0_vtocld f3_vtocld p_nfv f0_vtocld f3_vtocld f4_vtocld p_nfcvd f0_vtocld f2_vtocld f3_vtocld p_nfvd f0_vtocld f1_vtocld f2_vtocld f3_vtocld f4_vtocld f5_vtocld p_vtocldf $.
$}

$(Implicit substitution of a class for a set variable.  This is a
       generalization of ~ chvar .  (Contributed by NM, 30-Aug-1993.) $)

${
	$v ph ps x A  $.
	$d x A  $.
	f0_vtoclf $f wff ph $.
	f1_vtoclf $f wff ps $.
	f2_vtoclf $f set x $.
	f3_vtoclf $f class A $.
	e0_vtoclf $e |- F/ x ps $.
	e1_vtoclf $e |- A e. _V $.
	e2_vtoclf $e |- ( x = A -> ( ph <-> ps ) ) $.
	e3_vtoclf $e |- ph $.
	p_vtoclf $p |- ps $= e0_vtoclf e1_vtoclf f2_vtoclf f3_vtoclf p_isseti e2_vtoclf f2_vtoclf a_sup_set_class f3_vtoclf a_wceq f0_vtoclf f1_vtoclf p_biimpd f2_vtoclf a_sup_set_class f3_vtoclf a_wceq f0_vtoclf f1_vtoclf a_wi f2_vtoclf p_eximi f2_vtoclf a_sup_set_class f3_vtoclf a_wceq f2_vtoclf a_wex f0_vtoclf f1_vtoclf a_wi f2_vtoclf a_wex a_ax-mp f0_vtoclf f1_vtoclf f2_vtoclf p_19.36i e3_vtoclf f0_vtoclf f1_vtoclf f2_vtoclf p_mpg $.
$}

$(Implicit substitution of a class for a set variable.  (Contributed by
       NM, 30-Aug-1993.) $)

${
	$v ph ps x A  $.
	$d x A  $.
	$d x ps  $.
	f0_vtocl $f wff ph $.
	f1_vtocl $f wff ps $.
	f2_vtocl $f set x $.
	f3_vtocl $f class A $.
	e0_vtocl $e |- A e. _V $.
	e1_vtocl $e |- ( x = A -> ( ph <-> ps ) ) $.
	e2_vtocl $e |- ph $.
	p_vtocl $p |- ps $= f1_vtocl f2_vtocl p_nfv e0_vtocl e1_vtocl e2_vtocl f0_vtocl f1_vtocl f2_vtocl f3_vtocl p_vtoclf $.
$}

$(Implicit substitution of classes for set variables.  (Contributed by NM,
       26-Jul-1995.)  (Proof shortened by Andrew Salmon, 8-Jun-2011.) $)

${
	$v ph ps x y A B  $.
	$d x y A  $.
	$d x y B  $.
	$d x y ps  $.
	f0_vtocl2 $f wff ph $.
	f1_vtocl2 $f wff ps $.
	f2_vtocl2 $f set x $.
	f3_vtocl2 $f set y $.
	f4_vtocl2 $f class A $.
	f5_vtocl2 $f class B $.
	e0_vtocl2 $e |- A e. _V $.
	e1_vtocl2 $e |- B e. _V $.
	e2_vtocl2 $e |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) ) $.
	e3_vtocl2 $e |- ph $.
	p_vtocl2 $p |- ps $= e0_vtocl2 f2_vtocl2 f4_vtocl2 p_isseti e1_vtocl2 f3_vtocl2 f5_vtocl2 p_isseti f2_vtocl2 a_sup_set_class f4_vtocl2 a_wceq f3_vtocl2 a_sup_set_class f5_vtocl2 a_wceq f2_vtocl2 f3_vtocl2 p_eeanv e2_vtocl2 f2_vtocl2 a_sup_set_class f4_vtocl2 a_wceq f3_vtocl2 a_sup_set_class f5_vtocl2 a_wceq a_wa f0_vtocl2 f1_vtocl2 p_biimpd f2_vtocl2 a_sup_set_class f4_vtocl2 a_wceq f3_vtocl2 a_sup_set_class f5_vtocl2 a_wceq a_wa f0_vtocl2 f1_vtocl2 a_wi f2_vtocl2 f3_vtocl2 p_2eximi f2_vtocl2 a_sup_set_class f4_vtocl2 a_wceq f2_vtocl2 a_wex f3_vtocl2 a_sup_set_class f5_vtocl2 a_wceq f3_vtocl2 a_wex a_wa f2_vtocl2 a_sup_set_class f4_vtocl2 a_wceq f3_vtocl2 a_sup_set_class f5_vtocl2 a_wceq a_wa f3_vtocl2 a_wex f2_vtocl2 a_wex f0_vtocl2 f1_vtocl2 a_wi f3_vtocl2 a_wex f2_vtocl2 a_wex p_sylbir f2_vtocl2 a_sup_set_class f4_vtocl2 a_wceq f2_vtocl2 a_wex f3_vtocl2 a_sup_set_class f5_vtocl2 a_wceq f3_vtocl2 a_wex f0_vtocl2 f1_vtocl2 a_wi f3_vtocl2 a_wex f2_vtocl2 a_wex p_mp2an f0_vtocl2 f1_vtocl2 f3_vtocl2 p_19.36v f0_vtocl2 f1_vtocl2 a_wi f3_vtocl2 a_wex f0_vtocl2 f3_vtocl2 a_wal f1_vtocl2 a_wi f2_vtocl2 p_exbii f0_vtocl2 f1_vtocl2 a_wi f3_vtocl2 a_wex f2_vtocl2 a_wex f0_vtocl2 f3_vtocl2 a_wal f1_vtocl2 a_wi f2_vtocl2 a_wex p_mpbi f0_vtocl2 f3_vtocl2 a_wal f1_vtocl2 f2_vtocl2 p_19.36aiv e3_vtocl2 f0_vtocl2 f3_vtocl2 a_ax-gen f0_vtocl2 f3_vtocl2 a_wal f1_vtocl2 f2_vtocl2 p_mpg $.
$}

$(Implicit substitution of classes for set variables.  (Contributed by NM,
       3-Jun-1995.)  (Proof shortened by Andrew Salmon, 8-Jun-2011.) $)

${
	$v ph ps x y z A B C  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x y z ps  $.
	f0_vtocl3 $f wff ph $.
	f1_vtocl3 $f wff ps $.
	f2_vtocl3 $f set x $.
	f3_vtocl3 $f set y $.
	f4_vtocl3 $f set z $.
	f5_vtocl3 $f class A $.
	f6_vtocl3 $f class B $.
	f7_vtocl3 $f class C $.
	e0_vtocl3 $e |- A e. _V $.
	e1_vtocl3 $e |- B e. _V $.
	e2_vtocl3 $e |- C e. _V $.
	e3_vtocl3 $e |- ( ( x = A /\ y = B /\ z = C ) -> ( ph <-> ps ) ) $.
	e4_vtocl3 $e |- ph $.
	p_vtocl3 $p |- ps $= e0_vtocl3 f2_vtocl3 f5_vtocl3 p_isseti e1_vtocl3 f3_vtocl3 f6_vtocl3 p_isseti e2_vtocl3 f4_vtocl3 f7_vtocl3 p_isseti f2_vtocl3 a_sup_set_class f5_vtocl3 a_wceq f3_vtocl3 a_sup_set_class f6_vtocl3 a_wceq f4_vtocl3 a_sup_set_class f7_vtocl3 a_wceq f2_vtocl3 f3_vtocl3 f4_vtocl3 p_eeeanv e3_vtocl3 f2_vtocl3 a_sup_set_class f5_vtocl3 a_wceq f3_vtocl3 a_sup_set_class f6_vtocl3 a_wceq f4_vtocl3 a_sup_set_class f7_vtocl3 a_wceq a_w3a f0_vtocl3 f1_vtocl3 p_biimpd f2_vtocl3 a_sup_set_class f5_vtocl3 a_wceq f3_vtocl3 a_sup_set_class f6_vtocl3 a_wceq f4_vtocl3 a_sup_set_class f7_vtocl3 a_wceq a_w3a f0_vtocl3 f1_vtocl3 a_wi f4_vtocl3 p_eximi f2_vtocl3 a_sup_set_class f5_vtocl3 a_wceq f3_vtocl3 a_sup_set_class f6_vtocl3 a_wceq f4_vtocl3 a_sup_set_class f7_vtocl3 a_wceq a_w3a f4_vtocl3 a_wex f0_vtocl3 f1_vtocl3 a_wi f4_vtocl3 a_wex f2_vtocl3 f3_vtocl3 p_2eximi f2_vtocl3 a_sup_set_class f5_vtocl3 a_wceq f2_vtocl3 a_wex f3_vtocl3 a_sup_set_class f6_vtocl3 a_wceq f3_vtocl3 a_wex f4_vtocl3 a_sup_set_class f7_vtocl3 a_wceq f4_vtocl3 a_wex a_w3a f2_vtocl3 a_sup_set_class f5_vtocl3 a_wceq f3_vtocl3 a_sup_set_class f6_vtocl3 a_wceq f4_vtocl3 a_sup_set_class f7_vtocl3 a_wceq a_w3a f4_vtocl3 a_wex f3_vtocl3 a_wex f2_vtocl3 a_wex f0_vtocl3 f1_vtocl3 a_wi f4_vtocl3 a_wex f3_vtocl3 a_wex f2_vtocl3 a_wex p_sylbir f2_vtocl3 a_sup_set_class f5_vtocl3 a_wceq f2_vtocl3 a_wex f3_vtocl3 a_sup_set_class f6_vtocl3 a_wceq f3_vtocl3 a_wex f4_vtocl3 a_sup_set_class f7_vtocl3 a_wceq f4_vtocl3 a_wex f0_vtocl3 f1_vtocl3 a_wi f4_vtocl3 a_wex f3_vtocl3 a_wex f2_vtocl3 a_wex p_mp3an f0_vtocl3 f1_vtocl3 f4_vtocl3 p_19.36v f0_vtocl3 f1_vtocl3 a_wi f4_vtocl3 a_wex f0_vtocl3 f4_vtocl3 a_wal f1_vtocl3 a_wi f2_vtocl3 f3_vtocl3 p_2exbii f0_vtocl3 f1_vtocl3 a_wi f4_vtocl3 a_wex f3_vtocl3 a_wex f2_vtocl3 a_wex f0_vtocl3 f4_vtocl3 a_wal f1_vtocl3 a_wi f3_vtocl3 a_wex f2_vtocl3 a_wex p_mpbi f0_vtocl3 f4_vtocl3 a_wal f1_vtocl3 f3_vtocl3 p_19.36v f0_vtocl3 f4_vtocl3 a_wal f1_vtocl3 a_wi f3_vtocl3 a_wex f0_vtocl3 f4_vtocl3 a_wal f3_vtocl3 a_wal f1_vtocl3 a_wi f2_vtocl3 p_exbii f0_vtocl3 f4_vtocl3 a_wal f1_vtocl3 a_wi f3_vtocl3 a_wex f2_vtocl3 a_wex f0_vtocl3 f4_vtocl3 a_wal f3_vtocl3 a_wal f1_vtocl3 a_wi f2_vtocl3 a_wex p_mpbi f0_vtocl3 f4_vtocl3 a_wal f3_vtocl3 a_wal f1_vtocl3 f2_vtocl3 p_19.36aiv e4_vtocl3 f0_vtocl3 f3_vtocl3 f4_vtocl3 p_gen2 f0_vtocl3 f4_vtocl3 a_wal f3_vtocl3 a_wal f1_vtocl3 f2_vtocl3 p_mpg $.
$}

$(Implicit substitution of a class for a set variable.  (Contributed by
       NM, 23-Dec-1993.) $)

${
	$v ph ps ch th x A  $.
	$d x A  $.
	$d x ch  $.
	$d x th  $.
	f0_vtoclb $f wff ph $.
	f1_vtoclb $f wff ps $.
	f2_vtoclb $f wff ch $.
	f3_vtoclb $f wff th $.
	f4_vtoclb $f set x $.
	f5_vtoclb $f class A $.
	e0_vtoclb $e |- A e. _V $.
	e1_vtoclb $e |- ( x = A -> ( ph <-> ch ) ) $.
	e2_vtoclb $e |- ( x = A -> ( ps <-> th ) ) $.
	e3_vtoclb $e |- ( ph <-> ps ) $.
	p_vtoclb $p |- ( ch <-> th ) $= e0_vtoclb e1_vtoclb e2_vtoclb f4_vtoclb a_sup_set_class f5_vtoclb a_wceq f0_vtoclb f2_vtoclb f1_vtoclb f3_vtoclb p_bibi12d e3_vtoclb f0_vtoclb f1_vtoclb a_wb f2_vtoclb f3_vtoclb a_wb f4_vtoclb f5_vtoclb p_vtocl $.
$}

$(Implicit substitution of a class for a set variable, with bound-variable
       hypotheses in place of distinct variable restrictions.  (Contributed by
       NM, 21-Sep-2003.)  (Proof shortened by Mario Carneiro, 10-Oct-2016.) $)

${
	$v ph ps x A V  $.
	f0_vtoclgf $f wff ph $.
	f1_vtoclgf $f wff ps $.
	f2_vtoclgf $f set x $.
	f3_vtoclgf $f class A $.
	f4_vtoclgf $f class V $.
	e0_vtoclgf $e |- F/_ x A $.
	e1_vtoclgf $e |- F/ x ps $.
	e2_vtoclgf $e |- ( x = A -> ( ph <-> ps ) ) $.
	e3_vtoclgf $e |- ph $.
	p_vtoclgf $p |- ( A e. V -> ps ) $= f3_vtoclgf f4_vtoclgf p_elex e0_vtoclgf f2_vtoclgf f3_vtoclgf p_issetf e1_vtoclgf e3_vtoclgf e2_vtoclgf f2_vtoclgf a_sup_set_class f3_vtoclgf a_wceq f0_vtoclgf f1_vtoclgf p_mpbii f2_vtoclgf a_sup_set_class f3_vtoclgf a_wceq f1_vtoclgf f2_vtoclgf p_exlimi f3_vtoclgf a_cvv a_wcel f2_vtoclgf a_sup_set_class f3_vtoclgf a_wceq f2_vtoclgf a_wex f1_vtoclgf p_sylbi f3_vtoclgf f4_vtoclgf a_wcel f3_vtoclgf a_cvv a_wcel f1_vtoclgf p_syl $.
$}

$(Implicit substitution of a class expression for a set variable.
       (Contributed by NM, 17-Apr-1995.) $)

${
	$v ph ps x A V  $.
	$d x A  $.
	$d x ps  $.
	f0_vtoclg $f wff ph $.
	f1_vtoclg $f wff ps $.
	f2_vtoclg $f set x $.
	f3_vtoclg $f class A $.
	f4_vtoclg $f class V $.
	e0_vtoclg $e |- ( x = A -> ( ph <-> ps ) ) $.
	e1_vtoclg $e |- ph $.
	p_vtoclg $p |- ( A e. V -> ps ) $= f2_vtoclg f3_vtoclg p_nfcv f1_vtoclg f2_vtoclg p_nfv e0_vtoclg e1_vtoclg f0_vtoclg f1_vtoclg f2_vtoclg f3_vtoclg f4_vtoclg p_vtoclgf $.
$}

$(Implicit substitution of a class for a set variable.  (Contributed by
       NM, 29-Apr-1994.) $)

${
	$v ph ps ch th x A V  $.
	$d x A  $.
	$d x ch  $.
	$d x th  $.
	f0_vtoclbg $f wff ph $.
	f1_vtoclbg $f wff ps $.
	f2_vtoclbg $f wff ch $.
	f3_vtoclbg $f wff th $.
	f4_vtoclbg $f set x $.
	f5_vtoclbg $f class A $.
	f6_vtoclbg $f class V $.
	e0_vtoclbg $e |- ( x = A -> ( ph <-> ch ) ) $.
	e1_vtoclbg $e |- ( x = A -> ( ps <-> th ) ) $.
	e2_vtoclbg $e |- ( ph <-> ps ) $.
	p_vtoclbg $p |- ( A e. V -> ( ch <-> th ) ) $= e0_vtoclbg e1_vtoclbg f4_vtoclbg a_sup_set_class f5_vtoclbg a_wceq f0_vtoclbg f2_vtoclbg f1_vtoclbg f3_vtoclbg p_bibi12d e2_vtoclbg f0_vtoclbg f1_vtoclbg a_wb f2_vtoclbg f3_vtoclbg a_wb f4_vtoclbg f5_vtoclbg f6_vtoclbg p_vtoclg $.
$}

$(Implicit substitution of a class for a set variable.  (Contributed by
       NM, 25-Apr-1995.) $)

${
	$v ph ps ch x y A B V W  $.
	f0_vtocl2gf $f wff ph $.
	f1_vtocl2gf $f wff ps $.
	f2_vtocl2gf $f wff ch $.
	f3_vtocl2gf $f set x $.
	f4_vtocl2gf $f set y $.
	f5_vtocl2gf $f class A $.
	f6_vtocl2gf $f class B $.
	f7_vtocl2gf $f class V $.
	f8_vtocl2gf $f class W $.
	e0_vtocl2gf $e |- F/_ x A $.
	e1_vtocl2gf $e |- F/_ y A $.
	e2_vtocl2gf $e |- F/_ y B $.
	e3_vtocl2gf $e |- F/ x ps $.
	e4_vtocl2gf $e |- F/ y ch $.
	e5_vtocl2gf $e |- ( x = A -> ( ph <-> ps ) ) $.
	e6_vtocl2gf $e |- ( y = B -> ( ps <-> ch ) ) $.
	e7_vtocl2gf $e |- ph $.
	p_vtocl2gf $p |- ( ( A e. V /\ B e. W ) -> ch ) $= f5_vtocl2gf f7_vtocl2gf p_elex e2_vtocl2gf e1_vtocl2gf f4_vtocl2gf f5_vtocl2gf a_cvv p_nfel1 e4_vtocl2gf f5_vtocl2gf a_cvv a_wcel f2_vtocl2gf f4_vtocl2gf p_nfim e6_vtocl2gf f4_vtocl2gf a_sup_set_class f6_vtocl2gf a_wceq f1_vtocl2gf f2_vtocl2gf f5_vtocl2gf a_cvv a_wcel p_imbi2d e0_vtocl2gf e3_vtocl2gf e5_vtocl2gf e7_vtocl2gf f0_vtocl2gf f1_vtocl2gf f3_vtocl2gf f5_vtocl2gf a_cvv p_vtoclgf f5_vtocl2gf a_cvv a_wcel f1_vtocl2gf a_wi f5_vtocl2gf a_cvv a_wcel f2_vtocl2gf a_wi f4_vtocl2gf f6_vtocl2gf f8_vtocl2gf p_vtoclgf f5_vtocl2gf f7_vtocl2gf a_wcel f5_vtocl2gf a_cvv a_wcel f6_vtocl2gf f8_vtocl2gf a_wcel f2_vtocl2gf p_mpan9 $.
$}

$(Implicit substitution of a class for a set variable.  (Contributed by
       NM, 10-Aug-2013.)  (Revised by Mario Carneiro, 10-Oct-2016.) $)

${
	$v ph ps ch th x y z A B C V W X  $.
	$d A  $.
	$d B  $.
	$d C  $.
	$d y  $.
	$d z  $.
	f0_vtocl3gf $f wff ph $.
	f1_vtocl3gf $f wff ps $.
	f2_vtocl3gf $f wff ch $.
	f3_vtocl3gf $f wff th $.
	f4_vtocl3gf $f set x $.
	f5_vtocl3gf $f set y $.
	f6_vtocl3gf $f set z $.
	f7_vtocl3gf $f class A $.
	f8_vtocl3gf $f class B $.
	f9_vtocl3gf $f class C $.
	f10_vtocl3gf $f class V $.
	f11_vtocl3gf $f class W $.
	f12_vtocl3gf $f class X $.
	e0_vtocl3gf $e |- F/_ x A $.
	e1_vtocl3gf $e |- F/_ y A $.
	e2_vtocl3gf $e |- F/_ z A $.
	e3_vtocl3gf $e |- F/_ y B $.
	e4_vtocl3gf $e |- F/_ z B $.
	e5_vtocl3gf $e |- F/_ z C $.
	e6_vtocl3gf $e |- F/ x ps $.
	e7_vtocl3gf $e |- F/ y ch $.
	e8_vtocl3gf $e |- F/ z th $.
	e9_vtocl3gf $e |- ( x = A -> ( ph <-> ps ) ) $.
	e10_vtocl3gf $e |- ( y = B -> ( ps <-> ch ) ) $.
	e11_vtocl3gf $e |- ( z = C -> ( ch <-> th ) ) $.
	e12_vtocl3gf $e |- ph $.
	p_vtocl3gf $p |- ( ( A e. V /\ B e. W /\ C e. X ) -> th ) $= f7_vtocl3gf f10_vtocl3gf p_elex e3_vtocl3gf e4_vtocl3gf e5_vtocl3gf e1_vtocl3gf f5_vtocl3gf f7_vtocl3gf a_cvv p_nfel1 e7_vtocl3gf f7_vtocl3gf a_cvv a_wcel f2_vtocl3gf f5_vtocl3gf p_nfim e2_vtocl3gf f6_vtocl3gf f7_vtocl3gf a_cvv p_nfel1 e8_vtocl3gf f7_vtocl3gf a_cvv a_wcel f3_vtocl3gf f6_vtocl3gf p_nfim e10_vtocl3gf f5_vtocl3gf a_sup_set_class f8_vtocl3gf a_wceq f1_vtocl3gf f2_vtocl3gf f7_vtocl3gf a_cvv a_wcel p_imbi2d e11_vtocl3gf f6_vtocl3gf a_sup_set_class f9_vtocl3gf a_wceq f2_vtocl3gf f3_vtocl3gf f7_vtocl3gf a_cvv a_wcel p_imbi2d e0_vtocl3gf e6_vtocl3gf e9_vtocl3gf e12_vtocl3gf f0_vtocl3gf f1_vtocl3gf f4_vtocl3gf f7_vtocl3gf a_cvv p_vtoclgf f7_vtocl3gf a_cvv a_wcel f1_vtocl3gf a_wi f7_vtocl3gf a_cvv a_wcel f2_vtocl3gf a_wi f7_vtocl3gf a_cvv a_wcel f3_vtocl3gf a_wi f5_vtocl3gf f6_vtocl3gf f8_vtocl3gf f9_vtocl3gf f11_vtocl3gf f12_vtocl3gf p_vtocl2gf f7_vtocl3gf f10_vtocl3gf a_wcel f7_vtocl3gf a_cvv a_wcel f8_vtocl3gf f11_vtocl3gf a_wcel f9_vtocl3gf f12_vtocl3gf a_wcel a_wa f3_vtocl3gf p_mpan9 f7_vtocl3gf f10_vtocl3gf a_wcel f8_vtocl3gf f11_vtocl3gf a_wcel f9_vtocl3gf f12_vtocl3gf a_wcel f3_vtocl3gf p_3impb $.
$}

$(Implicit substitution of 2 classes for 2 set variables.  (Contributed by
       NM, 25-Apr-1995.) $)

${
	$v ph ps ch x y A B V W  $.
	$d x A  $.
	$d y A  $.
	$d y B  $.
	$d x ps  $.
	$d y ch  $.
	f0_vtocl2g $f wff ph $.
	f1_vtocl2g $f wff ps $.
	f2_vtocl2g $f wff ch $.
	f3_vtocl2g $f set x $.
	f4_vtocl2g $f set y $.
	f5_vtocl2g $f class A $.
	f6_vtocl2g $f class B $.
	f7_vtocl2g $f class V $.
	f8_vtocl2g $f class W $.
	e0_vtocl2g $e |- ( x = A -> ( ph <-> ps ) ) $.
	e1_vtocl2g $e |- ( y = B -> ( ps <-> ch ) ) $.
	e2_vtocl2g $e |- ph $.
	p_vtocl2g $p |- ( ( A e. V /\ B e. W ) -> ch ) $= f3_vtocl2g f5_vtocl2g p_nfcv f4_vtocl2g f5_vtocl2g p_nfcv f4_vtocl2g f6_vtocl2g p_nfcv f1_vtocl2g f3_vtocl2g p_nfv f2_vtocl2g f4_vtocl2g p_nfv e0_vtocl2g e1_vtocl2g e2_vtocl2g f0_vtocl2g f1_vtocl2g f2_vtocl2g f3_vtocl2g f4_vtocl2g f5_vtocl2g f6_vtocl2g f7_vtocl2g f8_vtocl2g p_vtocl2gf $.
$}

$(Implicit substitution of a class for a set variable.  (Contributed by
       NM, 17-Feb-2006.)  (Revised by Mario Carneiro, 10-Oct-2016.) $)

${
	$v ph ps x A B  $.
	$d A  $.
	$d x B  $.
	f0_vtoclgaf $f wff ph $.
	f1_vtoclgaf $f wff ps $.
	f2_vtoclgaf $f set x $.
	f3_vtoclgaf $f class A $.
	f4_vtoclgaf $f class B $.
	e0_vtoclgaf $e |- F/_ x A $.
	e1_vtoclgaf $e |- F/ x ps $.
	e2_vtoclgaf $e |- ( x = A -> ( ph <-> ps ) ) $.
	e3_vtoclgaf $e |- ( x e. B -> ph ) $.
	p_vtoclgaf $p |- ( A e. B -> ps ) $= e0_vtoclgaf e0_vtoclgaf f2_vtoclgaf f3_vtoclgaf f4_vtoclgaf p_nfel1 e1_vtoclgaf f3_vtoclgaf f4_vtoclgaf a_wcel f1_vtoclgaf f2_vtoclgaf p_nfim f2_vtoclgaf a_sup_set_class f3_vtoclgaf f4_vtoclgaf p_eleq1 e2_vtoclgaf f2_vtoclgaf a_sup_set_class f3_vtoclgaf a_wceq f2_vtoclgaf a_sup_set_class f4_vtoclgaf a_wcel f3_vtoclgaf f4_vtoclgaf a_wcel f0_vtoclgaf f1_vtoclgaf p_imbi12d e3_vtoclgaf f2_vtoclgaf a_sup_set_class f4_vtoclgaf a_wcel f0_vtoclgaf a_wi f3_vtoclgaf f4_vtoclgaf a_wcel f1_vtoclgaf a_wi f2_vtoclgaf f3_vtoclgaf f4_vtoclgaf p_vtoclgf f3_vtoclgaf f4_vtoclgaf a_wcel f1_vtoclgaf p_pm2.43i $.
$}

$(Implicit substitution of a class for a set variable.  (Contributed by
       NM, 20-Aug-1995.) $)

${
	$v ph ps x A B  $.
	$d x A  $.
	$d x B  $.
	$d x ps  $.
	f0_vtoclga $f wff ph $.
	f1_vtoclga $f wff ps $.
	f2_vtoclga $f set x $.
	f3_vtoclga $f class A $.
	f4_vtoclga $f class B $.
	e0_vtoclga $e |- ( x = A -> ( ph <-> ps ) ) $.
	e1_vtoclga $e |- ( x e. B -> ph ) $.
	p_vtoclga $p |- ( A e. B -> ps ) $= f2_vtoclga f3_vtoclga p_nfcv f1_vtoclga f2_vtoclga p_nfv e0_vtoclga e1_vtoclga f0_vtoclga f1_vtoclga f2_vtoclga f3_vtoclga f4_vtoclga p_vtoclgaf $.
$}

$(Implicit substitution of 2 classes for 2 set variables.  (Contributed by
       NM, 10-Aug-2013.) $)

${
	$v ph ps ch x y A B C D  $.
	$d x y C  $.
	$d x y D  $.
	f0_vtocl2gaf $f wff ph $.
	f1_vtocl2gaf $f wff ps $.
	f2_vtocl2gaf $f wff ch $.
	f3_vtocl2gaf $f set x $.
	f4_vtocl2gaf $f set y $.
	f5_vtocl2gaf $f class A $.
	f6_vtocl2gaf $f class B $.
	f7_vtocl2gaf $f class C $.
	f8_vtocl2gaf $f class D $.
	e0_vtocl2gaf $e |- F/_ x A $.
	e1_vtocl2gaf $e |- F/_ y A $.
	e2_vtocl2gaf $e |- F/_ y B $.
	e3_vtocl2gaf $e |- F/ x ps $.
	e4_vtocl2gaf $e |- F/ y ch $.
	e5_vtocl2gaf $e |- ( x = A -> ( ph <-> ps ) ) $.
	e6_vtocl2gaf $e |- ( y = B -> ( ps <-> ch ) ) $.
	e7_vtocl2gaf $e |- ( ( x e. C /\ y e. D ) -> ph ) $.
	p_vtocl2gaf $p |- ( ( A e. C /\ B e. D ) -> ch ) $= e0_vtocl2gaf e1_vtocl2gaf e2_vtocl2gaf e0_vtocl2gaf f3_vtocl2gaf f5_vtocl2gaf f7_vtocl2gaf p_nfel1 f4_vtocl2gaf a_sup_set_class f8_vtocl2gaf a_wcel f3_vtocl2gaf p_nfv f5_vtocl2gaf f7_vtocl2gaf a_wcel f4_vtocl2gaf a_sup_set_class f8_vtocl2gaf a_wcel f3_vtocl2gaf p_nfan e3_vtocl2gaf f5_vtocl2gaf f7_vtocl2gaf a_wcel f4_vtocl2gaf a_sup_set_class f8_vtocl2gaf a_wcel a_wa f1_vtocl2gaf f3_vtocl2gaf p_nfim e1_vtocl2gaf f4_vtocl2gaf f5_vtocl2gaf f7_vtocl2gaf p_nfel1 e2_vtocl2gaf f4_vtocl2gaf f6_vtocl2gaf f8_vtocl2gaf p_nfel1 f5_vtocl2gaf f7_vtocl2gaf a_wcel f6_vtocl2gaf f8_vtocl2gaf a_wcel f4_vtocl2gaf p_nfan e4_vtocl2gaf f5_vtocl2gaf f7_vtocl2gaf a_wcel f6_vtocl2gaf f8_vtocl2gaf a_wcel a_wa f2_vtocl2gaf f4_vtocl2gaf p_nfim f3_vtocl2gaf a_sup_set_class f5_vtocl2gaf f7_vtocl2gaf p_eleq1 f3_vtocl2gaf a_sup_set_class f5_vtocl2gaf a_wceq f3_vtocl2gaf a_sup_set_class f7_vtocl2gaf a_wcel f5_vtocl2gaf f7_vtocl2gaf a_wcel f4_vtocl2gaf a_sup_set_class f8_vtocl2gaf a_wcel p_anbi1d e5_vtocl2gaf f3_vtocl2gaf a_sup_set_class f5_vtocl2gaf a_wceq f3_vtocl2gaf a_sup_set_class f7_vtocl2gaf a_wcel f4_vtocl2gaf a_sup_set_class f8_vtocl2gaf a_wcel a_wa f5_vtocl2gaf f7_vtocl2gaf a_wcel f4_vtocl2gaf a_sup_set_class f8_vtocl2gaf a_wcel a_wa f0_vtocl2gaf f1_vtocl2gaf p_imbi12d f4_vtocl2gaf a_sup_set_class f6_vtocl2gaf f8_vtocl2gaf p_eleq1 f4_vtocl2gaf a_sup_set_class f6_vtocl2gaf a_wceq f4_vtocl2gaf a_sup_set_class f8_vtocl2gaf a_wcel f6_vtocl2gaf f8_vtocl2gaf a_wcel f5_vtocl2gaf f7_vtocl2gaf a_wcel p_anbi2d e6_vtocl2gaf f4_vtocl2gaf a_sup_set_class f6_vtocl2gaf a_wceq f5_vtocl2gaf f7_vtocl2gaf a_wcel f4_vtocl2gaf a_sup_set_class f8_vtocl2gaf a_wcel a_wa f5_vtocl2gaf f7_vtocl2gaf a_wcel f6_vtocl2gaf f8_vtocl2gaf a_wcel a_wa f1_vtocl2gaf f2_vtocl2gaf p_imbi12d e7_vtocl2gaf f3_vtocl2gaf a_sup_set_class f7_vtocl2gaf a_wcel f4_vtocl2gaf a_sup_set_class f8_vtocl2gaf a_wcel a_wa f0_vtocl2gaf a_wi f5_vtocl2gaf f7_vtocl2gaf a_wcel f4_vtocl2gaf a_sup_set_class f8_vtocl2gaf a_wcel a_wa f1_vtocl2gaf a_wi f5_vtocl2gaf f7_vtocl2gaf a_wcel f6_vtocl2gaf f8_vtocl2gaf a_wcel a_wa f2_vtocl2gaf a_wi f3_vtocl2gaf f4_vtocl2gaf f5_vtocl2gaf f6_vtocl2gaf f7_vtocl2gaf f8_vtocl2gaf p_vtocl2gf f5_vtocl2gaf f7_vtocl2gaf a_wcel f6_vtocl2gaf f8_vtocl2gaf a_wcel a_wa f2_vtocl2gaf p_pm2.43i $.
$}

$(Implicit substitution of 2 classes for 2 set variables.  (Contributed by
       NM, 20-Aug-1995.) $)

${
	$v ph ps ch x y A B C D  $.
	$d x y A  $.
	$d y B  $.
	$d x y C  $.
	$d x y D  $.
	$d x ps  $.
	$d y ch  $.
	f0_vtocl2ga $f wff ph $.
	f1_vtocl2ga $f wff ps $.
	f2_vtocl2ga $f wff ch $.
	f3_vtocl2ga $f set x $.
	f4_vtocl2ga $f set y $.
	f5_vtocl2ga $f class A $.
	f6_vtocl2ga $f class B $.
	f7_vtocl2ga $f class C $.
	f8_vtocl2ga $f class D $.
	e0_vtocl2ga $e |- ( x = A -> ( ph <-> ps ) ) $.
	e1_vtocl2ga $e |- ( y = B -> ( ps <-> ch ) ) $.
	e2_vtocl2ga $e |- ( ( x e. C /\ y e. D ) -> ph ) $.
	p_vtocl2ga $p |- ( ( A e. C /\ B e. D ) -> ch ) $= f3_vtocl2ga f5_vtocl2ga p_nfcv f4_vtocl2ga f5_vtocl2ga p_nfcv f4_vtocl2ga f6_vtocl2ga p_nfcv f1_vtocl2ga f3_vtocl2ga p_nfv f2_vtocl2ga f4_vtocl2ga p_nfv e0_vtocl2ga e1_vtocl2ga e2_vtocl2ga f0_vtocl2ga f1_vtocl2ga f2_vtocl2ga f3_vtocl2ga f4_vtocl2ga f5_vtocl2ga f6_vtocl2ga f7_vtocl2ga f8_vtocl2ga p_vtocl2gaf $.
$}

$(Implicit substitution of 3 classes for 3 set variables.  (Contributed by
       NM, 10-Aug-2013.)  (Revised by Mario Carneiro, 11-Oct-2016.) $)

${
	$v ph ps ch th x y z A B C R S T  $.
	$d A  $.
	$d B  $.
	$d C  $.
	$d x y z R  $.
	$d x y z S  $.
	$d x y z T  $.
	f0_vtocl3gaf $f wff ph $.
	f1_vtocl3gaf $f wff ps $.
	f2_vtocl3gaf $f wff ch $.
	f3_vtocl3gaf $f wff th $.
	f4_vtocl3gaf $f set x $.
	f5_vtocl3gaf $f set y $.
	f6_vtocl3gaf $f set z $.
	f7_vtocl3gaf $f class A $.
	f8_vtocl3gaf $f class B $.
	f9_vtocl3gaf $f class C $.
	f10_vtocl3gaf $f class R $.
	f11_vtocl3gaf $f class S $.
	f12_vtocl3gaf $f class T $.
	e0_vtocl3gaf $e |- F/_ x A $.
	e1_vtocl3gaf $e |- F/_ y A $.
	e2_vtocl3gaf $e |- F/_ z A $.
	e3_vtocl3gaf $e |- F/_ y B $.
	e4_vtocl3gaf $e |- F/_ z B $.
	e5_vtocl3gaf $e |- F/_ z C $.
	e6_vtocl3gaf $e |- F/ x ps $.
	e7_vtocl3gaf $e |- F/ y ch $.
	e8_vtocl3gaf $e |- F/ z th $.
	e9_vtocl3gaf $e |- ( x = A -> ( ph <-> ps ) ) $.
	e10_vtocl3gaf $e |- ( y = B -> ( ps <-> ch ) ) $.
	e11_vtocl3gaf $e |- ( z = C -> ( ch <-> th ) ) $.
	e12_vtocl3gaf $e |- ( ( x e. R /\ y e. S /\ z e. T ) -> ph ) $.
	p_vtocl3gaf $p |- ( ( A e. R /\ B e. S /\ C e. T ) -> th ) $= e0_vtocl3gaf e1_vtocl3gaf e2_vtocl3gaf e3_vtocl3gaf e4_vtocl3gaf e5_vtocl3gaf e0_vtocl3gaf f4_vtocl3gaf f7_vtocl3gaf f10_vtocl3gaf p_nfel1 f5_vtocl3gaf a_sup_set_class f11_vtocl3gaf a_wcel f4_vtocl3gaf p_nfv f6_vtocl3gaf a_sup_set_class f12_vtocl3gaf a_wcel f4_vtocl3gaf p_nfv f7_vtocl3gaf f10_vtocl3gaf a_wcel f5_vtocl3gaf a_sup_set_class f11_vtocl3gaf a_wcel f6_vtocl3gaf a_sup_set_class f12_vtocl3gaf a_wcel f4_vtocl3gaf p_nf3an e6_vtocl3gaf f7_vtocl3gaf f10_vtocl3gaf a_wcel f5_vtocl3gaf a_sup_set_class f11_vtocl3gaf a_wcel f6_vtocl3gaf a_sup_set_class f12_vtocl3gaf a_wcel a_w3a f1_vtocl3gaf f4_vtocl3gaf p_nfim e1_vtocl3gaf f5_vtocl3gaf f7_vtocl3gaf f10_vtocl3gaf p_nfel1 e3_vtocl3gaf f5_vtocl3gaf f8_vtocl3gaf f11_vtocl3gaf p_nfel1 f6_vtocl3gaf a_sup_set_class f12_vtocl3gaf a_wcel f5_vtocl3gaf p_nfv f7_vtocl3gaf f10_vtocl3gaf a_wcel f8_vtocl3gaf f11_vtocl3gaf a_wcel f6_vtocl3gaf a_sup_set_class f12_vtocl3gaf a_wcel f5_vtocl3gaf p_nf3an e7_vtocl3gaf f7_vtocl3gaf f10_vtocl3gaf a_wcel f8_vtocl3gaf f11_vtocl3gaf a_wcel f6_vtocl3gaf a_sup_set_class f12_vtocl3gaf a_wcel a_w3a f2_vtocl3gaf f5_vtocl3gaf p_nfim e2_vtocl3gaf f6_vtocl3gaf f7_vtocl3gaf f10_vtocl3gaf p_nfel1 e4_vtocl3gaf f6_vtocl3gaf f8_vtocl3gaf f11_vtocl3gaf p_nfel1 e5_vtocl3gaf f6_vtocl3gaf f9_vtocl3gaf f12_vtocl3gaf p_nfel1 f7_vtocl3gaf f10_vtocl3gaf a_wcel f8_vtocl3gaf f11_vtocl3gaf a_wcel f9_vtocl3gaf f12_vtocl3gaf a_wcel f6_vtocl3gaf p_nf3an e8_vtocl3gaf f7_vtocl3gaf f10_vtocl3gaf a_wcel f8_vtocl3gaf f11_vtocl3gaf a_wcel f9_vtocl3gaf f12_vtocl3gaf a_wcel a_w3a f3_vtocl3gaf f6_vtocl3gaf p_nfim f4_vtocl3gaf a_sup_set_class f7_vtocl3gaf f10_vtocl3gaf p_eleq1 f4_vtocl3gaf a_sup_set_class f7_vtocl3gaf a_wceq f4_vtocl3gaf a_sup_set_class f10_vtocl3gaf a_wcel f7_vtocl3gaf f10_vtocl3gaf a_wcel f5_vtocl3gaf a_sup_set_class f11_vtocl3gaf a_wcel f6_vtocl3gaf a_sup_set_class f12_vtocl3gaf a_wcel p_3anbi1d e9_vtocl3gaf f4_vtocl3gaf a_sup_set_class f7_vtocl3gaf a_wceq f4_vtocl3gaf a_sup_set_class f10_vtocl3gaf a_wcel f5_vtocl3gaf a_sup_set_class f11_vtocl3gaf a_wcel f6_vtocl3gaf a_sup_set_class f12_vtocl3gaf a_wcel a_w3a f7_vtocl3gaf f10_vtocl3gaf a_wcel f5_vtocl3gaf a_sup_set_class f11_vtocl3gaf a_wcel f6_vtocl3gaf a_sup_set_class f12_vtocl3gaf a_wcel a_w3a f0_vtocl3gaf f1_vtocl3gaf p_imbi12d f5_vtocl3gaf a_sup_set_class f8_vtocl3gaf f11_vtocl3gaf p_eleq1 f5_vtocl3gaf a_sup_set_class f8_vtocl3gaf a_wceq f5_vtocl3gaf a_sup_set_class f11_vtocl3gaf a_wcel f8_vtocl3gaf f11_vtocl3gaf a_wcel f7_vtocl3gaf f10_vtocl3gaf a_wcel f6_vtocl3gaf a_sup_set_class f12_vtocl3gaf a_wcel p_3anbi2d e10_vtocl3gaf f5_vtocl3gaf a_sup_set_class f8_vtocl3gaf a_wceq f7_vtocl3gaf f10_vtocl3gaf a_wcel f5_vtocl3gaf a_sup_set_class f11_vtocl3gaf a_wcel f6_vtocl3gaf a_sup_set_class f12_vtocl3gaf a_wcel a_w3a f7_vtocl3gaf f10_vtocl3gaf a_wcel f8_vtocl3gaf f11_vtocl3gaf a_wcel f6_vtocl3gaf a_sup_set_class f12_vtocl3gaf a_wcel a_w3a f1_vtocl3gaf f2_vtocl3gaf p_imbi12d f6_vtocl3gaf a_sup_set_class f9_vtocl3gaf f12_vtocl3gaf p_eleq1 f6_vtocl3gaf a_sup_set_class f9_vtocl3gaf a_wceq f6_vtocl3gaf a_sup_set_class f12_vtocl3gaf a_wcel f9_vtocl3gaf f12_vtocl3gaf a_wcel f7_vtocl3gaf f10_vtocl3gaf a_wcel f8_vtocl3gaf f11_vtocl3gaf a_wcel p_3anbi3d e11_vtocl3gaf f6_vtocl3gaf a_sup_set_class f9_vtocl3gaf a_wceq f7_vtocl3gaf f10_vtocl3gaf a_wcel f8_vtocl3gaf f11_vtocl3gaf a_wcel f6_vtocl3gaf a_sup_set_class f12_vtocl3gaf a_wcel a_w3a f7_vtocl3gaf f10_vtocl3gaf a_wcel f8_vtocl3gaf f11_vtocl3gaf a_wcel f9_vtocl3gaf f12_vtocl3gaf a_wcel a_w3a f2_vtocl3gaf f3_vtocl3gaf p_imbi12d e12_vtocl3gaf f4_vtocl3gaf a_sup_set_class f10_vtocl3gaf a_wcel f5_vtocl3gaf a_sup_set_class f11_vtocl3gaf a_wcel f6_vtocl3gaf a_sup_set_class f12_vtocl3gaf a_wcel a_w3a f0_vtocl3gaf a_wi f7_vtocl3gaf f10_vtocl3gaf a_wcel f5_vtocl3gaf a_sup_set_class f11_vtocl3gaf a_wcel f6_vtocl3gaf a_sup_set_class f12_vtocl3gaf a_wcel a_w3a f1_vtocl3gaf a_wi f7_vtocl3gaf f10_vtocl3gaf a_wcel f8_vtocl3gaf f11_vtocl3gaf a_wcel f6_vtocl3gaf a_sup_set_class f12_vtocl3gaf a_wcel a_w3a f2_vtocl3gaf a_wi f7_vtocl3gaf f10_vtocl3gaf a_wcel f8_vtocl3gaf f11_vtocl3gaf a_wcel f9_vtocl3gaf f12_vtocl3gaf a_wcel a_w3a f3_vtocl3gaf a_wi f4_vtocl3gaf f5_vtocl3gaf f6_vtocl3gaf f7_vtocl3gaf f8_vtocl3gaf f9_vtocl3gaf f10_vtocl3gaf f11_vtocl3gaf f12_vtocl3gaf p_vtocl3gf f7_vtocl3gaf f10_vtocl3gaf a_wcel f8_vtocl3gaf f11_vtocl3gaf a_wcel f9_vtocl3gaf f12_vtocl3gaf a_wcel a_w3a f3_vtocl3gaf p_pm2.43i $.
$}

$(Implicit substitution of 3 classes for 3 set variables.  (Contributed by
       NM, 20-Aug-1995.) $)

${
	$v ph ps ch th x y z A B C D R S  $.
	$d x y z A  $.
	$d y z B  $.
	$d z C  $.
	$d x y z D  $.
	$d x y z R  $.
	$d x y z S  $.
	$d x ps  $.
	$d y ch  $.
	$d z th  $.
	f0_vtocl3ga $f wff ph $.
	f1_vtocl3ga $f wff ps $.
	f2_vtocl3ga $f wff ch $.
	f3_vtocl3ga $f wff th $.
	f4_vtocl3ga $f set x $.
	f5_vtocl3ga $f set y $.
	f6_vtocl3ga $f set z $.
	f7_vtocl3ga $f class A $.
	f8_vtocl3ga $f class B $.
	f9_vtocl3ga $f class C $.
	f10_vtocl3ga $f class D $.
	f11_vtocl3ga $f class R $.
	f12_vtocl3ga $f class S $.
	e0_vtocl3ga $e |- ( x = A -> ( ph <-> ps ) ) $.
	e1_vtocl3ga $e |- ( y = B -> ( ps <-> ch ) ) $.
	e2_vtocl3ga $e |- ( z = C -> ( ch <-> th ) ) $.
	e3_vtocl3ga $e |- ( ( x e. D /\ y e. R /\ z e. S ) -> ph ) $.
	p_vtocl3ga $p |- ( ( A e. D /\ B e. R /\ C e. S ) -> th ) $= f4_vtocl3ga f7_vtocl3ga p_nfcv f5_vtocl3ga f7_vtocl3ga p_nfcv f6_vtocl3ga f7_vtocl3ga p_nfcv f5_vtocl3ga f8_vtocl3ga p_nfcv f6_vtocl3ga f8_vtocl3ga p_nfcv f6_vtocl3ga f9_vtocl3ga p_nfcv f1_vtocl3ga f4_vtocl3ga p_nfv f2_vtocl3ga f5_vtocl3ga p_nfv f3_vtocl3ga f6_vtocl3ga p_nfv e0_vtocl3ga e1_vtocl3ga e2_vtocl3ga e3_vtocl3ga f0_vtocl3ga f1_vtocl3ga f2_vtocl3ga f3_vtocl3ga f4_vtocl3ga f5_vtocl3ga f6_vtocl3ga f7_vtocl3ga f8_vtocl3ga f9_vtocl3ga f10_vtocl3ga f11_vtocl3ga f12_vtocl3ga p_vtocl3gaf $.
$}

$(Implicit substitution of a class for a set variable.  (Contributed by
       NM, 10-Jan-2004.) $)

${
	$v ph x A V  $.
	$d x A  $.
	$d x ph  $.
	f0_vtocleg $f wff ph $.
	f1_vtocleg $f set x $.
	f2_vtocleg $f class A $.
	f3_vtocleg $f class V $.
	e0_vtocleg $e |- ( x = A -> ph ) $.
	p_vtocleg $p |- ( A e. V -> ph ) $= f1_vtocleg f2_vtocleg f3_vtocleg p_elisset e0_vtocleg f1_vtocleg a_sup_set_class f2_vtocleg a_wceq f0_vtocleg f1_vtocleg p_exlimiv f2_vtocleg f3_vtocleg a_wcel f1_vtocleg a_sup_set_class f2_vtocleg a_wceq f1_vtocleg a_wex f0_vtocleg p_syl $.
$}

$(Implicit substitution of a class for a set variable.  (Closed theorem
       version of ~ vtoclef .)  (Contributed by NM, 7-Nov-2005.)  (Revised by
       Mario Carneiro, 11-Oct-2016.) $)

${
	$v ph x A B  $.
	$d x A  $.
	f0_vtoclegft $f wff ph $.
	f1_vtoclegft $f set x $.
	f2_vtoclegft $f class A $.
	f3_vtoclegft $f class B $.
	p_vtoclegft $p |- ( ( A e. B /\ F/ x ph /\ A. x ( x = A -> ph ) ) -> ph ) $= f1_vtoclegft f2_vtoclegft f3_vtoclegft p_elisset f1_vtoclegft a_sup_set_class f2_vtoclegft a_wceq f0_vtoclegft f1_vtoclegft p_exim f2_vtoclegft f3_vtoclegft a_wcel f1_vtoclegft a_sup_set_class f2_vtoclegft a_wceq f1_vtoclegft a_wex f1_vtoclegft a_sup_set_class f2_vtoclegft a_wceq f0_vtoclegft a_wi f1_vtoclegft a_wal f0_vtoclegft f1_vtoclegft a_wex p_mpan9 f2_vtoclegft f3_vtoclegft a_wcel f1_vtoclegft a_sup_set_class f2_vtoclegft a_wceq f0_vtoclegft a_wi f1_vtoclegft a_wal f0_vtoclegft f1_vtoclegft a_wex f0_vtoclegft f1_vtoclegft a_wnf p_3adant2 f0_vtoclegft f1_vtoclegft p_19.9t f0_vtoclegft f1_vtoclegft a_wnf f2_vtoclegft f3_vtoclegft a_wcel f0_vtoclegft f1_vtoclegft a_wex f0_vtoclegft a_wb f1_vtoclegft a_sup_set_class f2_vtoclegft a_wceq f0_vtoclegft a_wi f1_vtoclegft a_wal p_3ad2ant2 f2_vtoclegft f3_vtoclegft a_wcel f0_vtoclegft f1_vtoclegft a_wnf f1_vtoclegft a_sup_set_class f2_vtoclegft a_wceq f0_vtoclegft a_wi f1_vtoclegft a_wal a_w3a f0_vtoclegft f1_vtoclegft a_wex f0_vtoclegft p_mpbid $.
$}

$(Implicit substitution of a class for a set variable.  (Contributed by
       NM, 18-Aug-1993.) $)

${
	$v ph x A  $.
	$d x A  $.
	f0_vtoclef $f wff ph $.
	f1_vtoclef $f set x $.
	f2_vtoclef $f class A $.
	e0_vtoclef $e |- F/ x ph $.
	e1_vtoclef $e |- A e. _V $.
	e2_vtoclef $e |- ( x = A -> ph ) $.
	p_vtoclef $p |- ph $= e1_vtoclef f1_vtoclef f2_vtoclef p_isseti e0_vtoclef e2_vtoclef f1_vtoclef a_sup_set_class f2_vtoclef a_wceq f0_vtoclef f1_vtoclef p_exlimi f1_vtoclef a_sup_set_class f2_vtoclef a_wceq f1_vtoclef a_wex f0_vtoclef a_ax-mp $.
$}

$(Implicit substitution of a class for a set variable.  (Contributed by
       NM, 9-Sep-1993.) $)

${
	$v ph x A  $.
	$d x A  $.
	$d x ph  $.
	f0_vtocle $f wff ph $.
	f1_vtocle $f set x $.
	f2_vtocle $f class A $.
	e0_vtocle $e |- A e. _V $.
	e1_vtocle $e |- ( x = A -> ph ) $.
	p_vtocle $p |- ph $= e0_vtocle e1_vtocle f0_vtocle f1_vtocle f2_vtocle a_cvv p_vtocleg f2_vtocle a_cvv a_wcel f0_vtocle a_ax-mp $.
$}

$(Implicit substitution of a class for a set variable.  (Contributed by
       NM, 21-Nov-1994.) $)

${
	$v ph ps x A B  $.
	$d x A  $.
	$d x B  $.
	$d x ps  $.
	f0_vtoclri $f wff ph $.
	f1_vtoclri $f wff ps $.
	f2_vtoclri $f set x $.
	f3_vtoclri $f class A $.
	f4_vtoclri $f class B $.
	e0_vtoclri $e |- ( x = A -> ( ph <-> ps ) ) $.
	e1_vtoclri $e |- A. x e. B ph $.
	p_vtoclri $p |- ( A e. B -> ps ) $= e0_vtoclri e1_vtoclri f0_vtoclri f2_vtoclri f4_vtoclri p_rspec f0_vtoclri f1_vtoclri f2_vtoclri f3_vtoclri f4_vtoclri p_vtoclga $.
$}

$(A closed version of ~ spcimgf .  (Contributed by Mario Carneiro,
       4-Jan-2017.) $)

${
	$v ph ps x A B  $.
	$d x  $.
	$d A  $.
	f0_spcimgft $f wff ph $.
	f1_spcimgft $f wff ps $.
	f2_spcimgft $f set x $.
	f3_spcimgft $f class A $.
	f4_spcimgft $f class B $.
	e0_spcimgft $e |- F/ x ps $.
	e1_spcimgft $e |- F/_ x A $.
	p_spcimgft $p |- ( A. x ( x = A -> ( ph -> ps ) ) -> ( A e. B -> ( A. x ph -> ps ) ) ) $= f3_spcimgft f4_spcimgft p_elex e1_spcimgft f2_spcimgft f3_spcimgft p_issetf f2_spcimgft a_sup_set_class f3_spcimgft a_wceq f0_spcimgft f1_spcimgft a_wi f2_spcimgft p_exim f3_spcimgft a_cvv a_wcel f2_spcimgft a_sup_set_class f3_spcimgft a_wceq f2_spcimgft a_wex f2_spcimgft a_sup_set_class f3_spcimgft a_wceq f0_spcimgft f1_spcimgft a_wi a_wi f2_spcimgft a_wal f0_spcimgft f1_spcimgft a_wi f2_spcimgft a_wex p_syl5bi e0_spcimgft f0_spcimgft f1_spcimgft f2_spcimgft p_19.36 f2_spcimgft a_sup_set_class f3_spcimgft a_wceq f0_spcimgft f1_spcimgft a_wi a_wi f2_spcimgft a_wal f3_spcimgft a_cvv a_wcel f0_spcimgft f1_spcimgft a_wi f2_spcimgft a_wex f0_spcimgft f2_spcimgft a_wal f1_spcimgft a_wi p_syl6ib f3_spcimgft f4_spcimgft a_wcel f3_spcimgft a_cvv a_wcel f2_spcimgft a_sup_set_class f3_spcimgft a_wceq f0_spcimgft f1_spcimgft a_wi a_wi f2_spcimgft a_wal f0_spcimgft f2_spcimgft a_wal f1_spcimgft a_wi p_syl5 $.
$}

$(A closed version of ~ spcgf .  (Contributed by Andrew Salmon,
       6-Jun-2011.)  (Revised by Mario Carneiro, 4-Jan-2017.) $)

${
	$v ph ps x A B  $.
	$d x  $.
	$d A  $.
	f0_spcgft $f wff ph $.
	f1_spcgft $f wff ps $.
	f2_spcgft $f set x $.
	f3_spcgft $f class A $.
	f4_spcgft $f class B $.
	e0_spcgft $e |- F/ x ps $.
	e1_spcgft $e |- F/_ x A $.
	p_spcgft $p |- ( A. x ( x = A -> ( ph <-> ps ) ) -> ( A e. B -> ( A. x ph -> ps ) ) ) $= f0_spcgft f1_spcgft p_bi1 f0_spcgft f1_spcgft a_wb f0_spcgft f1_spcgft a_wi f2_spcgft a_sup_set_class f3_spcgft a_wceq p_imim2i f2_spcgft a_sup_set_class f3_spcgft a_wceq f0_spcgft f1_spcgft a_wb a_wi f2_spcgft a_sup_set_class f3_spcgft a_wceq f0_spcgft f1_spcgft a_wi a_wi f2_spcgft p_alimi e0_spcgft e1_spcgft f0_spcgft f1_spcgft f2_spcgft f3_spcgft f4_spcgft p_spcimgft f2_spcgft a_sup_set_class f3_spcgft a_wceq f0_spcgft f1_spcgft a_wb a_wi f2_spcgft a_wal f2_spcgft a_sup_set_class f3_spcgft a_wceq f0_spcgft f1_spcgft a_wi a_wi f2_spcgft a_wal f3_spcgft f4_spcgft a_wcel f0_spcgft f2_spcgft a_wal f1_spcgft a_wi a_wi p_syl $.
$}

$(Rule of specialization, using implicit substitution.  Compare Theorem
         7.3 of [Quine] p. 44.  (Contributed by Mario Carneiro, 4-Jan-2017.) $)

${
	$v ph ps x A V  $.
	f0_spcimgf $f wff ph $.
	f1_spcimgf $f wff ps $.
	f2_spcimgf $f set x $.
	f3_spcimgf $f class A $.
	f4_spcimgf $f class V $.
	e0_spcimgf $e |- F/_ x A $.
	e1_spcimgf $e |- F/ x ps $.
	e2_spcimgf $e |- ( x = A -> ( ph -> ps ) ) $.
	p_spcimgf $p |- ( A e. V -> ( A. x ph -> ps ) ) $= e1_spcimgf e0_spcimgf f0_spcimgf f1_spcimgf f2_spcimgf f3_spcimgf f4_spcimgf p_spcimgft e2_spcimgf f2_spcimgf a_sup_set_class f3_spcimgf a_wceq f0_spcimgf f1_spcimgf a_wi a_wi f3_spcimgf f4_spcimgf a_wcel f0_spcimgf f2_spcimgf a_wal f1_spcimgf a_wi a_wi f2_spcimgf p_mpg $.
$}

$(Existential specialization, using implicit substitution.  (Contributed
       by Mario Carneiro, 4-Jan-2017.) $)

${
	$v ph ps x A V  $.
	f0_spcimegf $f wff ph $.
	f1_spcimegf $f wff ps $.
	f2_spcimegf $f set x $.
	f3_spcimegf $f class A $.
	f4_spcimegf $f class V $.
	e0_spcimegf $e |- F/_ x A $.
	e1_spcimegf $e |- F/ x ps $.
	e2_spcimegf $e |- ( x = A -> ( ps -> ph ) ) $.
	p_spcimegf $p |- ( A e. V -> ( ps -> E. x ph ) ) $= e0_spcimegf e1_spcimegf f1_spcimegf f2_spcimegf p_nfn e2_spcimegf f2_spcimegf a_sup_set_class f3_spcimegf a_wceq f1_spcimegf f0_spcimegf p_con3d f0_spcimegf a_wn f1_spcimegf a_wn f2_spcimegf f3_spcimegf f4_spcimegf p_spcimgf f3_spcimegf f4_spcimegf a_wcel f0_spcimegf a_wn f2_spcimegf a_wal f1_spcimegf p_con2d f0_spcimegf f2_spcimegf a_df-ex f3_spcimegf f4_spcimegf a_wcel f1_spcimegf f0_spcimegf a_wn f2_spcimegf a_wal a_wn f0_spcimegf f2_spcimegf a_wex p_syl6ibr $.
$}

$(Rule of specialization, using implicit substitution.  Compare Theorem
       7.3 of [Quine] p. 44.  (Contributed by NM, 2-Feb-1997.)  (Revised by
       Andrew Salmon, 12-Aug-2011.) $)

${
	$v ph ps x A V  $.
	$d A  $.
	$d x  $.
	f0_spcgf $f wff ph $.
	f1_spcgf $f wff ps $.
	f2_spcgf $f set x $.
	f3_spcgf $f class A $.
	f4_spcgf $f class V $.
	e0_spcgf $e |- F/_ x A $.
	e1_spcgf $e |- F/ x ps $.
	e2_spcgf $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_spcgf $p |- ( A e. V -> ( A. x ph -> ps ) ) $= e1_spcgf e0_spcgf f0_spcgf f1_spcgf f2_spcgf f3_spcgf f4_spcgf p_spcgft e2_spcgf f2_spcgf a_sup_set_class f3_spcgf a_wceq f0_spcgf f1_spcgf a_wb a_wi f3_spcgf f4_spcgf a_wcel f0_spcgf f2_spcgf a_wal f1_spcgf a_wi a_wi f2_spcgf p_mpg $.
$}

$(Existential specialization, using implicit substitution.  (Contributed
       by NM, 2-Feb-1997.) $)

${
	$v ph ps x A V  $.
	$d A  $.
	$d x  $.
	f0_spcegf $f wff ph $.
	f1_spcegf $f wff ps $.
	f2_spcegf $f set x $.
	f3_spcegf $f class A $.
	f4_spcegf $f class V $.
	e0_spcegf $e |- F/_ x A $.
	e1_spcegf $e |- F/ x ps $.
	e2_spcegf $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_spcegf $p |- ( A e. V -> ( ps -> E. x ph ) ) $= e0_spcegf e1_spcegf f1_spcegf f2_spcegf p_nfn e2_spcegf f2_spcegf a_sup_set_class f3_spcegf a_wceq f0_spcegf f1_spcegf p_notbid f0_spcegf a_wn f1_spcegf a_wn f2_spcegf f3_spcegf f4_spcegf p_spcgf f3_spcegf f4_spcegf a_wcel f0_spcegf a_wn f2_spcegf a_wal f1_spcegf p_con2d f0_spcegf f2_spcegf a_df-ex f3_spcegf f4_spcegf a_wcel f1_spcegf f0_spcegf a_wn f2_spcegf a_wal a_wn f0_spcegf f2_spcegf a_wex p_syl6ibr $.
$}

$(Restricted specialization, using implicit substitution.  (Contributed
         by Mario Carneiro, 4-Jan-2017.) $)

${
	$v ph ps ch x A B  $.
	$d x A  $.
	$d x ph  $.
	$d x ch  $.
	f0_spcimdv $f wff ph $.
	f1_spcimdv $f wff ps $.
	f2_spcimdv $f wff ch $.
	f3_spcimdv $f set x $.
	f4_spcimdv $f class A $.
	f5_spcimdv $f class B $.
	e0_spcimdv $e |- ( ph -> A e. B ) $.
	e1_spcimdv $e |- ( ( ph /\ x = A ) -> ( ps -> ch ) ) $.
	p_spcimdv $p |- ( ph -> ( A. x ps -> ch ) ) $= e1_spcimdv f0_spcimdv f3_spcimdv a_sup_set_class f4_spcimdv a_wceq f1_spcimdv f2_spcimdv a_wi p_ex f0_spcimdv f3_spcimdv a_sup_set_class f4_spcimdv a_wceq f1_spcimdv f2_spcimdv a_wi a_wi f3_spcimdv p_alrimiv e0_spcimdv f2_spcimdv f3_spcimdv p_nfv f3_spcimdv f4_spcimdv p_nfcv f1_spcimdv f2_spcimdv f3_spcimdv f4_spcimdv f5_spcimdv p_spcimgft f0_spcimdv f3_spcimdv a_sup_set_class f4_spcimdv a_wceq f1_spcimdv f2_spcimdv a_wi a_wi f3_spcimdv a_wal f4_spcimdv f5_spcimdv a_wcel f1_spcimdv f3_spcimdv a_wal f2_spcimdv a_wi p_sylc $.
$}

$(Rule of specialization, using implicit substitution.  Analogous to
         ~ rspcdv .  (Contributed by David Moews, 1-May-2017.) $)

${
	$v ph ps ch x A B  $.
	$d x A  $.
	$d x ph  $.
	$d x ch  $.
	f0_spcdv $f wff ph $.
	f1_spcdv $f wff ps $.
	f2_spcdv $f wff ch $.
	f3_spcdv $f set x $.
	f4_spcdv $f class A $.
	f5_spcdv $f class B $.
	e0_spcdv $e |- ( ph -> A e. B ) $.
	e1_spcdv $e |- ( ( ph /\ x = A ) -> ( ps <-> ch ) ) $.
	p_spcdv $p |- ( ph -> ( A. x ps -> ch ) ) $= e0_spcdv e1_spcdv f0_spcdv f3_spcdv a_sup_set_class f4_spcdv a_wceq a_wa f1_spcdv f2_spcdv p_biimpd f0_spcdv f1_spcdv f2_spcdv f3_spcdv f4_spcdv f5_spcdv p_spcimdv $.
$}

$(Restricted existential specialization, using implicit substitution.
       (Contributed by Mario Carneiro, 4-Jan-2017.) $)

${
	$v ph ps ch x A B  $.
	$d x A  $.
	$d x ph  $.
	$d x ch  $.
	f0_spcimedv $f wff ph $.
	f1_spcimedv $f wff ps $.
	f2_spcimedv $f wff ch $.
	f3_spcimedv $f set x $.
	f4_spcimedv $f class A $.
	f5_spcimedv $f class B $.
	e0_spcimedv $e |- ( ph -> A e. B ) $.
	e1_spcimedv $e |- ( ( ph /\ x = A ) -> ( ch -> ps ) ) $.
	p_spcimedv $p |- ( ph -> ( ch -> E. x ps ) ) $= e0_spcimedv e1_spcimedv f0_spcimedv f3_spcimedv a_sup_set_class f4_spcimedv a_wceq a_wa f2_spcimedv f1_spcimedv p_con3d f0_spcimedv f1_spcimedv a_wn f2_spcimedv a_wn f3_spcimedv f4_spcimedv f5_spcimedv p_spcimdv f0_spcimedv f1_spcimedv a_wn f3_spcimedv a_wal f2_spcimedv p_con2d f1_spcimedv f3_spcimedv a_df-ex f0_spcimedv f2_spcimedv f1_spcimedv a_wn f3_spcimedv a_wal a_wn f1_spcimedv f3_spcimedv a_wex p_syl6ibr $.
$}

$(Rule of specialization, using implicit substitution.  Compare Theorem
       7.3 of [Quine] p. 44.  (Contributed by NM, 22-Jun-1994.) $)

${
	$v ph ps x A V  $.
	$d x ps  $.
	$d x A  $.
	f0_spcgv $f wff ph $.
	f1_spcgv $f wff ps $.
	f2_spcgv $f set x $.
	f3_spcgv $f class A $.
	f4_spcgv $f class V $.
	e0_spcgv $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_spcgv $p |- ( A e. V -> ( A. x ph -> ps ) ) $= f2_spcgv f3_spcgv p_nfcv f1_spcgv f2_spcgv p_nfv e0_spcgv f0_spcgv f1_spcgv f2_spcgv f3_spcgv f4_spcgv p_spcgf $.
$}

$(Existential specialization, using implicit substitution.  (Contributed
       by NM, 14-Aug-1994.) $)

${
	$v ph ps x A V  $.
	$d x ps  $.
	$d x A  $.
	f0_spcegv $f wff ph $.
	f1_spcegv $f wff ps $.
	f2_spcegv $f set x $.
	f3_spcegv $f class A $.
	f4_spcegv $f class V $.
	e0_spcegv $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_spcegv $p |- ( A e. V -> ( ps -> E. x ph ) ) $= f2_spcegv f3_spcegv p_nfcv f1_spcegv f2_spcegv p_nfv e0_spcegv f0_spcegv f1_spcegv f2_spcegv f3_spcegv f4_spcegv p_spcegf $.
$}

$(Existential specialization with 2 quantifiers, using implicit
       substitution.  (Contributed by NM, 3-Aug-1995.) $)

${
	$v ph ps x y A B V W  $.
	$d x y A  $.
	$d x y B  $.
	$d x y ps  $.
	f0_spc2egv $f wff ph $.
	f1_spc2egv $f wff ps $.
	f2_spc2egv $f set x $.
	f3_spc2egv $f set y $.
	f4_spc2egv $f class A $.
	f5_spc2egv $f class B $.
	f6_spc2egv $f class V $.
	f7_spc2egv $f class W $.
	e0_spc2egv $e |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) ) $.
	p_spc2egv $p |- ( ( A e. V /\ B e. W ) -> ( ps -> E. x E. y ph ) ) $= f2_spc2egv f4_spc2egv f6_spc2egv p_elisset f3_spc2egv f5_spc2egv f7_spc2egv p_elisset f4_spc2egv f6_spc2egv a_wcel f2_spc2egv a_sup_set_class f4_spc2egv a_wceq f2_spc2egv a_wex f5_spc2egv f7_spc2egv a_wcel f3_spc2egv a_sup_set_class f5_spc2egv a_wceq f3_spc2egv a_wex p_anim12i f2_spc2egv a_sup_set_class f4_spc2egv a_wceq f3_spc2egv a_sup_set_class f5_spc2egv a_wceq f2_spc2egv f3_spc2egv p_eeanv f4_spc2egv f6_spc2egv a_wcel f5_spc2egv f7_spc2egv a_wcel a_wa f2_spc2egv a_sup_set_class f4_spc2egv a_wceq f2_spc2egv a_wex f3_spc2egv a_sup_set_class f5_spc2egv a_wceq f3_spc2egv a_wex a_wa f2_spc2egv a_sup_set_class f4_spc2egv a_wceq f3_spc2egv a_sup_set_class f5_spc2egv a_wceq a_wa f3_spc2egv a_wex f2_spc2egv a_wex p_sylibr e0_spc2egv f2_spc2egv a_sup_set_class f4_spc2egv a_wceq f3_spc2egv a_sup_set_class f5_spc2egv a_wceq a_wa f0_spc2egv f1_spc2egv p_biimprcd f1_spc2egv f2_spc2egv a_sup_set_class f4_spc2egv a_wceq f3_spc2egv a_sup_set_class f5_spc2egv a_wceq a_wa f0_spc2egv f2_spc2egv f3_spc2egv p_2eximdv f4_spc2egv f6_spc2egv a_wcel f5_spc2egv f7_spc2egv a_wcel a_wa f2_spc2egv a_sup_set_class f4_spc2egv a_wceq f3_spc2egv a_sup_set_class f5_spc2egv a_wceq a_wa f3_spc2egv a_wex f2_spc2egv a_wex f1_spc2egv f0_spc2egv f3_spc2egv a_wex f2_spc2egv a_wex p_syl5com $.
$}

$(Specialization with 2 quantifiers, using implicit substitution.
       (Contributed by NM, 27-Apr-2004.) $)

${
	$v ph ps x y A B V W  $.
	$d x y A  $.
	$d x y B  $.
	$d x y ps  $.
	f0_spc2gv $f wff ph $.
	f1_spc2gv $f wff ps $.
	f2_spc2gv $f set x $.
	f3_spc2gv $f set y $.
	f4_spc2gv $f class A $.
	f5_spc2gv $f class B $.
	f6_spc2gv $f class V $.
	f7_spc2gv $f class W $.
	e0_spc2gv $e |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) ) $.
	p_spc2gv $p |- ( ( A e. V /\ B e. W ) -> ( A. x A. y ph -> ps ) ) $= e0_spc2gv f2_spc2gv a_sup_set_class f4_spc2gv a_wceq f3_spc2gv a_sup_set_class f5_spc2gv a_wceq a_wa f0_spc2gv f1_spc2gv p_notbid f0_spc2gv a_wn f1_spc2gv a_wn f2_spc2gv f3_spc2gv f4_spc2gv f5_spc2gv f6_spc2gv f7_spc2gv p_spc2egv f0_spc2gv f2_spc2gv f3_spc2gv p_2nalexn f4_spc2gv f6_spc2gv a_wcel f5_spc2gv f7_spc2gv a_wcel a_wa f1_spc2gv a_wn f0_spc2gv a_wn f3_spc2gv a_wex f2_spc2gv a_wex f0_spc2gv f3_spc2gv a_wal f2_spc2gv a_wal a_wn p_syl6ibr f4_spc2gv f6_spc2gv a_wcel f5_spc2gv f7_spc2gv a_wcel a_wa f1_spc2gv f0_spc2gv f3_spc2gv a_wal f2_spc2gv a_wal p_con4d $.
$}

$(Existential specialization with 3 quantifiers, using implicit
       substitution.  (Contributed by NM, 12-May-2008.) $)

${
	$v ph ps x y z A B C V W X  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x y z ps  $.
	f0_spc3egv $f wff ph $.
	f1_spc3egv $f wff ps $.
	f2_spc3egv $f set x $.
	f3_spc3egv $f set y $.
	f4_spc3egv $f set z $.
	f5_spc3egv $f class A $.
	f6_spc3egv $f class B $.
	f7_spc3egv $f class C $.
	f8_spc3egv $f class V $.
	f9_spc3egv $f class W $.
	f10_spc3egv $f class X $.
	e0_spc3egv $e |- ( ( x = A /\ y = B /\ z = C ) -> ( ph <-> ps ) ) $.
	p_spc3egv $p |- ( ( A e. V /\ B e. W /\ C e. X ) -> ( ps -> E. x E. y E. z ph ) ) $= f2_spc3egv f5_spc3egv f8_spc3egv p_elisset f3_spc3egv f6_spc3egv f9_spc3egv p_elisset f4_spc3egv f7_spc3egv f10_spc3egv p_elisset f5_spc3egv f8_spc3egv a_wcel f2_spc3egv a_sup_set_class f5_spc3egv a_wceq f2_spc3egv a_wex f6_spc3egv f9_spc3egv a_wcel f3_spc3egv a_sup_set_class f6_spc3egv a_wceq f3_spc3egv a_wex f7_spc3egv f10_spc3egv a_wcel f4_spc3egv a_sup_set_class f7_spc3egv a_wceq f4_spc3egv a_wex p_3anim123i f2_spc3egv a_sup_set_class f5_spc3egv a_wceq f3_spc3egv a_sup_set_class f6_spc3egv a_wceq f4_spc3egv a_sup_set_class f7_spc3egv a_wceq f2_spc3egv f3_spc3egv f4_spc3egv p_eeeanv f5_spc3egv f8_spc3egv a_wcel f6_spc3egv f9_spc3egv a_wcel f7_spc3egv f10_spc3egv a_wcel a_w3a f2_spc3egv a_sup_set_class f5_spc3egv a_wceq f2_spc3egv a_wex f3_spc3egv a_sup_set_class f6_spc3egv a_wceq f3_spc3egv a_wex f4_spc3egv a_sup_set_class f7_spc3egv a_wceq f4_spc3egv a_wex a_w3a f2_spc3egv a_sup_set_class f5_spc3egv a_wceq f3_spc3egv a_sup_set_class f6_spc3egv a_wceq f4_spc3egv a_sup_set_class f7_spc3egv a_wceq a_w3a f4_spc3egv a_wex f3_spc3egv a_wex f2_spc3egv a_wex p_sylibr e0_spc3egv f2_spc3egv a_sup_set_class f5_spc3egv a_wceq f3_spc3egv a_sup_set_class f6_spc3egv a_wceq f4_spc3egv a_sup_set_class f7_spc3egv a_wceq a_w3a f0_spc3egv f1_spc3egv p_biimprcd f1_spc3egv f2_spc3egv a_sup_set_class f5_spc3egv a_wceq f3_spc3egv a_sup_set_class f6_spc3egv a_wceq f4_spc3egv a_sup_set_class f7_spc3egv a_wceq a_w3a f0_spc3egv f4_spc3egv p_eximdv f1_spc3egv f2_spc3egv a_sup_set_class f5_spc3egv a_wceq f3_spc3egv a_sup_set_class f6_spc3egv a_wceq f4_spc3egv a_sup_set_class f7_spc3egv a_wceq a_w3a f4_spc3egv a_wex f0_spc3egv f4_spc3egv a_wex f2_spc3egv f3_spc3egv p_2eximdv f5_spc3egv f8_spc3egv a_wcel f6_spc3egv f9_spc3egv a_wcel f7_spc3egv f10_spc3egv a_wcel a_w3a f2_spc3egv a_sup_set_class f5_spc3egv a_wceq f3_spc3egv a_sup_set_class f6_spc3egv a_wceq f4_spc3egv a_sup_set_class f7_spc3egv a_wceq a_w3a f4_spc3egv a_wex f3_spc3egv a_wex f2_spc3egv a_wex f1_spc3egv f0_spc3egv f4_spc3egv a_wex f3_spc3egv a_wex f2_spc3egv a_wex p_syl5com $.
$}

$(Specialization with 3 quantifiers, using implicit substitution.
       (Contributed by NM, 12-May-2008.) $)

${
	$v ph ps x y z A B C V W X  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x y z ps  $.
	f0_spc3gv $f wff ph $.
	f1_spc3gv $f wff ps $.
	f2_spc3gv $f set x $.
	f3_spc3gv $f set y $.
	f4_spc3gv $f set z $.
	f5_spc3gv $f class A $.
	f6_spc3gv $f class B $.
	f7_spc3gv $f class C $.
	f8_spc3gv $f class V $.
	f9_spc3gv $f class W $.
	f10_spc3gv $f class X $.
	e0_spc3gv $e |- ( ( x = A /\ y = B /\ z = C ) -> ( ph <-> ps ) ) $.
	p_spc3gv $p |- ( ( A e. V /\ B e. W /\ C e. X ) -> ( A. x A. y A. z ph -> ps ) ) $= e0_spc3gv f2_spc3gv a_sup_set_class f5_spc3gv a_wceq f3_spc3gv a_sup_set_class f6_spc3gv a_wceq f4_spc3gv a_sup_set_class f7_spc3gv a_wceq a_w3a f0_spc3gv f1_spc3gv p_notbid f0_spc3gv a_wn f1_spc3gv a_wn f2_spc3gv f3_spc3gv f4_spc3gv f5_spc3gv f6_spc3gv f7_spc3gv f8_spc3gv f9_spc3gv f10_spc3gv p_spc3egv f0_spc3gv f4_spc3gv p_exnal f0_spc3gv a_wn f4_spc3gv a_wex f0_spc3gv f4_spc3gv a_wal a_wn f3_spc3gv p_exbii f0_spc3gv f4_spc3gv a_wal f3_spc3gv p_exnal f0_spc3gv a_wn f4_spc3gv a_wex f3_spc3gv a_wex f0_spc3gv f4_spc3gv a_wal a_wn f3_spc3gv a_wex f0_spc3gv f4_spc3gv a_wal f3_spc3gv a_wal a_wn p_bitri f0_spc3gv a_wn f4_spc3gv a_wex f3_spc3gv a_wex f0_spc3gv f4_spc3gv a_wal f3_spc3gv a_wal a_wn f2_spc3gv p_exbii f0_spc3gv f4_spc3gv a_wal f3_spc3gv a_wal f2_spc3gv p_exnal f0_spc3gv a_wn f4_spc3gv a_wex f3_spc3gv a_wex f2_spc3gv a_wex f0_spc3gv f4_spc3gv a_wal f3_spc3gv a_wal a_wn f2_spc3gv a_wex f0_spc3gv f4_spc3gv a_wal f3_spc3gv a_wal f2_spc3gv a_wal a_wn p_bitr2i f5_spc3gv f8_spc3gv a_wcel f6_spc3gv f9_spc3gv a_wcel f7_spc3gv f10_spc3gv a_wcel a_w3a f1_spc3gv a_wn f0_spc3gv a_wn f4_spc3gv a_wex f3_spc3gv a_wex f2_spc3gv a_wex f0_spc3gv f4_spc3gv a_wal f3_spc3gv a_wal f2_spc3gv a_wal a_wn p_syl6ibr f5_spc3gv f8_spc3gv a_wcel f6_spc3gv f9_spc3gv a_wcel f7_spc3gv f10_spc3gv a_wcel a_w3a f1_spc3gv f0_spc3gv f4_spc3gv a_wal f3_spc3gv a_wal f2_spc3gv a_wal p_con4d $.
$}

$(Rule of specialization, using implicit substitution.  (Contributed by
       NM, 22-Jun-1994.) $)

${
	$v ph ps x A  $.
	$d x A  $.
	$d x ps  $.
	f0_spcv $f wff ph $.
	f1_spcv $f wff ps $.
	f2_spcv $f set x $.
	f3_spcv $f class A $.
	e0_spcv $e |- A e. _V $.
	e1_spcv $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_spcv $p |- ( A. x ph -> ps ) $= e0_spcv e1_spcv f0_spcv f1_spcv f2_spcv f3_spcv a_cvv p_spcgv f3_spcv a_cvv a_wcel f0_spcv f2_spcv a_wal f1_spcv a_wi a_ax-mp $.
$}

$(Existential specialization, using implicit substitution.  (Contributed
       by NM, 31-Dec-1993.)  (Proof shortened by Eric Schmidt, 22-Dec-2006.) $)

${
	$v ph ps x A  $.
	$d x A  $.
	$d x ps  $.
	f0_spcev $f wff ph $.
	f1_spcev $f wff ps $.
	f2_spcev $f set x $.
	f3_spcev $f class A $.
	e0_spcev $e |- A e. _V $.
	e1_spcev $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_spcev $p |- ( ps -> E. x ph ) $= e0_spcev e1_spcev f0_spcev f1_spcev f2_spcev f3_spcev a_cvv p_spcegv f3_spcev a_cvv a_wcel f1_spcev f0_spcev f2_spcev a_wex a_wi a_ax-mp $.
$}

$(Existential specialization, using implicit substitution.  (Contributed
       by NM, 3-Aug-1995.) $)

${
	$v ph ps x y A B  $.
	$d x y A  $.
	$d x y B  $.
	$d x y ps  $.
	f0_spc2ev $f wff ph $.
	f1_spc2ev $f wff ps $.
	f2_spc2ev $f set x $.
	f3_spc2ev $f set y $.
	f4_spc2ev $f class A $.
	f5_spc2ev $f class B $.
	e0_spc2ev $e |- A e. _V $.
	e1_spc2ev $e |- B e. _V $.
	e2_spc2ev $e |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) ) $.
	p_spc2ev $p |- ( ps -> E. x E. y ph ) $= e0_spc2ev e1_spc2ev e2_spc2ev f0_spc2ev f1_spc2ev f2_spc2ev f3_spc2ev f4_spc2ev f5_spc2ev a_cvv a_cvv p_spc2egv f4_spc2ev a_cvv a_wcel f5_spc2ev a_cvv a_wcel f1_spc2ev f0_spc2ev f3_spc2ev a_wex f2_spc2ev a_wex a_wi p_mp2an $.
$}

$(A closed version of ~ rspc .  (Contributed by Andrew Salmon,
       6-Jun-2011.) $)

${
	$v ph ps x A B  $.
	$d x A  $.
	$d x B  $.
	f0_rspct $f wff ph $.
	f1_rspct $f wff ps $.
	f2_rspct $f set x $.
	f3_rspct $f class A $.
	f4_rspct $f class B $.
	e0_rspct $e |- F/ x ps $.
	p_rspct $p |- ( A. x ( x = A -> ( ph <-> ps ) ) -> ( A e. B -> ( A. x e. B ph -> ps ) ) ) $= f0_rspct f2_rspct f4_rspct a_df-ral f2_rspct a_sup_set_class f3_rspct f4_rspct p_eleq1 f2_rspct a_sup_set_class f3_rspct a_wceq f2_rspct a_sup_set_class f4_rspct a_wcel f3_rspct f4_rspct a_wcel a_wb f0_rspct f1_rspct a_wb p_adantr f2_rspct a_sup_set_class f3_rspct a_wceq f0_rspct f1_rspct a_wb p_simpr f2_rspct a_sup_set_class f3_rspct a_wceq f0_rspct f1_rspct a_wb a_wa f2_rspct a_sup_set_class f4_rspct a_wcel f3_rspct f4_rspct a_wcel f0_rspct f1_rspct p_imbi12d f2_rspct a_sup_set_class f3_rspct a_wceq f0_rspct f1_rspct a_wb f2_rspct a_sup_set_class f4_rspct a_wcel f0_rspct a_wi f3_rspct f4_rspct a_wcel f1_rspct a_wi a_wb p_ex f2_rspct a_sup_set_class f3_rspct a_wceq f0_rspct f1_rspct a_wb f2_rspct a_sup_set_class f4_rspct a_wcel f0_rspct a_wi f3_rspct f4_rspct a_wcel f1_rspct a_wi a_wb p_a2i f2_rspct a_sup_set_class f3_rspct a_wceq f0_rspct f1_rspct a_wb a_wi f2_rspct a_sup_set_class f3_rspct a_wceq f2_rspct a_sup_set_class f4_rspct a_wcel f0_rspct a_wi f3_rspct f4_rspct a_wcel f1_rspct a_wi a_wb a_wi f2_rspct p_alimi f3_rspct f4_rspct a_wcel f2_rspct p_nfv e0_rspct f3_rspct f4_rspct a_wcel f1_rspct f2_rspct p_nfim f2_rspct f3_rspct p_nfcv f2_rspct a_sup_set_class f4_rspct a_wcel f0_rspct a_wi f3_rspct f4_rspct a_wcel f1_rspct a_wi f2_rspct f3_rspct f4_rspct p_spcgft f2_rspct a_sup_set_class f3_rspct a_wceq f0_rspct f1_rspct a_wb a_wi f2_rspct a_wal f2_rspct a_sup_set_class f3_rspct a_wceq f2_rspct a_sup_set_class f4_rspct a_wcel f0_rspct a_wi f3_rspct f4_rspct a_wcel f1_rspct a_wi a_wb a_wi f2_rspct a_wal f3_rspct f4_rspct a_wcel f2_rspct a_sup_set_class f4_rspct a_wcel f0_rspct a_wi f2_rspct a_wal f3_rspct f4_rspct a_wcel f1_rspct a_wi a_wi a_wi p_syl f0_rspct f2_rspct f4_rspct a_wral f2_rspct a_sup_set_class f4_rspct a_wcel f0_rspct a_wi f2_rspct a_wal f2_rspct a_sup_set_class f3_rspct a_wceq f0_rspct f1_rspct a_wb a_wi f2_rspct a_wal f3_rspct f4_rspct a_wcel f3_rspct f4_rspct a_wcel f1_rspct a_wi p_syl7bi f2_rspct a_sup_set_class f3_rspct a_wceq f0_rspct f1_rspct a_wb a_wi f2_rspct a_wal f3_rspct f4_rspct a_wcel f0_rspct f2_rspct f4_rspct a_wral f3_rspct f4_rspct a_wcel f1_rspct p_com34 f2_rspct a_sup_set_class f3_rspct a_wceq f0_rspct f1_rspct a_wb a_wi f2_rspct a_wal f3_rspct f4_rspct a_wcel f0_rspct f2_rspct f4_rspct a_wral f1_rspct a_wi p_pm2.43d $.
$}

$(Restricted specialization, using implicit substitution.  (Contributed by
       NM, 19-Apr-2005.)  (Revised by Mario Carneiro, 11-Oct-2016.) $)

${
	$v ph ps x A B  $.
	$d x A  $.
	$d x B  $.
	f0_rspc $f wff ph $.
	f1_rspc $f wff ps $.
	f2_rspc $f set x $.
	f3_rspc $f class A $.
	f4_rspc $f class B $.
	e0_rspc $e |- F/ x ps $.
	e1_rspc $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_rspc $p |- ( A e. B -> ( A. x e. B ph -> ps ) ) $= f0_rspc f2_rspc f4_rspc a_df-ral f2_rspc f3_rspc p_nfcv f3_rspc f4_rspc a_wcel f2_rspc p_nfv e0_rspc f3_rspc f4_rspc a_wcel f1_rspc f2_rspc p_nfim f2_rspc a_sup_set_class f3_rspc f4_rspc p_eleq1 e1_rspc f2_rspc a_sup_set_class f3_rspc a_wceq f2_rspc a_sup_set_class f4_rspc a_wcel f3_rspc f4_rspc a_wcel f0_rspc f1_rspc p_imbi12d f2_rspc a_sup_set_class f4_rspc a_wcel f0_rspc a_wi f3_rspc f4_rspc a_wcel f1_rspc a_wi f2_rspc f3_rspc f4_rspc p_spcgf f2_rspc a_sup_set_class f4_rspc a_wcel f0_rspc a_wi f2_rspc a_wal f3_rspc f4_rspc a_wcel f1_rspc p_pm2.43a f0_rspc f2_rspc f4_rspc a_wral f2_rspc a_sup_set_class f4_rspc a_wcel f0_rspc a_wi f2_rspc a_wal f3_rspc f4_rspc a_wcel f1_rspc p_syl5bi $.
$}

$(Restricted existential specialization, using implicit substitution.
       (Contributed by NM, 26-May-1998.)  (Revised by Mario Carneiro,
       11-Oct-2016.) $)

${
	$v ph ps x A B  $.
	$d x A  $.
	$d x B  $.
	f0_rspce $f wff ph $.
	f1_rspce $f wff ps $.
	f2_rspce $f set x $.
	f3_rspce $f class A $.
	f4_rspce $f class B $.
	e0_rspce $e |- F/ x ps $.
	e1_rspce $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_rspce $p |- ( ( A e. B /\ ps ) -> E. x e. B ph ) $= f2_rspce f3_rspce p_nfcv f3_rspce f4_rspce a_wcel f2_rspce p_nfv e0_rspce f3_rspce f4_rspce a_wcel f1_rspce f2_rspce p_nfan f2_rspce a_sup_set_class f3_rspce f4_rspce p_eleq1 e1_rspce f2_rspce a_sup_set_class f3_rspce a_wceq f2_rspce a_sup_set_class f4_rspce a_wcel f3_rspce f4_rspce a_wcel f0_rspce f1_rspce p_anbi12d f2_rspce a_sup_set_class f4_rspce a_wcel f0_rspce a_wa f3_rspce f4_rspce a_wcel f1_rspce a_wa f2_rspce f3_rspce f4_rspce p_spcegf f3_rspce f4_rspce a_wcel f1_rspce f2_rspce a_sup_set_class f4_rspce a_wcel f0_rspce a_wa f2_rspce a_wex p_anabsi5 f0_rspce f2_rspce f4_rspce a_df-rex f3_rspce f4_rspce a_wcel f1_rspce a_wa f2_rspce a_sup_set_class f4_rspce a_wcel f0_rspce a_wa f2_rspce a_wex f0_rspce f2_rspce f4_rspce a_wrex p_sylibr $.
$}

$(Restricted specialization, using implicit substitution.  (Contributed by
       NM, 26-May-1998.) $)

${
	$v ph ps x A B  $.
	$d x A  $.
	$d x B  $.
	$d x ps  $.
	f0_rspcv $f wff ph $.
	f1_rspcv $f wff ps $.
	f2_rspcv $f set x $.
	f3_rspcv $f class A $.
	f4_rspcv $f class B $.
	e0_rspcv $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_rspcv $p |- ( A e. B -> ( A. x e. B ph -> ps ) ) $= f1_rspcv f2_rspcv p_nfv e0_rspcv f0_rspcv f1_rspcv f2_rspcv f3_rspcv f4_rspcv p_rspc $.
$}

$(Restricted specialization, using implicit substitution.  (Contributed by
       NM, 2-Feb-2006.) $)

${
	$v ph ps x A B  $.
	$d x A  $.
	$d x B  $.
	$d x ps  $.
	f0_rspccv $f wff ph $.
	f1_rspccv $f wff ps $.
	f2_rspccv $f set x $.
	f3_rspccv $f class A $.
	f4_rspccv $f class B $.
	e0_rspccv $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_rspccv $p |- ( A. x e. B ph -> ( A e. B -> ps ) ) $= e0_rspccv f0_rspccv f1_rspccv f2_rspccv f3_rspccv f4_rspccv p_rspcv f3_rspccv f4_rspccv a_wcel f0_rspccv f2_rspccv f4_rspccv a_wral f1_rspccv p_com12 $.
$}

$(Restricted specialization, using implicit substitution.  (Contributed by
       NM, 13-Sep-2005.) $)

${
	$v ph ps x A B  $.
	$d x A  $.
	$d x B  $.
	$d x ps  $.
	f0_rspcva $f wff ph $.
	f1_rspcva $f wff ps $.
	f2_rspcva $f set x $.
	f3_rspcva $f class A $.
	f4_rspcva $f class B $.
	e0_rspcva $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_rspcva $p |- ( ( A e. B /\ A. x e. B ph ) -> ps ) $= e0_rspcva f0_rspcva f1_rspcva f2_rspcva f3_rspcva f4_rspcva p_rspcv f3_rspcva f4_rspcva a_wcel f0_rspcva f2_rspcva f4_rspcva a_wral f1_rspcva p_imp $.
$}

$(Restricted specialization, using implicit substitution.  (Contributed by
       NM, 26-Jul-2006.)  (Proof shortened by Andrew Salmon, 8-Jun-2011.) $)

${
	$v ph ps x A B  $.
	$d x A  $.
	$d x B  $.
	$d x ps  $.
	f0_rspccva $f wff ph $.
	f1_rspccva $f wff ps $.
	f2_rspccva $f set x $.
	f3_rspccva $f class A $.
	f4_rspccva $f class B $.
	e0_rspccva $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_rspccva $p |- ( ( A. x e. B ph /\ A e. B ) -> ps ) $= e0_rspccva f0_rspccva f1_rspccva f2_rspccva f3_rspccva f4_rspccva p_rspcv f3_rspccva f4_rspccva a_wcel f0_rspccva f2_rspccva f4_rspccva a_wral f1_rspccva p_impcom $.
$}

$(Restricted existential specialization, using implicit substitution.
       (Contributed by NM, 26-May-1998.) $)

${
	$v ph ps x A B  $.
	$d x A  $.
	$d x B  $.
	$d x ps  $.
	f0_rspcev $f wff ph $.
	f1_rspcev $f wff ps $.
	f2_rspcev $f set x $.
	f3_rspcev $f class A $.
	f4_rspcev $f class B $.
	e0_rspcev $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_rspcev $p |- ( ( A e. B /\ ps ) -> E. x e. B ph ) $= f1_rspcev f2_rspcev p_nfv e0_rspcev f0_rspcev f1_rspcev f2_rspcev f3_rspcev f4_rspcev p_rspce $.
$}

$(Restricted specialization, using implicit substitution.  (Contributed
         by Mario Carneiro, 4-Jan-2017.) $)

${
	$v ph ps ch x A B  $.
	$d x A  $.
	$d x B  $.
	$d x ph  $.
	$d x ch  $.
	f0_rspcimdv $f wff ph $.
	f1_rspcimdv $f wff ps $.
	f2_rspcimdv $f wff ch $.
	f3_rspcimdv $f set x $.
	f4_rspcimdv $f class A $.
	f5_rspcimdv $f class B $.
	e0_rspcimdv $e |- ( ph -> A e. B ) $.
	e1_rspcimdv $e |- ( ( ph /\ x = A ) -> ( ps -> ch ) ) $.
	p_rspcimdv $p |- ( ph -> ( A. x e. B ps -> ch ) ) $= f1_rspcimdv f3_rspcimdv f5_rspcimdv a_df-ral e0_rspcimdv e0_rspcimdv f0_rspcimdv f3_rspcimdv a_sup_set_class f4_rspcimdv a_wceq p_simpr f0_rspcimdv f3_rspcimdv a_sup_set_class f4_rspcimdv a_wceq a_wa f3_rspcimdv a_sup_set_class f4_rspcimdv f5_rspcimdv p_eleq1d f0_rspcimdv f3_rspcimdv a_sup_set_class f4_rspcimdv a_wceq a_wa f3_rspcimdv a_sup_set_class f5_rspcimdv a_wcel f4_rspcimdv f5_rspcimdv a_wcel p_biimprd e1_rspcimdv f0_rspcimdv f3_rspcimdv a_sup_set_class f4_rspcimdv a_wceq a_wa f4_rspcimdv f5_rspcimdv a_wcel f3_rspcimdv a_sup_set_class f5_rspcimdv a_wcel f1_rspcimdv f2_rspcimdv p_imim12d f0_rspcimdv f3_rspcimdv a_sup_set_class f5_rspcimdv a_wcel f1_rspcimdv a_wi f4_rspcimdv f5_rspcimdv a_wcel f2_rspcimdv a_wi f3_rspcimdv f4_rspcimdv f5_rspcimdv p_spcimdv f0_rspcimdv f3_rspcimdv a_sup_set_class f5_rspcimdv a_wcel f1_rspcimdv a_wi f3_rspcimdv a_wal f4_rspcimdv f5_rspcimdv a_wcel f2_rspcimdv p_mpid f1_rspcimdv f3_rspcimdv f5_rspcimdv a_wral f3_rspcimdv a_sup_set_class f5_rspcimdv a_wcel f1_rspcimdv a_wi f3_rspcimdv a_wal f0_rspcimdv f2_rspcimdv p_syl5bi $.
$}

$(Restricted existential specialization, using implicit substitution.
       (Contributed by Mario Carneiro, 4-Jan-2017.) $)

${
	$v ph ps ch x A B  $.
	$d x A  $.
	$d x B  $.
	$d x ph  $.
	$d x ch  $.
	f0_rspcimedv $f wff ph $.
	f1_rspcimedv $f wff ps $.
	f2_rspcimedv $f wff ch $.
	f3_rspcimedv $f set x $.
	f4_rspcimedv $f class A $.
	f5_rspcimedv $f class B $.
	e0_rspcimedv $e |- ( ph -> A e. B ) $.
	e1_rspcimedv $e |- ( ( ph /\ x = A ) -> ( ch -> ps ) ) $.
	p_rspcimedv $p |- ( ph -> ( ch -> E. x e. B ps ) ) $= e0_rspcimedv e1_rspcimedv f0_rspcimedv f3_rspcimedv a_sup_set_class f4_rspcimedv a_wceq a_wa f2_rspcimedv f1_rspcimedv p_con3d f0_rspcimedv f1_rspcimedv a_wn f2_rspcimedv a_wn f3_rspcimedv f4_rspcimedv f5_rspcimedv p_rspcimdv f0_rspcimedv f1_rspcimedv a_wn f3_rspcimedv f5_rspcimedv a_wral f2_rspcimedv p_con2d f1_rspcimedv f3_rspcimedv f5_rspcimedv p_dfrex2 f0_rspcimedv f2_rspcimedv f1_rspcimedv a_wn f3_rspcimedv f5_rspcimedv a_wral a_wn f1_rspcimedv f3_rspcimedv f5_rspcimedv a_wrex p_syl6ibr $.
$}

$(Restricted specialization, using implicit substitution.  (Contributed by
       NM, 17-Feb-2007.)  (Revised by Mario Carneiro, 4-Jan-2017.) $)

${
	$v ph ps ch x A B  $.
	$d x A  $.
	$d x B  $.
	$d x ph  $.
	$d x ch  $.
	f0_rspcdv $f wff ph $.
	f1_rspcdv $f wff ps $.
	f2_rspcdv $f wff ch $.
	f3_rspcdv $f set x $.
	f4_rspcdv $f class A $.
	f5_rspcdv $f class B $.
	e0_rspcdv $e |- ( ph -> A e. B ) $.
	e1_rspcdv $e |- ( ( ph /\ x = A ) -> ( ps <-> ch ) ) $.
	p_rspcdv $p |- ( ph -> ( A. x e. B ps -> ch ) ) $= e0_rspcdv e1_rspcdv f0_rspcdv f3_rspcdv a_sup_set_class f4_rspcdv a_wceq a_wa f1_rspcdv f2_rspcdv p_biimpd f0_rspcdv f1_rspcdv f2_rspcdv f3_rspcdv f4_rspcdv f5_rspcdv p_rspcimdv $.
$}

$(Restricted existential specialization, using implicit substitution.
       (Contributed by FL, 17-Apr-2007.)  (Revised by Mario Carneiro,
       4-Jan-2017.) $)

${
	$v ph ps ch x A B  $.
	$d x A  $.
	$d x B  $.
	$d x ph  $.
	$d x ch  $.
	f0_rspcedv $f wff ph $.
	f1_rspcedv $f wff ps $.
	f2_rspcedv $f wff ch $.
	f3_rspcedv $f set x $.
	f4_rspcedv $f class A $.
	f5_rspcedv $f class B $.
	e0_rspcedv $e |- ( ph -> A e. B ) $.
	e1_rspcedv $e |- ( ( ph /\ x = A ) -> ( ps <-> ch ) ) $.
	p_rspcedv $p |- ( ph -> ( ch -> E. x e. B ps ) ) $= e0_rspcedv e1_rspcedv f0_rspcedv f3_rspcedv a_sup_set_class f4_rspcedv a_wceq a_wa f1_rspcedv f2_rspcedv p_biimprd f0_rspcedv f1_rspcedv f2_rspcedv f3_rspcedv f4_rspcedv f5_rspcedv p_rspcimedv $.
$}

$(2-variable restricted specialization, using implicit substitution.
       (Contributed by NM, 9-Nov-2012.) $)

${
	$v ph ps ch x y A B C D  $.
	$d x y A  $.
	$d y B  $.
	$d x C  $.
	$d x y D  $.
	f0_rspc2 $f wff ph $.
	f1_rspc2 $f wff ps $.
	f2_rspc2 $f wff ch $.
	f3_rspc2 $f set x $.
	f4_rspc2 $f set y $.
	f5_rspc2 $f class A $.
	f6_rspc2 $f class B $.
	f7_rspc2 $f class C $.
	f8_rspc2 $f class D $.
	e0_rspc2 $e |- F/ x ch $.
	e1_rspc2 $e |- F/ y ps $.
	e2_rspc2 $e |- ( x = A -> ( ph <-> ch ) ) $.
	e3_rspc2 $e |- ( y = B -> ( ch <-> ps ) ) $.
	p_rspc2 $p |- ( ( A e. C /\ B e. D ) -> ( A. x e. C A. y e. D ph -> ps ) ) $= f3_rspc2 f8_rspc2 p_nfcv e0_rspc2 f2_rspc2 f3_rspc2 f4_rspc2 f8_rspc2 p_nfral e2_rspc2 f3_rspc2 a_sup_set_class f5_rspc2 a_wceq f0_rspc2 f2_rspc2 f4_rspc2 f8_rspc2 p_ralbidv f0_rspc2 f4_rspc2 f8_rspc2 a_wral f2_rspc2 f4_rspc2 f8_rspc2 a_wral f3_rspc2 f5_rspc2 f7_rspc2 p_rspc e1_rspc2 e3_rspc2 f2_rspc2 f1_rspc2 f4_rspc2 f6_rspc2 f8_rspc2 p_rspc f5_rspc2 f7_rspc2 a_wcel f0_rspc2 f4_rspc2 f8_rspc2 a_wral f3_rspc2 f7_rspc2 a_wral f2_rspc2 f4_rspc2 f8_rspc2 a_wral f6_rspc2 f8_rspc2 a_wcel f1_rspc2 p_sylan9 $.
$}

$(2-variable restricted specialization, using implicit substitution.
       (Contributed by NM, 13-Sep-1999.) $)

${
	$v ph ps ch x y A B C D  $.
	$d x y A  $.
	$d y B  $.
	$d x C  $.
	$d x y D  $.
	$d x ch  $.
	$d y ps  $.
	f0_rspc2v $f wff ph $.
	f1_rspc2v $f wff ps $.
	f2_rspc2v $f wff ch $.
	f3_rspc2v $f set x $.
	f4_rspc2v $f set y $.
	f5_rspc2v $f class A $.
	f6_rspc2v $f class B $.
	f7_rspc2v $f class C $.
	f8_rspc2v $f class D $.
	e0_rspc2v $e |- ( x = A -> ( ph <-> ch ) ) $.
	e1_rspc2v $e |- ( y = B -> ( ch <-> ps ) ) $.
	p_rspc2v $p |- ( ( A e. C /\ B e. D ) -> ( A. x e. C A. y e. D ph -> ps ) ) $= f2_rspc2v f3_rspc2v p_nfv f1_rspc2v f4_rspc2v p_nfv e0_rspc2v e1_rspc2v f0_rspc2v f1_rspc2v f2_rspc2v f3_rspc2v f4_rspc2v f5_rspc2v f6_rspc2v f7_rspc2v f8_rspc2v p_rspc2 $.
$}

$(2-variable restricted specialization, using implicit substitution.
       (Contributed by NM, 18-Jun-2014.) $)

${
	$v ph ps ch x y A B C D  $.
	$d x y A  $.
	$d y B  $.
	$d x C  $.
	$d x y D  $.
	$d x ch  $.
	$d y ps  $.
	f0_rspc2va $f wff ph $.
	f1_rspc2va $f wff ps $.
	f2_rspc2va $f wff ch $.
	f3_rspc2va $f set x $.
	f4_rspc2va $f set y $.
	f5_rspc2va $f class A $.
	f6_rspc2va $f class B $.
	f7_rspc2va $f class C $.
	f8_rspc2va $f class D $.
	e0_rspc2va $e |- ( x = A -> ( ph <-> ch ) ) $.
	e1_rspc2va $e |- ( y = B -> ( ch <-> ps ) ) $.
	p_rspc2va $p |- ( ( ( A e. C /\ B e. D ) /\ A. x e. C A. y e. D ph ) -> ps ) $= e0_rspc2va e1_rspc2va f0_rspc2va f1_rspc2va f2_rspc2va f3_rspc2va f4_rspc2va f5_rspc2va f6_rspc2va f7_rspc2va f8_rspc2va p_rspc2v f5_rspc2va f7_rspc2va a_wcel f6_rspc2va f8_rspc2va a_wcel a_wa f0_rspc2va f4_rspc2va f8_rspc2va a_wral f3_rspc2va f7_rspc2va a_wral f1_rspc2va p_imp $.
$}

$(2-variable restricted existential specialization, using implicit
       substitution.  (Contributed by NM, 16-Oct-1999.) $)

${
	$v ph ps ch x y A B C D  $.
	$d x y A  $.
	$d y B  $.
	$d x C  $.
	$d x y D  $.
	$d x ch  $.
	$d y ps  $.
	f0_rspc2ev $f wff ph $.
	f1_rspc2ev $f wff ps $.
	f2_rspc2ev $f wff ch $.
	f3_rspc2ev $f set x $.
	f4_rspc2ev $f set y $.
	f5_rspc2ev $f class A $.
	f6_rspc2ev $f class B $.
	f7_rspc2ev $f class C $.
	f8_rspc2ev $f class D $.
	e0_rspc2ev $e |- ( x = A -> ( ph <-> ch ) ) $.
	e1_rspc2ev $e |- ( y = B -> ( ch <-> ps ) ) $.
	p_rspc2ev $p |- ( ( A e. C /\ B e. D /\ ps ) -> E. x e. C E. y e. D ph ) $= e1_rspc2ev f2_rspc2ev f1_rspc2ev f4_rspc2ev f6_rspc2ev f8_rspc2ev p_rspcev f6_rspc2ev f8_rspc2ev a_wcel f1_rspc2ev a_wa f2_rspc2ev f4_rspc2ev f8_rspc2ev a_wrex f5_rspc2ev f7_rspc2ev a_wcel p_anim2i f5_rspc2ev f7_rspc2ev a_wcel f6_rspc2ev f8_rspc2ev a_wcel f1_rspc2ev f5_rspc2ev f7_rspc2ev a_wcel f2_rspc2ev f4_rspc2ev f8_rspc2ev a_wrex a_wa p_3impb e0_rspc2ev f3_rspc2ev a_sup_set_class f5_rspc2ev a_wceq f0_rspc2ev f2_rspc2ev f4_rspc2ev f8_rspc2ev p_rexbidv f0_rspc2ev f4_rspc2ev f8_rspc2ev a_wrex f2_rspc2ev f4_rspc2ev f8_rspc2ev a_wrex f3_rspc2ev f5_rspc2ev f7_rspc2ev p_rspcev f5_rspc2ev f7_rspc2ev a_wcel f6_rspc2ev f8_rspc2ev a_wcel f1_rspc2ev a_w3a f5_rspc2ev f7_rspc2ev a_wcel f2_rspc2ev f4_rspc2ev f8_rspc2ev a_wrex a_wa f0_rspc2ev f4_rspc2ev f8_rspc2ev a_wrex f3_rspc2ev f7_rspc2ev a_wrex p_syl $.
$}

$(3-variable restricted specialization, using implicit substitution.
       (Contributed by NM, 10-May-2005.) $)

${
	$v ph ps ch th x y z A B C R S T  $.
	$d z ps  $.
	$d x ch  $.
	$d y th  $.
	$d x y z A  $.
	$d y z B  $.
	$d z C  $.
	$d x R  $.
	$d x y S  $.
	$d x y z T  $.
	f0_rspc3v $f wff ph $.
	f1_rspc3v $f wff ps $.
	f2_rspc3v $f wff ch $.
	f3_rspc3v $f wff th $.
	f4_rspc3v $f set x $.
	f5_rspc3v $f set y $.
	f6_rspc3v $f set z $.
	f7_rspc3v $f class A $.
	f8_rspc3v $f class B $.
	f9_rspc3v $f class C $.
	f10_rspc3v $f class R $.
	f11_rspc3v $f class S $.
	f12_rspc3v $f class T $.
	e0_rspc3v $e |- ( x = A -> ( ph <-> ch ) ) $.
	e1_rspc3v $e |- ( y = B -> ( ch <-> th ) ) $.
	e2_rspc3v $e |- ( z = C -> ( th <-> ps ) ) $.
	p_rspc3v $p |- ( ( A e. R /\ B e. S /\ C e. T ) -> ( A. x e. R A. y e. S A. z e. T ph -> ps ) ) $= e0_rspc3v f4_rspc3v a_sup_set_class f7_rspc3v a_wceq f0_rspc3v f2_rspc3v f6_rspc3v f12_rspc3v p_ralbidv e1_rspc3v f5_rspc3v a_sup_set_class f8_rspc3v a_wceq f2_rspc3v f3_rspc3v f6_rspc3v f12_rspc3v p_ralbidv f0_rspc3v f6_rspc3v f12_rspc3v a_wral f3_rspc3v f6_rspc3v f12_rspc3v a_wral f2_rspc3v f6_rspc3v f12_rspc3v a_wral f4_rspc3v f5_rspc3v f7_rspc3v f8_rspc3v f10_rspc3v f11_rspc3v p_rspc2v e2_rspc3v f3_rspc3v f1_rspc3v f6_rspc3v f9_rspc3v f12_rspc3v p_rspcv f7_rspc3v f10_rspc3v a_wcel f8_rspc3v f11_rspc3v a_wcel a_wa f0_rspc3v f6_rspc3v f12_rspc3v a_wral f5_rspc3v f11_rspc3v a_wral f4_rspc3v f10_rspc3v a_wral f3_rspc3v f6_rspc3v f12_rspc3v a_wral f9_rspc3v f12_rspc3v a_wcel f1_rspc3v p_sylan9 f7_rspc3v f10_rspc3v a_wcel f8_rspc3v f11_rspc3v a_wcel f9_rspc3v f12_rspc3v a_wcel f0_rspc3v f6_rspc3v f12_rspc3v a_wral f5_rspc3v f11_rspc3v a_wral f4_rspc3v f10_rspc3v a_wral f1_rspc3v a_wi p_3impa $.
$}

$(3-variable restricted existentional specialization, using implicit
       substitution.  (Contributed by NM, 25-Jul-2012.) $)

${
	$v ph ps ch th x y z A B C R S T  $.
	$d z ps  $.
	$d x ch  $.
	$d y th  $.
	$d x y z A  $.
	$d y z B  $.
	$d z C  $.
	$d x R  $.
	$d x y S  $.
	$d x y z T  $.
	f0_rspc3ev $f wff ph $.
	f1_rspc3ev $f wff ps $.
	f2_rspc3ev $f wff ch $.
	f3_rspc3ev $f wff th $.
	f4_rspc3ev $f set x $.
	f5_rspc3ev $f set y $.
	f6_rspc3ev $f set z $.
	f7_rspc3ev $f class A $.
	f8_rspc3ev $f class B $.
	f9_rspc3ev $f class C $.
	f10_rspc3ev $f class R $.
	f11_rspc3ev $f class S $.
	f12_rspc3ev $f class T $.
	e0_rspc3ev $e |- ( x = A -> ( ph <-> ch ) ) $.
	e1_rspc3ev $e |- ( y = B -> ( ch <-> th ) ) $.
	e2_rspc3ev $e |- ( z = C -> ( th <-> ps ) ) $.
	p_rspc3ev $p |- ( ( ( A e. R /\ B e. S /\ C e. T ) /\ ps ) -> E. x e. R E. y e. S E. z e. T ph ) $= f7_rspc3ev f10_rspc3ev a_wcel f8_rspc3ev f11_rspc3ev a_wcel f9_rspc3ev f12_rspc3ev a_wcel f1_rspc3ev p_simpl1 f7_rspc3ev f10_rspc3ev a_wcel f8_rspc3ev f11_rspc3ev a_wcel f9_rspc3ev f12_rspc3ev a_wcel f1_rspc3ev p_simpl2 e2_rspc3ev f3_rspc3ev f1_rspc3ev f6_rspc3ev f9_rspc3ev f12_rspc3ev p_rspcev f9_rspc3ev f12_rspc3ev a_wcel f7_rspc3ev f10_rspc3ev a_wcel f1_rspc3ev f3_rspc3ev f6_rspc3ev f12_rspc3ev a_wrex f8_rspc3ev f11_rspc3ev a_wcel p_3ad2antl3 e0_rspc3ev f4_rspc3ev a_sup_set_class f7_rspc3ev a_wceq f0_rspc3ev f2_rspc3ev f6_rspc3ev f12_rspc3ev p_rexbidv e1_rspc3ev f5_rspc3ev a_sup_set_class f8_rspc3ev a_wceq f2_rspc3ev f3_rspc3ev f6_rspc3ev f12_rspc3ev p_rexbidv f0_rspc3ev f6_rspc3ev f12_rspc3ev a_wrex f3_rspc3ev f6_rspc3ev f12_rspc3ev a_wrex f2_rspc3ev f6_rspc3ev f12_rspc3ev a_wrex f4_rspc3ev f5_rspc3ev f7_rspc3ev f8_rspc3ev f10_rspc3ev f11_rspc3ev p_rspc2ev f7_rspc3ev f10_rspc3ev a_wcel f8_rspc3ev f11_rspc3ev a_wcel f9_rspc3ev f12_rspc3ev a_wcel a_w3a f1_rspc3ev a_wa f7_rspc3ev f10_rspc3ev a_wcel f8_rspc3ev f11_rspc3ev a_wcel f3_rspc3ev f6_rspc3ev f12_rspc3ev a_wrex f0_rspc3ev f6_rspc3ev f12_rspc3ev a_wrex f5_rspc3ev f11_rspc3ev a_wrex f4_rspc3ev f10_rspc3ev a_wrex p_syl3anc $.
$}

$(A variable introduction law for class equality.  (Contributed by NM,
       14-Apr-1995.)  (Proof shortened by Andrew Salmon, 8-Jun-2011.) $)

${
	$v x A B  $.
	$d x A  $.
	$d x B  $.
	f0_eqvinc $f set x $.
	f1_eqvinc $f class A $.
	f2_eqvinc $f class B $.
	e0_eqvinc $e |- A e. _V $.
	p_eqvinc $p |- ( A = B <-> E. x ( x = A /\ x = B ) ) $= e0_eqvinc f0_eqvinc f1_eqvinc p_isseti f0_eqvinc a_sup_set_class f1_eqvinc a_wceq f1_eqvinc f2_eqvinc a_wceq a_ax-1 f0_eqvinc a_sup_set_class f1_eqvinc f2_eqvinc p_eqtr f0_eqvinc a_sup_set_class f1_eqvinc a_wceq f1_eqvinc f2_eqvinc a_wceq f0_eqvinc a_sup_set_class f2_eqvinc a_wceq p_ex f0_eqvinc a_sup_set_class f1_eqvinc a_wceq f1_eqvinc f2_eqvinc a_wceq f0_eqvinc a_sup_set_class f1_eqvinc a_wceq a_wi f1_eqvinc f2_eqvinc a_wceq f0_eqvinc a_sup_set_class f2_eqvinc a_wceq a_wi p_jca f0_eqvinc a_sup_set_class f1_eqvinc a_wceq f1_eqvinc f2_eqvinc a_wceq f0_eqvinc a_sup_set_class f1_eqvinc a_wceq a_wi f1_eqvinc f2_eqvinc a_wceq f0_eqvinc a_sup_set_class f2_eqvinc a_wceq a_wi a_wa f0_eqvinc p_eximi f1_eqvinc f2_eqvinc a_wceq f0_eqvinc a_sup_set_class f1_eqvinc a_wceq f0_eqvinc a_sup_set_class f2_eqvinc a_wceq p_pm3.43 f1_eqvinc f2_eqvinc a_wceq f0_eqvinc a_sup_set_class f1_eqvinc a_wceq a_wi f1_eqvinc f2_eqvinc a_wceq f0_eqvinc a_sup_set_class f2_eqvinc a_wceq a_wi a_wa f1_eqvinc f2_eqvinc a_wceq f0_eqvinc a_sup_set_class f1_eqvinc a_wceq f0_eqvinc a_sup_set_class f2_eqvinc a_wceq a_wa a_wi f0_eqvinc p_eximi f0_eqvinc a_sup_set_class f1_eqvinc a_wceq f0_eqvinc a_wex f1_eqvinc f2_eqvinc a_wceq f0_eqvinc a_sup_set_class f1_eqvinc a_wceq a_wi f1_eqvinc f2_eqvinc a_wceq f0_eqvinc a_sup_set_class f2_eqvinc a_wceq a_wi a_wa f0_eqvinc a_wex f1_eqvinc f2_eqvinc a_wceq f0_eqvinc a_sup_set_class f1_eqvinc a_wceq f0_eqvinc a_sup_set_class f2_eqvinc a_wceq a_wa a_wi f0_eqvinc a_wex p_mp2b f1_eqvinc f2_eqvinc a_wceq f0_eqvinc a_sup_set_class f1_eqvinc a_wceq f0_eqvinc a_sup_set_class f2_eqvinc a_wceq a_wa f0_eqvinc p_19.37aiv f0_eqvinc a_sup_set_class f1_eqvinc f2_eqvinc p_eqtr2 f0_eqvinc a_sup_set_class f1_eqvinc a_wceq f0_eqvinc a_sup_set_class f2_eqvinc a_wceq a_wa f1_eqvinc f2_eqvinc a_wceq f0_eqvinc p_exlimiv f1_eqvinc f2_eqvinc a_wceq f0_eqvinc a_sup_set_class f1_eqvinc a_wceq f0_eqvinc a_sup_set_class f2_eqvinc a_wceq a_wa f0_eqvinc a_wex p_impbii $.
$}

$(A variable introduction law for class equality, using bound-variable
       hypotheses instead of distinct variable conditions.  (Contributed by NM,
       14-Sep-2003.) $)

${
	$v x A B  $.
	$d A y  $.
	$d B y  $.
	$d x y  $.
	f0_eqvincf $f set x $.
	f1_eqvincf $f class A $.
	f2_eqvincf $f class B $.
	i0_eqvincf $f set y $.
	e0_eqvincf $e |- F/_ x A $.
	e1_eqvincf $e |- F/_ x B $.
	e2_eqvincf $e |- A e. _V $.
	p_eqvincf $p |- ( A = B <-> E. x ( x = A /\ x = B ) ) $= e2_eqvincf i0_eqvincf f1_eqvincf f2_eqvincf p_eqvinc e0_eqvincf f0_eqvincf i0_eqvincf a_sup_set_class f1_eqvincf p_nfeq2 e1_eqvincf f0_eqvincf i0_eqvincf a_sup_set_class f2_eqvincf p_nfeq2 i0_eqvincf a_sup_set_class f1_eqvincf a_wceq i0_eqvincf a_sup_set_class f2_eqvincf a_wceq f0_eqvincf p_nfan f0_eqvincf a_sup_set_class f1_eqvincf a_wceq f0_eqvincf a_sup_set_class f2_eqvincf a_wceq a_wa i0_eqvincf p_nfv i0_eqvincf a_sup_set_class f0_eqvincf a_sup_set_class f1_eqvincf p_eqeq1 i0_eqvincf a_sup_set_class f0_eqvincf a_sup_set_class f2_eqvincf p_eqeq1 i0_eqvincf a_sup_set_class f0_eqvincf a_sup_set_class a_wceq i0_eqvincf a_sup_set_class f1_eqvincf a_wceq f0_eqvincf a_sup_set_class f1_eqvincf a_wceq i0_eqvincf a_sup_set_class f2_eqvincf a_wceq f0_eqvincf a_sup_set_class f2_eqvincf a_wceq p_anbi12d i0_eqvincf a_sup_set_class f1_eqvincf a_wceq i0_eqvincf a_sup_set_class f2_eqvincf a_wceq a_wa f0_eqvincf a_sup_set_class f1_eqvincf a_wceq f0_eqvincf a_sup_set_class f2_eqvincf a_wceq a_wa i0_eqvincf f0_eqvincf p_cbvex f1_eqvincf f2_eqvincf a_wceq i0_eqvincf a_sup_set_class f1_eqvincf a_wceq i0_eqvincf a_sup_set_class f2_eqvincf a_wceq a_wa i0_eqvincf a_wex f0_eqvincf a_sup_set_class f1_eqvincf a_wceq f0_eqvincf a_sup_set_class f2_eqvincf a_wceq a_wa f0_eqvincf a_wex p_bitri $.
$}

$(Two ways to express substitution of ` A ` for ` x ` in ` ph ` .
       (Contributed by NM, 2-Mar-1995.) $)

${
	$v ph x A  $.
	$d x A y  $.
	$d ph y  $.
	f0_alexeq $f wff ph $.
	f1_alexeq $f set x $.
	f2_alexeq $f class A $.
	i0_alexeq $f set y $.
	e0_alexeq $e |- A e. _V $.
	p_alexeq $p |- ( A. x ( x = A -> ph ) <-> E. x ( x = A /\ ph ) ) $= e0_alexeq i0_alexeq a_sup_set_class f2_alexeq f1_alexeq a_sup_set_class p_eqeq2 i0_alexeq a_sup_set_class f2_alexeq a_wceq f1_alexeq a_sup_set_class i0_alexeq a_sup_set_class a_wceq f1_alexeq a_sup_set_class f2_alexeq a_wceq f0_alexeq p_anbi1d i0_alexeq a_sup_set_class f2_alexeq a_wceq f1_alexeq a_sup_set_class i0_alexeq a_sup_set_class a_wceq f0_alexeq a_wa f1_alexeq a_sup_set_class f2_alexeq a_wceq f0_alexeq a_wa f1_alexeq p_exbidv i0_alexeq a_sup_set_class f2_alexeq f1_alexeq a_sup_set_class p_eqeq2 i0_alexeq a_sup_set_class f2_alexeq a_wceq f1_alexeq a_sup_set_class i0_alexeq a_sup_set_class a_wceq f1_alexeq a_sup_set_class f2_alexeq a_wceq f0_alexeq p_imbi1d i0_alexeq a_sup_set_class f2_alexeq a_wceq f1_alexeq a_sup_set_class i0_alexeq a_sup_set_class a_wceq f0_alexeq a_wi f1_alexeq a_sup_set_class f2_alexeq a_wceq f0_alexeq a_wi f1_alexeq p_albidv f0_alexeq f1_alexeq i0_alexeq p_sb56 f1_alexeq a_sup_set_class i0_alexeq a_sup_set_class a_wceq f0_alexeq a_wa f1_alexeq a_wex f1_alexeq a_sup_set_class i0_alexeq a_sup_set_class a_wceq f0_alexeq a_wi f1_alexeq a_wal f1_alexeq a_sup_set_class f2_alexeq a_wceq f0_alexeq a_wa f1_alexeq a_wex f1_alexeq a_sup_set_class f2_alexeq a_wceq f0_alexeq a_wi f1_alexeq a_wal i0_alexeq f2_alexeq p_vtoclb f1_alexeq a_sup_set_class f2_alexeq a_wceq f0_alexeq a_wa f1_alexeq a_wex f1_alexeq a_sup_set_class f2_alexeq a_wceq f0_alexeq a_wi f1_alexeq a_wal p_bicomi $.
$}

$(Equality implies equivalence with substitution.  (Contributed by NM,
       2-Mar-1995.) $)

${
	$v ph x A  $.
	$d x A y  $.
	$d ph y  $.
	f0_ceqex $f wff ph $.
	f1_ceqex $f set x $.
	f2_ceqex $f class A $.
	i0_ceqex $f set y $.
	p_ceqex $p |- ( x = A -> ( ph <-> E. x ( x = A /\ ph ) ) ) $= f1_ceqex a_sup_set_class f2_ceqex a_wceq f1_ceqex p_19.8a f1_ceqex f2_ceqex p_isset f1_ceqex a_sup_set_class f2_ceqex a_wceq f1_ceqex a_sup_set_class f2_ceqex a_wceq f1_ceqex a_wex f2_ceqex a_cvv a_wcel p_sylibr i0_ceqex a_sup_set_class f2_ceqex f1_ceqex a_sup_set_class p_eqeq2 i0_ceqex a_sup_set_class f2_ceqex f1_ceqex a_sup_set_class p_eqeq2 i0_ceqex a_sup_set_class f2_ceqex a_wceq f1_ceqex a_sup_set_class i0_ceqex a_sup_set_class a_wceq f1_ceqex a_sup_set_class f2_ceqex a_wceq f0_ceqex p_anbi1d i0_ceqex a_sup_set_class f2_ceqex a_wceq f1_ceqex a_sup_set_class i0_ceqex a_sup_set_class a_wceq f0_ceqex a_wa f1_ceqex a_sup_set_class f2_ceqex a_wceq f0_ceqex a_wa f1_ceqex p_exbidv i0_ceqex a_sup_set_class f2_ceqex a_wceq f1_ceqex a_sup_set_class i0_ceqex a_sup_set_class a_wceq f0_ceqex a_wa f1_ceqex a_wex f1_ceqex a_sup_set_class f2_ceqex a_wceq f0_ceqex a_wa f1_ceqex a_wex f0_ceqex p_bibi2d i0_ceqex a_sup_set_class f2_ceqex a_wceq f1_ceqex a_sup_set_class i0_ceqex a_sup_set_class a_wceq f1_ceqex a_sup_set_class f2_ceqex a_wceq f0_ceqex f1_ceqex a_sup_set_class i0_ceqex a_sup_set_class a_wceq f0_ceqex a_wa f1_ceqex a_wex a_wb f0_ceqex f1_ceqex a_sup_set_class f2_ceqex a_wceq f0_ceqex a_wa f1_ceqex a_wex a_wb p_imbi12d f1_ceqex a_sup_set_class i0_ceqex a_sup_set_class a_wceq f0_ceqex a_wa f1_ceqex p_19.8a f1_ceqex a_sup_set_class i0_ceqex a_sup_set_class a_wceq f0_ceqex f1_ceqex a_sup_set_class i0_ceqex a_sup_set_class a_wceq f0_ceqex a_wa f1_ceqex a_wex p_ex i0_ceqex p_vex f0_ceqex f1_ceqex i0_ceqex a_sup_set_class p_alexeq f1_ceqex a_sup_set_class i0_ceqex a_sup_set_class a_wceq f0_ceqex a_wi f1_ceqex p_sp f1_ceqex a_sup_set_class i0_ceqex a_sup_set_class a_wceq f0_ceqex a_wi f1_ceqex a_wal f1_ceqex a_sup_set_class i0_ceqex a_sup_set_class a_wceq f0_ceqex p_com12 f1_ceqex a_sup_set_class i0_ceqex a_sup_set_class a_wceq f0_ceqex a_wa f1_ceqex a_wex f1_ceqex a_sup_set_class i0_ceqex a_sup_set_class a_wceq f0_ceqex a_wi f1_ceqex a_wal f1_ceqex a_sup_set_class i0_ceqex a_sup_set_class a_wceq f0_ceqex p_syl5bir f1_ceqex a_sup_set_class i0_ceqex a_sup_set_class a_wceq f0_ceqex f1_ceqex a_sup_set_class i0_ceqex a_sup_set_class a_wceq f0_ceqex a_wa f1_ceqex a_wex p_impbid f1_ceqex a_sup_set_class i0_ceqex a_sup_set_class a_wceq f0_ceqex f1_ceqex a_sup_set_class i0_ceqex a_sup_set_class a_wceq f0_ceqex a_wa f1_ceqex a_wex a_wb a_wi f1_ceqex a_sup_set_class f2_ceqex a_wceq f0_ceqex f1_ceqex a_sup_set_class f2_ceqex a_wceq f0_ceqex a_wa f1_ceqex a_wex a_wb a_wi i0_ceqex f2_ceqex a_cvv p_vtoclg f2_ceqex a_cvv a_wcel f1_ceqex a_sup_set_class f2_ceqex a_wceq f0_ceqex f1_ceqex a_sup_set_class f2_ceqex a_wceq f0_ceqex a_wa f1_ceqex a_wex a_wb p_mpcom $.
$}

$(A representation of explicit substitution of a class for a variable,
       inferred from an implicit substitution hypothesis.  (Contributed by NM,
       11-Oct-2004.) $)

${
	$v ph ps x A V  $.
	$d x A  $.
	f0_ceqsexg $f wff ph $.
	f1_ceqsexg $f wff ps $.
	f2_ceqsexg $f set x $.
	f3_ceqsexg $f class A $.
	f4_ceqsexg $f class V $.
	e0_ceqsexg $e |- F/ x ps $.
	e1_ceqsexg $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_ceqsexg $p |- ( A e. V -> ( E. x ( x = A /\ ph ) <-> ps ) ) $= f2_ceqsexg f3_ceqsexg p_nfcv f2_ceqsexg a_sup_set_class f3_ceqsexg a_wceq f0_ceqsexg a_wa f2_ceqsexg p_nfe1 e0_ceqsexg f2_ceqsexg a_sup_set_class f3_ceqsexg a_wceq f0_ceqsexg a_wa f2_ceqsexg a_wex f1_ceqsexg f2_ceqsexg p_nfbi f0_ceqsexg f2_ceqsexg f3_ceqsexg p_ceqex e1_ceqsexg f2_ceqsexg a_sup_set_class f3_ceqsexg a_wceq f0_ceqsexg f2_ceqsexg a_sup_set_class f3_ceqsexg a_wceq f0_ceqsexg a_wa f2_ceqsexg a_wex f0_ceqsexg f1_ceqsexg p_bibi12d f0_ceqsexg p_biid f0_ceqsexg f0_ceqsexg a_wb f2_ceqsexg a_sup_set_class f3_ceqsexg a_wceq f0_ceqsexg a_wa f2_ceqsexg a_wex f1_ceqsexg a_wb f2_ceqsexg f3_ceqsexg f4_ceqsexg p_vtoclgf $.
$}

$(Elimination of an existential quantifier, using implicit substitution.
       (Contributed by NM, 29-Dec-1996.) $)

${
	$v ph ps x A V  $.
	$d x A  $.
	$d x ps  $.
	f0_ceqsexgv $f wff ph $.
	f1_ceqsexgv $f wff ps $.
	f2_ceqsexgv $f set x $.
	f3_ceqsexgv $f class A $.
	f4_ceqsexgv $f class V $.
	e0_ceqsexgv $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_ceqsexgv $p |- ( A e. V -> ( E. x ( x = A /\ ph ) <-> ps ) ) $= f1_ceqsexgv f2_ceqsexgv p_nfv e0_ceqsexgv f0_ceqsexgv f1_ceqsexgv f2_ceqsexgv f3_ceqsexgv f4_ceqsexgv p_ceqsexg $.
$}

$(Elimination of a restricted existential quantifier, using implicit
       substitution.  (Contributed by NM, 30-Apr-2004.) $)

${
	$v ph ps x A B  $.
	$d x A  $.
	$d x B  $.
	$d x ps  $.
	f0_ceqsrexv $f wff ph $.
	f1_ceqsrexv $f wff ps $.
	f2_ceqsrexv $f set x $.
	f3_ceqsrexv $f class A $.
	f4_ceqsrexv $f class B $.
	e0_ceqsrexv $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_ceqsrexv $p |- ( A e. B -> ( E. x e. B ( x = A /\ ph ) <-> ps ) ) $= f2_ceqsrexv a_sup_set_class f3_ceqsrexv a_wceq f0_ceqsrexv a_wa f2_ceqsrexv f4_ceqsrexv a_df-rex f2_ceqsrexv a_sup_set_class f3_ceqsrexv a_wceq f2_ceqsrexv a_sup_set_class f4_ceqsrexv a_wcel f0_ceqsrexv p_an12 f2_ceqsrexv a_sup_set_class f3_ceqsrexv a_wceq f2_ceqsrexv a_sup_set_class f4_ceqsrexv a_wcel f0_ceqsrexv a_wa a_wa f2_ceqsrexv a_sup_set_class f4_ceqsrexv a_wcel f2_ceqsrexv a_sup_set_class f3_ceqsrexv a_wceq f0_ceqsrexv a_wa a_wa f2_ceqsrexv p_exbii f2_ceqsrexv a_sup_set_class f3_ceqsrexv a_wceq f0_ceqsrexv a_wa f2_ceqsrexv f4_ceqsrexv a_wrex f2_ceqsrexv a_sup_set_class f4_ceqsrexv a_wcel f2_ceqsrexv a_sup_set_class f3_ceqsrexv a_wceq f0_ceqsrexv a_wa a_wa f2_ceqsrexv a_wex f2_ceqsrexv a_sup_set_class f3_ceqsrexv a_wceq f2_ceqsrexv a_sup_set_class f4_ceqsrexv a_wcel f0_ceqsrexv a_wa a_wa f2_ceqsrexv a_wex p_bitr4i f2_ceqsrexv a_sup_set_class f3_ceqsrexv f4_ceqsrexv p_eleq1 e0_ceqsrexv f2_ceqsrexv a_sup_set_class f3_ceqsrexv a_wceq f2_ceqsrexv a_sup_set_class f4_ceqsrexv a_wcel f3_ceqsrexv f4_ceqsrexv a_wcel f0_ceqsrexv f1_ceqsrexv p_anbi12d f2_ceqsrexv a_sup_set_class f4_ceqsrexv a_wcel f0_ceqsrexv a_wa f3_ceqsrexv f4_ceqsrexv a_wcel f1_ceqsrexv a_wa f2_ceqsrexv f3_ceqsrexv f4_ceqsrexv p_ceqsexgv f3_ceqsrexv f4_ceqsrexv a_wcel f2_ceqsrexv a_sup_set_class f3_ceqsrexv a_wceq f2_ceqsrexv a_sup_set_class f4_ceqsrexv a_wcel f0_ceqsrexv a_wa a_wa f2_ceqsrexv a_wex f1_ceqsrexv p_bianabs f2_ceqsrexv a_sup_set_class f3_ceqsrexv a_wceq f0_ceqsrexv a_wa f2_ceqsrexv f4_ceqsrexv a_wrex f2_ceqsrexv a_sup_set_class f3_ceqsrexv a_wceq f2_ceqsrexv a_sup_set_class f4_ceqsrexv a_wcel f0_ceqsrexv a_wa a_wa f2_ceqsrexv a_wex f3_ceqsrexv f4_ceqsrexv a_wcel f1_ceqsrexv p_syl5bb $.
$}

$(Elimination of a restricted existential quantifier, using implicit
       substitution.  (Contributed by Mario Carneiro, 14-Mar-2014.) $)

${
	$v ph ps x A B  $.
	$d x A  $.
	$d x B  $.
	$d x ps  $.
	f0_ceqsrexbv $f wff ph $.
	f1_ceqsrexbv $f wff ps $.
	f2_ceqsrexbv $f set x $.
	f3_ceqsrexbv $f class A $.
	f4_ceqsrexbv $f class B $.
	e0_ceqsrexbv $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_ceqsrexbv $p |- ( E. x e. B ( x = A /\ ph ) <-> ( A e. B /\ ps ) ) $= f3_ceqsrexbv f4_ceqsrexbv a_wcel f2_ceqsrexbv a_sup_set_class f3_ceqsrexbv a_wceq f0_ceqsrexbv a_wa f2_ceqsrexbv f4_ceqsrexbv p_r19.42v f2_ceqsrexbv a_sup_set_class f3_ceqsrexbv f4_ceqsrexbv p_eleq1 f2_ceqsrexbv a_sup_set_class f3_ceqsrexbv a_wceq f2_ceqsrexbv a_sup_set_class f4_ceqsrexbv a_wcel f3_ceqsrexbv f4_ceqsrexbv a_wcel a_wb f0_ceqsrexbv p_adantr f2_ceqsrexbv a_sup_set_class f3_ceqsrexbv a_wceq f0_ceqsrexbv a_wa f2_ceqsrexbv a_sup_set_class f4_ceqsrexbv a_wcel f3_ceqsrexbv f4_ceqsrexbv a_wcel p_pm5.32ri f2_ceqsrexbv a_sup_set_class f4_ceqsrexbv a_wcel f2_ceqsrexbv a_sup_set_class f3_ceqsrexbv a_wceq f0_ceqsrexbv a_wa a_wa f3_ceqsrexbv f4_ceqsrexbv a_wcel f2_ceqsrexbv a_sup_set_class f3_ceqsrexbv a_wceq f0_ceqsrexbv a_wa a_wa p_bicomi f3_ceqsrexbv f4_ceqsrexbv a_wcel f2_ceqsrexbv a_sup_set_class f3_ceqsrexbv a_wceq f0_ceqsrexbv a_wa a_wa f2_ceqsrexbv a_sup_set_class f4_ceqsrexbv a_wcel f2_ceqsrexbv a_sup_set_class f3_ceqsrexbv a_wceq f0_ceqsrexbv a_wa p_baib f3_ceqsrexbv f4_ceqsrexbv a_wcel f2_ceqsrexbv a_sup_set_class f3_ceqsrexbv a_wceq f0_ceqsrexbv a_wa a_wa f2_ceqsrexbv a_sup_set_class f3_ceqsrexbv a_wceq f0_ceqsrexbv a_wa f2_ceqsrexbv f4_ceqsrexbv p_rexbiia e0_ceqsrexbv f0_ceqsrexbv f1_ceqsrexbv f2_ceqsrexbv f3_ceqsrexbv f4_ceqsrexbv p_ceqsrexv f3_ceqsrexbv f4_ceqsrexbv a_wcel f2_ceqsrexbv a_sup_set_class f3_ceqsrexbv a_wceq f0_ceqsrexbv a_wa f2_ceqsrexbv f4_ceqsrexbv a_wrex f1_ceqsrexbv p_pm5.32i f3_ceqsrexbv f4_ceqsrexbv a_wcel f2_ceqsrexbv a_sup_set_class f3_ceqsrexbv a_wceq f0_ceqsrexbv a_wa a_wa f2_ceqsrexbv f4_ceqsrexbv a_wrex f3_ceqsrexbv f4_ceqsrexbv a_wcel f2_ceqsrexbv a_sup_set_class f3_ceqsrexbv a_wceq f0_ceqsrexbv a_wa f2_ceqsrexbv f4_ceqsrexbv a_wrex a_wa f2_ceqsrexbv a_sup_set_class f3_ceqsrexbv a_wceq f0_ceqsrexbv a_wa f2_ceqsrexbv f4_ceqsrexbv a_wrex f3_ceqsrexbv f4_ceqsrexbv a_wcel f1_ceqsrexbv a_wa p_3bitr3i $.
$}

$(Elimination of a restricted existential quantifier, using implicit
       substitution.  (Contributed by NM, 29-Oct-2005.) $)

${
	$v ph ps ch x y A B C D  $.
	$d x y A  $.
	$d x y B  $.
	$d x C  $.
	$d x y D  $.
	$d x ps  $.
	$d y ch  $.
	f0_ceqsrex2v $f wff ph $.
	f1_ceqsrex2v $f wff ps $.
	f2_ceqsrex2v $f wff ch $.
	f3_ceqsrex2v $f set x $.
	f4_ceqsrex2v $f set y $.
	f5_ceqsrex2v $f class A $.
	f6_ceqsrex2v $f class B $.
	f7_ceqsrex2v $f class C $.
	f8_ceqsrex2v $f class D $.
	e0_ceqsrex2v $e |- ( x = A -> ( ph <-> ps ) ) $.
	e1_ceqsrex2v $e |- ( y = B -> ( ps <-> ch ) ) $.
	p_ceqsrex2v $p |- ( ( A e. C /\ B e. D ) -> ( E. x e. C E. y e. D ( ( x = A /\ y = B ) /\ ph ) <-> ch ) ) $= f3_ceqsrex2v a_sup_set_class f5_ceqsrex2v a_wceq f4_ceqsrex2v a_sup_set_class f6_ceqsrex2v a_wceq f0_ceqsrex2v p_anass f3_ceqsrex2v a_sup_set_class f5_ceqsrex2v a_wceq f4_ceqsrex2v a_sup_set_class f6_ceqsrex2v a_wceq a_wa f0_ceqsrex2v a_wa f3_ceqsrex2v a_sup_set_class f5_ceqsrex2v a_wceq f4_ceqsrex2v a_sup_set_class f6_ceqsrex2v a_wceq f0_ceqsrex2v a_wa a_wa f4_ceqsrex2v f8_ceqsrex2v p_rexbii f3_ceqsrex2v a_sup_set_class f5_ceqsrex2v a_wceq f4_ceqsrex2v a_sup_set_class f6_ceqsrex2v a_wceq f0_ceqsrex2v a_wa f4_ceqsrex2v f8_ceqsrex2v p_r19.42v f3_ceqsrex2v a_sup_set_class f5_ceqsrex2v a_wceq f4_ceqsrex2v a_sup_set_class f6_ceqsrex2v a_wceq a_wa f0_ceqsrex2v a_wa f4_ceqsrex2v f8_ceqsrex2v a_wrex f3_ceqsrex2v a_sup_set_class f5_ceqsrex2v a_wceq f4_ceqsrex2v a_sup_set_class f6_ceqsrex2v a_wceq f0_ceqsrex2v a_wa a_wa f4_ceqsrex2v f8_ceqsrex2v a_wrex f3_ceqsrex2v a_sup_set_class f5_ceqsrex2v a_wceq f4_ceqsrex2v a_sup_set_class f6_ceqsrex2v a_wceq f0_ceqsrex2v a_wa f4_ceqsrex2v f8_ceqsrex2v a_wrex a_wa p_bitri f3_ceqsrex2v a_sup_set_class f5_ceqsrex2v a_wceq f4_ceqsrex2v a_sup_set_class f6_ceqsrex2v a_wceq a_wa f0_ceqsrex2v a_wa f4_ceqsrex2v f8_ceqsrex2v a_wrex f3_ceqsrex2v a_sup_set_class f5_ceqsrex2v a_wceq f4_ceqsrex2v a_sup_set_class f6_ceqsrex2v a_wceq f0_ceqsrex2v a_wa f4_ceqsrex2v f8_ceqsrex2v a_wrex a_wa f3_ceqsrex2v f7_ceqsrex2v p_rexbii e0_ceqsrex2v f3_ceqsrex2v a_sup_set_class f5_ceqsrex2v a_wceq f0_ceqsrex2v f1_ceqsrex2v f4_ceqsrex2v a_sup_set_class f6_ceqsrex2v a_wceq p_anbi2d f3_ceqsrex2v a_sup_set_class f5_ceqsrex2v a_wceq f4_ceqsrex2v a_sup_set_class f6_ceqsrex2v a_wceq f0_ceqsrex2v a_wa f4_ceqsrex2v a_sup_set_class f6_ceqsrex2v a_wceq f1_ceqsrex2v a_wa f4_ceqsrex2v f8_ceqsrex2v p_rexbidv f4_ceqsrex2v a_sup_set_class f6_ceqsrex2v a_wceq f0_ceqsrex2v a_wa f4_ceqsrex2v f8_ceqsrex2v a_wrex f4_ceqsrex2v a_sup_set_class f6_ceqsrex2v a_wceq f1_ceqsrex2v a_wa f4_ceqsrex2v f8_ceqsrex2v a_wrex f3_ceqsrex2v f5_ceqsrex2v f7_ceqsrex2v p_ceqsrexv f3_ceqsrex2v a_sup_set_class f5_ceqsrex2v a_wceq f4_ceqsrex2v a_sup_set_class f6_ceqsrex2v a_wceq a_wa f0_ceqsrex2v a_wa f4_ceqsrex2v f8_ceqsrex2v a_wrex f3_ceqsrex2v f7_ceqsrex2v a_wrex f3_ceqsrex2v a_sup_set_class f5_ceqsrex2v a_wceq f4_ceqsrex2v a_sup_set_class f6_ceqsrex2v a_wceq f0_ceqsrex2v a_wa f4_ceqsrex2v f8_ceqsrex2v a_wrex a_wa f3_ceqsrex2v f7_ceqsrex2v a_wrex f5_ceqsrex2v f7_ceqsrex2v a_wcel f4_ceqsrex2v a_sup_set_class f6_ceqsrex2v a_wceq f1_ceqsrex2v a_wa f4_ceqsrex2v f8_ceqsrex2v a_wrex p_syl5bb e1_ceqsrex2v f1_ceqsrex2v f2_ceqsrex2v f4_ceqsrex2v f6_ceqsrex2v f8_ceqsrex2v p_ceqsrexv f5_ceqsrex2v f7_ceqsrex2v a_wcel f3_ceqsrex2v a_sup_set_class f5_ceqsrex2v a_wceq f4_ceqsrex2v a_sup_set_class f6_ceqsrex2v a_wceq a_wa f0_ceqsrex2v a_wa f4_ceqsrex2v f8_ceqsrex2v a_wrex f3_ceqsrex2v f7_ceqsrex2v a_wrex f4_ceqsrex2v a_sup_set_class f6_ceqsrex2v a_wceq f1_ceqsrex2v a_wa f4_ceqsrex2v f8_ceqsrex2v a_wrex f6_ceqsrex2v f8_ceqsrex2v a_wcel f2_ceqsrex2v p_sylan9bb $.
$}

$(An alternate definition of class membership when the class is a set.
       (Contributed by NM, 18-Aug-1993.) $)

${
	$v x A B  $.
	$d x A  $.
	$d x B  $.
	f0_clel2 $f set x $.
	f1_clel2 $f class A $.
	f2_clel2 $f class B $.
	e0_clel2 $e |- A e. _V $.
	p_clel2 $p |- ( A e. B <-> A. x ( x = A -> x e. B ) ) $= e0_clel2 f0_clel2 a_sup_set_class f1_clel2 f2_clel2 p_eleq1 f0_clel2 a_sup_set_class f2_clel2 a_wcel f1_clel2 f2_clel2 a_wcel f0_clel2 f1_clel2 p_ceqsalv f0_clel2 a_sup_set_class f1_clel2 a_wceq f0_clel2 a_sup_set_class f2_clel2 a_wcel a_wi f0_clel2 a_wal f1_clel2 f2_clel2 a_wcel p_bicomi $.
$}

$(An alternate definition of class membership when the class is a set.
       (Contributed by NM, 13-Aug-2005.) $)

${
	$v x A B V  $.
	$d x A  $.
	$d x B  $.
	f0_clel3g $f set x $.
	f1_clel3g $f class A $.
	f2_clel3g $f class B $.
	f3_clel3g $f class V $.
	p_clel3g $p |- ( B e. V -> ( A e. B <-> E. x ( x = B /\ A e. x ) ) ) $= f0_clel3g a_sup_set_class f2_clel3g f1_clel3g p_eleq2 f1_clel3g f0_clel3g a_sup_set_class a_wcel f1_clel3g f2_clel3g a_wcel f0_clel3g f2_clel3g f3_clel3g p_ceqsexgv f2_clel3g f3_clel3g a_wcel f0_clel3g a_sup_set_class f2_clel3g a_wceq f1_clel3g f0_clel3g a_sup_set_class a_wcel a_wa f0_clel3g a_wex f1_clel3g f2_clel3g a_wcel p_bicomd $.
$}

$(An alternate definition of class membership when the class is a set.
       (Contributed by NM, 18-Aug-1993.) $)

${
	$v x A B  $.
	$d x A  $.
	$d x B  $.
	f0_clel3 $f set x $.
	f1_clel3 $f class A $.
	f2_clel3 $f class B $.
	e0_clel3 $e |- B e. _V $.
	p_clel3 $p |- ( A e. B <-> E. x ( x = B /\ A e. x ) ) $= e0_clel3 f0_clel3 f1_clel3 f2_clel3 a_cvv p_clel3g f2_clel3 a_cvv a_wcel f1_clel3 f2_clel3 a_wcel f0_clel3 a_sup_set_class f2_clel3 a_wceq f1_clel3 f0_clel3 a_sup_set_class a_wcel a_wa f0_clel3 a_wex a_wb a_ax-mp $.
$}

$(An alternate definition of class membership when the class is a set.
       (Contributed by NM, 18-Aug-1993.) $)

${
	$v x A B  $.
	$d x A  $.
	$d x B  $.
	f0_clel4 $f set x $.
	f1_clel4 $f class A $.
	f2_clel4 $f class B $.
	e0_clel4 $e |- B e. _V $.
	p_clel4 $p |- ( A e. B <-> A. x ( x = B -> A e. x ) ) $= e0_clel4 f0_clel4 a_sup_set_class f2_clel4 f1_clel4 p_eleq2 f1_clel4 f0_clel4 a_sup_set_class a_wcel f1_clel4 f2_clel4 a_wcel f0_clel4 f2_clel4 p_ceqsalv f0_clel4 a_sup_set_class f2_clel4 a_wceq f1_clel4 f0_clel4 a_sup_set_class a_wcel a_wi f0_clel4 a_wal f1_clel4 f2_clel4 a_wcel p_bicomi $.
$}

$(Compare theorem *13.183 in [WhiteheadRussell] p. 178.  Only ` A ` is
       required to be a set.  (Contributed by Andrew Salmon, 3-Jun-2011.) $)

${
	$v z A B V  $.
	$d y A z  $.
	$d y B z  $.
	f0_pm13.183 $f set z $.
	f1_pm13.183 $f class A $.
	f2_pm13.183 $f class B $.
	f3_pm13.183 $f class V $.
	i0_pm13.183 $f set y $.
	p_pm13.183 $p |- ( A e. V -> ( A = B <-> A. z ( z = A <-> z = B ) ) ) $= i0_pm13.183 a_sup_set_class f1_pm13.183 f2_pm13.183 p_eqeq1 i0_pm13.183 a_sup_set_class f1_pm13.183 f0_pm13.183 a_sup_set_class p_eqeq2 i0_pm13.183 a_sup_set_class f1_pm13.183 a_wceq f0_pm13.183 a_sup_set_class i0_pm13.183 a_sup_set_class a_wceq f0_pm13.183 a_sup_set_class f1_pm13.183 a_wceq f0_pm13.183 a_sup_set_class f2_pm13.183 a_wceq p_bibi1d i0_pm13.183 a_sup_set_class f1_pm13.183 a_wceq f0_pm13.183 a_sup_set_class i0_pm13.183 a_sup_set_class a_wceq f0_pm13.183 a_sup_set_class f2_pm13.183 a_wceq a_wb f0_pm13.183 a_sup_set_class f1_pm13.183 a_wceq f0_pm13.183 a_sup_set_class f2_pm13.183 a_wceq a_wb f0_pm13.183 p_albidv i0_pm13.183 a_sup_set_class f2_pm13.183 f0_pm13.183 a_sup_set_class p_eqeq2 i0_pm13.183 a_sup_set_class f2_pm13.183 a_wceq f0_pm13.183 a_sup_set_class i0_pm13.183 a_sup_set_class a_wceq f0_pm13.183 a_sup_set_class f2_pm13.183 a_wceq a_wb f0_pm13.183 p_alrimiv f0_pm13.183 a_sup_set_class i0_pm13.183 a_sup_set_class a_wceq f0_pm13.183 a_sup_set_class f2_pm13.183 a_wceq a_wb f0_pm13.183 i0_pm13.183 p_stdpc4 f0_pm13.183 a_sup_set_class i0_pm13.183 a_sup_set_class a_wceq f0_pm13.183 a_sup_set_class f2_pm13.183 a_wceq f0_pm13.183 i0_pm13.183 p_sbbi i0_pm13.183 f0_pm13.183 f2_pm13.183 p_eqsb3 f0_pm13.183 a_sup_set_class f2_pm13.183 a_wceq f0_pm13.183 i0_pm13.183 a_wsb i0_pm13.183 a_sup_set_class f2_pm13.183 a_wceq f0_pm13.183 a_sup_set_class i0_pm13.183 a_sup_set_class a_wceq f0_pm13.183 i0_pm13.183 a_wsb p_bibi2i f0_pm13.183 i0_pm13.183 p_equsb1 f0_pm13.183 a_sup_set_class i0_pm13.183 a_sup_set_class a_wceq f0_pm13.183 i0_pm13.183 a_wsb i0_pm13.183 a_sup_set_class f2_pm13.183 a_wceq p_bi1 f0_pm13.183 a_sup_set_class i0_pm13.183 a_sup_set_class a_wceq f0_pm13.183 i0_pm13.183 a_wsb i0_pm13.183 a_sup_set_class f2_pm13.183 a_wceq a_wb f0_pm13.183 a_sup_set_class i0_pm13.183 a_sup_set_class a_wceq f0_pm13.183 i0_pm13.183 a_wsb i0_pm13.183 a_sup_set_class f2_pm13.183 a_wceq p_mpi f0_pm13.183 a_sup_set_class i0_pm13.183 a_sup_set_class a_wceq f0_pm13.183 i0_pm13.183 a_wsb f0_pm13.183 a_sup_set_class f2_pm13.183 a_wceq f0_pm13.183 i0_pm13.183 a_wsb a_wb f0_pm13.183 a_sup_set_class i0_pm13.183 a_sup_set_class a_wceq f0_pm13.183 i0_pm13.183 a_wsb i0_pm13.183 a_sup_set_class f2_pm13.183 a_wceq a_wb i0_pm13.183 a_sup_set_class f2_pm13.183 a_wceq p_sylbi f0_pm13.183 a_sup_set_class i0_pm13.183 a_sup_set_class a_wceq f0_pm13.183 a_sup_set_class f2_pm13.183 a_wceq a_wb f0_pm13.183 i0_pm13.183 a_wsb f0_pm13.183 a_sup_set_class i0_pm13.183 a_sup_set_class a_wceq f0_pm13.183 i0_pm13.183 a_wsb f0_pm13.183 a_sup_set_class f2_pm13.183 a_wceq f0_pm13.183 i0_pm13.183 a_wsb a_wb i0_pm13.183 a_sup_set_class f2_pm13.183 a_wceq p_sylbi f0_pm13.183 a_sup_set_class i0_pm13.183 a_sup_set_class a_wceq f0_pm13.183 a_sup_set_class f2_pm13.183 a_wceq a_wb f0_pm13.183 a_wal f0_pm13.183 a_sup_set_class i0_pm13.183 a_sup_set_class a_wceq f0_pm13.183 a_sup_set_class f2_pm13.183 a_wceq a_wb f0_pm13.183 i0_pm13.183 a_wsb i0_pm13.183 a_sup_set_class f2_pm13.183 a_wceq p_syl i0_pm13.183 a_sup_set_class f2_pm13.183 a_wceq f0_pm13.183 a_sup_set_class i0_pm13.183 a_sup_set_class a_wceq f0_pm13.183 a_sup_set_class f2_pm13.183 a_wceq a_wb f0_pm13.183 a_wal p_impbii i0_pm13.183 a_sup_set_class f2_pm13.183 a_wceq f0_pm13.183 a_sup_set_class i0_pm13.183 a_sup_set_class a_wceq f0_pm13.183 a_sup_set_class f2_pm13.183 a_wceq a_wb f0_pm13.183 a_wal f1_pm13.183 f2_pm13.183 a_wceq f0_pm13.183 a_sup_set_class f1_pm13.183 a_wceq f0_pm13.183 a_sup_set_class f2_pm13.183 a_wceq a_wb f0_pm13.183 a_wal i0_pm13.183 f1_pm13.183 f3_pm13.183 p_vtoclbg $.
$}

$(Restricted quantifier version of Theorem 19.3 of [Margaris] p. 89.  We
       don't need the non-empty class condition of ~ r19.3rzv when there is an
       outer quantifier.  (Contributed by NM, 25-Oct-2012.) $)

${
	$v ph x y A  $.
	$d y A  $.
	$d x y  $.
	$d y ph  $.
	f0_rr19.3v $f wff ph $.
	f1_rr19.3v $f set x $.
	f2_rr19.3v $f set y $.
	f3_rr19.3v $f class A $.
	p_rr19.3v $p |- ( A. x e. A A. y e. A ph <-> A. x e. A ph ) $= f2_rr19.3v a_sup_set_class f1_rr19.3v a_sup_set_class a_wceq f0_rr19.3v p_biidd f0_rr19.3v f0_rr19.3v f2_rr19.3v f1_rr19.3v a_sup_set_class f3_rr19.3v p_rspcv f0_rr19.3v f2_rr19.3v f3_rr19.3v a_wral f0_rr19.3v f1_rr19.3v f3_rr19.3v p_ralimia f0_rr19.3v f2_rr19.3v a_sup_set_class f3_rr19.3v a_wcel a_ax-1 f0_rr19.3v f0_rr19.3v f2_rr19.3v f3_rr19.3v p_ralrimiv f0_rr19.3v f0_rr19.3v f2_rr19.3v f3_rr19.3v a_wral f1_rr19.3v f3_rr19.3v p_ralimi f0_rr19.3v f2_rr19.3v f3_rr19.3v a_wral f1_rr19.3v f3_rr19.3v a_wral f0_rr19.3v f1_rr19.3v f3_rr19.3v a_wral p_impbii $.
$}

$(Restricted quantifier version of Theorem 19.28 of [Margaris] p. 90.  We
       don't need the non-empty class condition of ~ r19.28zv when there is an
       outer quantifier.  (Contributed by NM, 29-Oct-2012.) $)

${
	$v ph ps x y A  $.
	$d y A  $.
	$d x y  $.
	$d y ph  $.
	f0_rr19.28v $f wff ph $.
	f1_rr19.28v $f wff ps $.
	f2_rr19.28v $f set x $.
	f3_rr19.28v $f set y $.
	f4_rr19.28v $f class A $.
	p_rr19.28v $p |- ( A. x e. A A. y e. A ( ph /\ ps ) <-> A. x e. A ( ph /\ A. y e. A ps ) ) $= f0_rr19.28v f1_rr19.28v p_simpl f0_rr19.28v f1_rr19.28v a_wa f0_rr19.28v f3_rr19.28v f4_rr19.28v p_ralimi f3_rr19.28v a_sup_set_class f2_rr19.28v a_sup_set_class a_wceq f0_rr19.28v p_biidd f0_rr19.28v f0_rr19.28v f3_rr19.28v f2_rr19.28v a_sup_set_class f4_rr19.28v p_rspcv f0_rr19.28v f1_rr19.28v a_wa f3_rr19.28v f4_rr19.28v a_wral f0_rr19.28v f3_rr19.28v f4_rr19.28v a_wral f2_rr19.28v a_sup_set_class f4_rr19.28v a_wcel f0_rr19.28v p_syl5 f0_rr19.28v f1_rr19.28v p_simpr f0_rr19.28v f1_rr19.28v a_wa f1_rr19.28v f3_rr19.28v f4_rr19.28v p_ralimi f0_rr19.28v f1_rr19.28v a_wa f3_rr19.28v f4_rr19.28v a_wral f1_rr19.28v f3_rr19.28v f4_rr19.28v a_wral a_wi f2_rr19.28v a_sup_set_class f4_rr19.28v a_wcel p_a1i f2_rr19.28v a_sup_set_class f4_rr19.28v a_wcel f0_rr19.28v f1_rr19.28v a_wa f3_rr19.28v f4_rr19.28v a_wral f0_rr19.28v f1_rr19.28v f3_rr19.28v f4_rr19.28v a_wral p_jcad f0_rr19.28v f1_rr19.28v a_wa f3_rr19.28v f4_rr19.28v a_wral f0_rr19.28v f1_rr19.28v f3_rr19.28v f4_rr19.28v a_wral a_wa f2_rr19.28v f4_rr19.28v p_ralimia f0_rr19.28v f1_rr19.28v f3_rr19.28v f4_rr19.28v p_r19.28av f0_rr19.28v f1_rr19.28v f3_rr19.28v f4_rr19.28v a_wral a_wa f0_rr19.28v f1_rr19.28v a_wa f3_rr19.28v f4_rr19.28v a_wral f2_rr19.28v f4_rr19.28v p_ralimi f0_rr19.28v f1_rr19.28v a_wa f3_rr19.28v f4_rr19.28v a_wral f2_rr19.28v f4_rr19.28v a_wral f0_rr19.28v f1_rr19.28v f3_rr19.28v f4_rr19.28v a_wral a_wa f2_rr19.28v f4_rr19.28v a_wral p_impbii $.
$}

$(Membership in a class abstraction, using implicit substitution.  (Closed
       theorem version of ~ elabg .)  (Contributed by NM, 7-Nov-2005.)  (Proof
       shortened by Andrew Salmon, 8-Jun-2011.) $)

${
	$v ph ps x A B  $.
	$d x A  $.
	$d ph  $.
	$d x ps  $.
	f0_elabgt $f wff ph $.
	f1_elabgt $f wff ps $.
	f2_elabgt $f set x $.
	f3_elabgt $f class A $.
	f4_elabgt $f class B $.
	p_elabgt $p |- ( ( A e. B /\ A. x ( x = A -> ( ph <-> ps ) ) ) -> ( A e. { x | ph } <-> ps ) ) $= f0_elabgt f2_elabgt p_abid f2_elabgt a_sup_set_class f3_elabgt f0_elabgt f2_elabgt a_cab p_eleq1 f0_elabgt f2_elabgt a_sup_set_class f0_elabgt f2_elabgt a_cab a_wcel f2_elabgt a_sup_set_class f3_elabgt a_wceq f3_elabgt f0_elabgt f2_elabgt a_cab a_wcel p_syl5bbr f2_elabgt a_sup_set_class f3_elabgt a_wceq f0_elabgt f3_elabgt f0_elabgt f2_elabgt a_cab a_wcel f1_elabgt p_bibi1d f2_elabgt a_sup_set_class f3_elabgt a_wceq f0_elabgt f1_elabgt a_wb f3_elabgt f0_elabgt f2_elabgt a_cab a_wcel f1_elabgt a_wb p_biimpd f2_elabgt a_sup_set_class f3_elabgt a_wceq f0_elabgt f1_elabgt a_wb f3_elabgt f0_elabgt f2_elabgt a_cab a_wcel f1_elabgt a_wb p_a2i f2_elabgt a_sup_set_class f3_elabgt a_wceq f0_elabgt f1_elabgt a_wb a_wi f2_elabgt a_sup_set_class f3_elabgt a_wceq f3_elabgt f0_elabgt f2_elabgt a_cab a_wcel f1_elabgt a_wb a_wi f2_elabgt p_alimi f2_elabgt f3_elabgt p_nfcv f0_elabgt f2_elabgt p_nfab1 f2_elabgt f3_elabgt f0_elabgt f2_elabgt a_cab p_nfel2 f1_elabgt f2_elabgt p_nfv f3_elabgt f0_elabgt f2_elabgt a_cab a_wcel f1_elabgt f2_elabgt p_nfbi f2_elabgt a_sup_set_class f3_elabgt a_wceq f3_elabgt f0_elabgt f2_elabgt a_cab a_wcel f1_elabgt a_wb p_pm5.5 f2_elabgt a_sup_set_class f3_elabgt a_wceq f3_elabgt f0_elabgt f2_elabgt a_cab a_wcel f1_elabgt a_wb a_wi f3_elabgt f0_elabgt f2_elabgt a_cab a_wcel f1_elabgt a_wb f2_elabgt f3_elabgt f4_elabgt p_spcgf f3_elabgt f4_elabgt a_wcel f2_elabgt a_sup_set_class f3_elabgt a_wceq f3_elabgt f0_elabgt f2_elabgt a_cab a_wcel f1_elabgt a_wb a_wi f2_elabgt a_wal f3_elabgt f0_elabgt f2_elabgt a_cab a_wcel f1_elabgt a_wb p_imp f2_elabgt a_sup_set_class f3_elabgt a_wceq f0_elabgt f1_elabgt a_wb a_wi f2_elabgt a_wal f3_elabgt f4_elabgt a_wcel f2_elabgt a_sup_set_class f3_elabgt a_wceq f3_elabgt f0_elabgt f2_elabgt a_cab a_wcel f1_elabgt a_wb a_wi f2_elabgt a_wal f3_elabgt f0_elabgt f2_elabgt a_cab a_wcel f1_elabgt a_wb p_sylan2 $.
$}

$(Membership in a class abstraction, using implicit substitution.  Compare
       Theorem 6.13 of [Quine] p. 44.  This version has bound-variable
       hypotheses in place of distinct variable restrictions.  (Contributed by
       NM, 21-Sep-2003.)  (Revised by Mario Carneiro, 12-Oct-2016.) $)

${
	$v ph ps x A B  $.
	f0_elabgf $f wff ph $.
	f1_elabgf $f wff ps $.
	f2_elabgf $f set x $.
	f3_elabgf $f class A $.
	f4_elabgf $f class B $.
	e0_elabgf $e |- F/_ x A $.
	e1_elabgf $e |- F/ x ps $.
	e2_elabgf $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_elabgf $p |- ( A e. B -> ( A e. { x | ph } <-> ps ) ) $= e0_elabgf e0_elabgf f0_elabgf f2_elabgf p_nfab1 f2_elabgf f3_elabgf f0_elabgf f2_elabgf a_cab p_nfel e1_elabgf f3_elabgf f0_elabgf f2_elabgf a_cab a_wcel f1_elabgf f2_elabgf p_nfbi f2_elabgf a_sup_set_class f3_elabgf f0_elabgf f2_elabgf a_cab p_eleq1 e2_elabgf f2_elabgf a_sup_set_class f3_elabgf a_wceq f2_elabgf a_sup_set_class f0_elabgf f2_elabgf a_cab a_wcel f3_elabgf f0_elabgf f2_elabgf a_cab a_wcel f0_elabgf f1_elabgf p_bibi12d f0_elabgf f2_elabgf p_abid f2_elabgf a_sup_set_class f0_elabgf f2_elabgf a_cab a_wcel f0_elabgf a_wb f3_elabgf f0_elabgf f2_elabgf a_cab a_wcel f1_elabgf a_wb f2_elabgf f3_elabgf f4_elabgf p_vtoclgf $.
$}

$(Membership in a class abstraction, using implicit substitution.
       (Contributed by NM, 1-Aug-1994.)  (Revised by Mario Carneiro,
       12-Oct-2016.) $)

${
	$v ph ps x A  $.
	$d ps  $.
	$d x A  $.
	$d ph  $.
	f0_elabf $f wff ph $.
	f1_elabf $f wff ps $.
	f2_elabf $f set x $.
	f3_elabf $f class A $.
	e0_elabf $e |- F/ x ps $.
	e1_elabf $e |- A e. _V $.
	e2_elabf $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_elabf $p |- ( A e. { x | ph } <-> ps ) $= e1_elabf f2_elabf f3_elabf p_nfcv e0_elabf e2_elabf f0_elabf f1_elabf f2_elabf f3_elabf a_cvv p_elabgf f3_elabf a_cvv a_wcel f3_elabf f0_elabf f2_elabf a_cab a_wcel f1_elabf a_wb a_ax-mp $.
$}

$(Membership in a class abstraction, using implicit substitution.  Compare
       Theorem 6.13 of [Quine] p. 44.  (Contributed by NM, 1-Aug-1994.) $)

${
	$v ph ps x A  $.
	$d x ps  $.
	$d x A  $.
	f0_elab $f wff ph $.
	f1_elab $f wff ps $.
	f2_elab $f set x $.
	f3_elab $f class A $.
	e0_elab $e |- A e. _V $.
	e1_elab $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_elab $p |- ( A e. { x | ph } <-> ps ) $= f1_elab f2_elab p_nfv e0_elab e1_elab f0_elab f1_elab f2_elab f3_elab p_elabf $.
$}

$(Membership in a class abstraction, using implicit substitution.  Compare
       Theorem 6.13 of [Quine] p. 44.  (Contributed by NM, 14-Apr-1995.) $)

${
	$v ph ps x A V  $.
	$d x ps  $.
	$d x A  $.
	f0_elabg $f wff ph $.
	f1_elabg $f wff ps $.
	f2_elabg $f set x $.
	f3_elabg $f class A $.
	f4_elabg $f class V $.
	e0_elabg $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_elabg $p |- ( A e. V -> ( A e. { x | ph } <-> ps ) ) $= f2_elabg f3_elabg p_nfcv f1_elabg f2_elabg p_nfv e0_elabg f0_elabg f1_elabg f2_elabg f3_elabg f4_elabg p_elabgf $.
$}

$(Membership in a class abstraction, using implicit substitution.
       (Contributed by NM, 13-Sep-1995.) $)

${
	$v ph ps x A B V  $.
	$d x ps  $.
	$d x A  $.
	f0_elab2g $f wff ph $.
	f1_elab2g $f wff ps $.
	f2_elab2g $f set x $.
	f3_elab2g $f class A $.
	f4_elab2g $f class B $.
	f5_elab2g $f class V $.
	e0_elab2g $e |- ( x = A -> ( ph <-> ps ) ) $.
	e1_elab2g $e |- B = { x | ph } $.
	p_elab2g $p |- ( A e. V -> ( A e. B <-> ps ) ) $= e1_elab2g f4_elab2g f0_elab2g f2_elab2g a_cab f3_elab2g p_eleq2i e0_elab2g f0_elab2g f1_elab2g f2_elab2g f3_elab2g f5_elab2g p_elabg f3_elab2g f4_elab2g a_wcel f3_elab2g f0_elab2g f2_elab2g a_cab a_wcel f3_elab2g f5_elab2g a_wcel f1_elab2g p_syl5bb $.
$}

$(Membership in a class abstraction, using implicit substitution.
       (Contributed by NM, 13-Sep-1995.) $)

${
	$v ph ps x A B  $.
	$d x ps  $.
	$d x A  $.
	f0_elab2 $f wff ph $.
	f1_elab2 $f wff ps $.
	f2_elab2 $f set x $.
	f3_elab2 $f class A $.
	f4_elab2 $f class B $.
	e0_elab2 $e |- A e. _V $.
	e1_elab2 $e |- ( x = A -> ( ph <-> ps ) ) $.
	e2_elab2 $e |- B = { x | ph } $.
	p_elab2 $p |- ( A e. B <-> ps ) $= e0_elab2 e1_elab2 e2_elab2 f0_elab2 f1_elab2 f2_elab2 f3_elab2 f4_elab2 a_cvv p_elab2g f3_elab2 a_cvv a_wcel f3_elab2 f4_elab2 a_wcel f1_elab2 a_wb a_ax-mp $.
$}

$(Membership in a class abstraction, using implicit substitution.
       (Contributed by NM, 17-Oct-2012.) $)

${
	$v ph ps x A B  $.
	$d x ps  $.
	$d x A  $.
	f0_elab4g $f wff ph $.
	f1_elab4g $f wff ps $.
	f2_elab4g $f set x $.
	f3_elab4g $f class A $.
	f4_elab4g $f class B $.
	e0_elab4g $e |- ( x = A -> ( ph <-> ps ) ) $.
	e1_elab4g $e |- B = { x | ph } $.
	p_elab4g $p |- ( A e. B <-> ( A e. _V /\ ps ) ) $= f3_elab4g f4_elab4g p_elex e0_elab4g e1_elab4g f0_elab4g f1_elab4g f2_elab4g f3_elab4g f4_elab4g a_cvv p_elab2g f3_elab4g f4_elab4g a_wcel f3_elab4g a_cvv a_wcel f1_elab4g p_biadan2 $.
$}

$(Membership in a class abstraction, with a weaker antecedent than
       ~ elabgf .  (Contributed by NM, 6-Sep-2011.) $)

${
	$v ph ps x A B  $.
	$d A  $.
	f0_elab3gf $f wff ph $.
	f1_elab3gf $f wff ps $.
	f2_elab3gf $f set x $.
	f3_elab3gf $f class A $.
	f4_elab3gf $f class B $.
	e0_elab3gf $e |- F/_ x A $.
	e1_elab3gf $e |- F/ x ps $.
	e2_elab3gf $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_elab3gf $p |- ( ( ps -> A e. B ) -> ( A e. { x | ph } <-> ps ) ) $= e0_elab3gf e1_elab3gf e2_elab3gf f0_elab3gf f1_elab3gf f2_elab3gf f3_elab3gf f0_elab3gf f2_elab3gf a_cab p_elabgf f3_elab3gf f0_elab3gf f2_elab3gf a_cab a_wcel f1_elab3gf p_ibi f1_elab3gf f3_elab3gf f0_elab3gf f2_elab3gf a_cab a_wcel p_pm2.21 f1_elab3gf a_wn f3_elab3gf f0_elab3gf f2_elab3gf a_cab a_wcel f1_elab3gf p_impbid2 e0_elab3gf e1_elab3gf e2_elab3gf f0_elab3gf f1_elab3gf f2_elab3gf f3_elab3gf f4_elab3gf p_elabgf f1_elab3gf f3_elab3gf f4_elab3gf a_wcel f3_elab3gf f0_elab3gf f2_elab3gf a_cab a_wcel f1_elab3gf a_wb p_ja $.
$}

$(Membership in a class abstraction, with a weaker antecedent than
       ~ elabg .  (Contributed by NM, 29-Aug-2006.) $)

${
	$v ph ps x A B  $.
	$d x ps  $.
	$d x A  $.
	f0_elab3g $f wff ph $.
	f1_elab3g $f wff ps $.
	f2_elab3g $f set x $.
	f3_elab3g $f class A $.
	f4_elab3g $f class B $.
	e0_elab3g $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_elab3g $p |- ( ( ps -> A e. B ) -> ( A e. { x | ph } <-> ps ) ) $= f2_elab3g f3_elab3g p_nfcv f1_elab3g f2_elab3g p_nfv e0_elab3g f0_elab3g f1_elab3g f2_elab3g f3_elab3g f4_elab3g p_elab3gf $.
$}

$(Membership in a class abstraction using implicit substitution.
       (Contributed by NM, 10-Nov-2000.) $)

${
	$v ph ps x A  $.
	$d x ps  $.
	$d x A  $.
	f0_elab3 $f wff ph $.
	f1_elab3 $f wff ps $.
	f2_elab3 $f set x $.
	f3_elab3 $f class A $.
	e0_elab3 $e |- ( ps -> A e. _V ) $.
	e1_elab3 $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_elab3 $p |- ( A e. { x | ph } <-> ps ) $= e0_elab3 e1_elab3 f0_elab3 f1_elab3 f2_elab3 f3_elab3 a_cvv p_elab3g f1_elab3 f3_elab3 a_cvv a_wcel a_wi f3_elab3 f0_elab3 f2_elab3 a_cab a_wcel f1_elab3 a_wb a_ax-mp $.
$}

$(Membership in a restricted class abstraction, using implicit
       substitution.  This version has bound-variable hypotheses in place of
       distinct variable restrictions.  (Contributed by NM, 21-Sep-2003.) $)

${
	$v ph ps x A B  $.
	f0_elrabf $f wff ph $.
	f1_elrabf $f wff ps $.
	f2_elrabf $f set x $.
	f3_elrabf $f class A $.
	f4_elrabf $f class B $.
	e0_elrabf $e |- F/_ x A $.
	e1_elrabf $e |- F/_ x B $.
	e2_elrabf $e |- F/ x ps $.
	e3_elrabf $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_elrabf $p |- ( A e. { x e. B | ph } <-> ( A e. B /\ ps ) ) $= f3_elrabf f0_elrabf f2_elrabf f4_elrabf a_crab p_elex f3_elrabf f4_elrabf p_elex f3_elrabf f4_elrabf a_wcel f3_elrabf a_cvv a_wcel f1_elrabf p_adantr f0_elrabf f2_elrabf f4_elrabf a_df-rab f0_elrabf f2_elrabf f4_elrabf a_crab f2_elrabf a_sup_set_class f4_elrabf a_wcel f0_elrabf a_wa f2_elrabf a_cab f3_elrabf p_eleq2i e0_elrabf e0_elrabf e1_elrabf f2_elrabf f3_elrabf f4_elrabf p_nfel e2_elrabf f3_elrabf f4_elrabf a_wcel f1_elrabf f2_elrabf p_nfan f2_elrabf a_sup_set_class f3_elrabf f4_elrabf p_eleq1 e3_elrabf f2_elrabf a_sup_set_class f3_elrabf a_wceq f2_elrabf a_sup_set_class f4_elrabf a_wcel f3_elrabf f4_elrabf a_wcel f0_elrabf f1_elrabf p_anbi12d f2_elrabf a_sup_set_class f4_elrabf a_wcel f0_elrabf a_wa f3_elrabf f4_elrabf a_wcel f1_elrabf a_wa f2_elrabf f3_elrabf a_cvv p_elabgf f3_elrabf f0_elrabf f2_elrabf f4_elrabf a_crab a_wcel f3_elrabf f2_elrabf a_sup_set_class f4_elrabf a_wcel f0_elrabf a_wa f2_elrabf a_cab a_wcel f3_elrabf a_cvv a_wcel f3_elrabf f4_elrabf a_wcel f1_elrabf a_wa p_syl5bb f3_elrabf f0_elrabf f2_elrabf f4_elrabf a_crab a_wcel f3_elrabf a_cvv a_wcel f3_elrabf f4_elrabf a_wcel f1_elrabf a_wa p_pm5.21nii $.
$}

$(Membership in a restricted class abstraction, using implicit
       substitution.  (Contributed by NM, 21-May-1999.) $)

${
	$v ph ps x A B  $.
	$d x ps  $.
	$d x A  $.
	$d x B  $.
	f0_elrab $f wff ph $.
	f1_elrab $f wff ps $.
	f2_elrab $f set x $.
	f3_elrab $f class A $.
	f4_elrab $f class B $.
	e0_elrab $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_elrab $p |- ( A e. { x e. B | ph } <-> ( A e. B /\ ps ) ) $= f2_elrab f3_elrab p_nfcv f2_elrab f4_elrab p_nfcv f1_elrab f2_elrab p_nfv e0_elrab f0_elrab f1_elrab f2_elrab f3_elrab f4_elrab p_elrabf $.
$}

$(Membership in a restricted class abstraction, using implicit
       substitution.  (Contributed by NM, 5-Oct-2006.) $)

${
	$v ph ps x A B  $.
	$d x ps  $.
	$d x A  $.
	$d x B  $.
	f0_elrab3 $f wff ph $.
	f1_elrab3 $f wff ps $.
	f2_elrab3 $f set x $.
	f3_elrab3 $f class A $.
	f4_elrab3 $f class B $.
	e0_elrab3 $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_elrab3 $p |- ( A e. B -> ( A e. { x e. B | ph } <-> ps ) ) $= e0_elrab3 f0_elrab3 f1_elrab3 f2_elrab3 f3_elrab3 f4_elrab3 p_elrab f3_elrab3 f0_elrab3 f2_elrab3 f4_elrab3 a_crab a_wcel f3_elrab3 f4_elrab3 a_wcel f1_elrab3 p_baib $.
$}

$(Membership in a class abstraction, using implicit substitution.
       (Contributed by NM, 2-Nov-2006.) $)

${
	$v ph ps x A B C  $.
	$d x ps  $.
	$d x A  $.
	$d x B  $.
	f0_elrab2 $f wff ph $.
	f1_elrab2 $f wff ps $.
	f2_elrab2 $f set x $.
	f3_elrab2 $f class A $.
	f4_elrab2 $f class B $.
	f5_elrab2 $f class C $.
	e0_elrab2 $e |- ( x = A -> ( ph <-> ps ) ) $.
	e1_elrab2 $e |- C = { x e. B | ph } $.
	p_elrab2 $p |- ( A e. C <-> ( A e. B /\ ps ) ) $= e1_elrab2 f5_elrab2 f0_elrab2 f2_elrab2 f4_elrab2 a_crab f3_elrab2 p_eleq2i e0_elrab2 f0_elrab2 f1_elrab2 f2_elrab2 f3_elrab2 f4_elrab2 p_elrab f3_elrab2 f5_elrab2 a_wcel f3_elrab2 f0_elrab2 f2_elrab2 f4_elrab2 a_crab a_wcel f3_elrab2 f4_elrab2 a_wcel f1_elrab2 a_wa p_bitri $.
$}

$(Universal quantification over a class abstraction.  (Contributed by Jeff
       Madsen, 10-Jun-2010.) $)

${
	$v ph ps ch x y  $.
	$d x y  $.
	$d y  $.
	$d y ps  $.
	f0_ralab $f wff ph $.
	f1_ralab $f wff ps $.
	f2_ralab $f wff ch $.
	f3_ralab $f set x $.
	f4_ralab $f set y $.
	e0_ralab $e |- ( y = x -> ( ph <-> ps ) ) $.
	p_ralab $p |- ( A. x e. { y | ph } ch <-> A. x ( ps -> ch ) ) $= f2_ralab f3_ralab f0_ralab f4_ralab a_cab a_df-ral f3_ralab p_vex e0_ralab f0_ralab f1_ralab f4_ralab f3_ralab a_sup_set_class p_elab f3_ralab a_sup_set_class f0_ralab f4_ralab a_cab a_wcel f1_ralab f2_ralab p_imbi1i f3_ralab a_sup_set_class f0_ralab f4_ralab a_cab a_wcel f2_ralab a_wi f1_ralab f2_ralab a_wi f3_ralab p_albii f2_ralab f3_ralab f0_ralab f4_ralab a_cab a_wral f3_ralab a_sup_set_class f0_ralab f4_ralab a_cab a_wcel f2_ralab a_wi f3_ralab a_wal f1_ralab f2_ralab a_wi f3_ralab a_wal p_bitri $.
$}

$(Universal quantification over a restricted class abstraction.
       (Contributed by Jeff Madsen, 10-Jun-2010.) $)

${
	$v ph ps ch x y A  $.
	$d x y  $.
	$d y A  $.
	$d y ps  $.
	f0_ralrab $f wff ph $.
	f1_ralrab $f wff ps $.
	f2_ralrab $f wff ch $.
	f3_ralrab $f set x $.
	f4_ralrab $f set y $.
	f5_ralrab $f class A $.
	e0_ralrab $e |- ( y = x -> ( ph <-> ps ) ) $.
	p_ralrab $p |- ( A. x e. { y e. A | ph } ch <-> A. x e. A ( ps -> ch ) ) $= e0_ralrab f0_ralrab f1_ralrab f4_ralrab f3_ralrab a_sup_set_class f5_ralrab p_elrab f3_ralrab a_sup_set_class f0_ralrab f4_ralrab f5_ralrab a_crab a_wcel f3_ralrab a_sup_set_class f5_ralrab a_wcel f1_ralrab a_wa f2_ralrab p_imbi1i f3_ralrab a_sup_set_class f5_ralrab a_wcel f1_ralrab f2_ralrab p_impexp f3_ralrab a_sup_set_class f0_ralrab f4_ralrab f5_ralrab a_crab a_wcel f2_ralrab a_wi f3_ralrab a_sup_set_class f5_ralrab a_wcel f1_ralrab a_wa f2_ralrab a_wi f3_ralrab a_sup_set_class f5_ralrab a_wcel f1_ralrab f2_ralrab a_wi a_wi p_bitri f2_ralrab f1_ralrab f2_ralrab a_wi f3_ralrab f0_ralrab f4_ralrab f5_ralrab a_crab f5_ralrab p_ralbii2 $.
$}

$(Existential quantification over a class abstraction.  (Contributed by
       Mario Carneiro, 23-Jan-2014.)  (Revised by Mario Carneiro,
       3-Sep-2015.) $)

${
	$v ph ps ch x y  $.
	$d x y  $.
	$d y  $.
	$d y ps  $.
	f0_rexab $f wff ph $.
	f1_rexab $f wff ps $.
	f2_rexab $f wff ch $.
	f3_rexab $f set x $.
	f4_rexab $f set y $.
	e0_rexab $e |- ( y = x -> ( ph <-> ps ) ) $.
	p_rexab $p |- ( E. x e. { y | ph } ch <-> E. x ( ps /\ ch ) ) $= f2_rexab f3_rexab f0_rexab f4_rexab a_cab a_df-rex f3_rexab p_vex e0_rexab f0_rexab f1_rexab f4_rexab f3_rexab a_sup_set_class p_elab f3_rexab a_sup_set_class f0_rexab f4_rexab a_cab a_wcel f1_rexab f2_rexab p_anbi1i f3_rexab a_sup_set_class f0_rexab f4_rexab a_cab a_wcel f2_rexab a_wa f1_rexab f2_rexab a_wa f3_rexab p_exbii f2_rexab f3_rexab f0_rexab f4_rexab a_cab a_wrex f3_rexab a_sup_set_class f0_rexab f4_rexab a_cab a_wcel f2_rexab a_wa f3_rexab a_wex f1_rexab f2_rexab a_wa f3_rexab a_wex p_bitri $.
$}

$(Existential quantification over a class abstraction.  (Contributed by
       Jeff Madsen, 17-Jun-2011.)  (Revised by Mario Carneiro, 3-Sep-2015.) $)

${
	$v ph ps ch x y A  $.
	$d x y  $.
	$d y A  $.
	$d y ps  $.
	f0_rexrab $f wff ph $.
	f1_rexrab $f wff ps $.
	f2_rexrab $f wff ch $.
	f3_rexrab $f set x $.
	f4_rexrab $f set y $.
	f5_rexrab $f class A $.
	e0_rexrab $e |- ( y = x -> ( ph <-> ps ) ) $.
	p_rexrab $p |- ( E. x e. { y e. A | ph } ch <-> E. x e. A ( ps /\ ch ) ) $= e0_rexrab f0_rexrab f1_rexrab f4_rexrab f3_rexrab a_sup_set_class f5_rexrab p_elrab f3_rexrab a_sup_set_class f0_rexrab f4_rexrab f5_rexrab a_crab a_wcel f3_rexrab a_sup_set_class f5_rexrab a_wcel f1_rexrab a_wa f2_rexrab p_anbi1i f3_rexrab a_sup_set_class f5_rexrab a_wcel f1_rexrab f2_rexrab p_anass f3_rexrab a_sup_set_class f0_rexrab f4_rexrab f5_rexrab a_crab a_wcel f2_rexrab a_wa f3_rexrab a_sup_set_class f5_rexrab a_wcel f1_rexrab a_wa f2_rexrab a_wa f3_rexrab a_sup_set_class f5_rexrab a_wcel f1_rexrab f2_rexrab a_wa a_wa p_bitri f2_rexrab f1_rexrab f2_rexrab a_wa f3_rexrab f0_rexrab f4_rexrab f5_rexrab a_crab f5_rexrab p_rexbii2 $.
$}

$(Universal quantification over a class abstraction.  (Contributed by
       Mario Carneiro, 3-Sep-2015.) $)

${
	$v ph ps ch x y  $.
	$d x y  $.
	$d x  $.
	$d x ch  $.
	$d x ph  $.
	$d y ps  $.
	f0_ralab2 $f wff ph $.
	f1_ralab2 $f wff ps $.
	f2_ralab2 $f wff ch $.
	f3_ralab2 $f set x $.
	f4_ralab2 $f set y $.
	e0_ralab2 $e |- ( x = y -> ( ps <-> ch ) ) $.
	p_ralab2 $p |- ( A. x e. { y | ph } ps <-> A. y ( ph -> ch ) ) $= f1_ralab2 f3_ralab2 f0_ralab2 f4_ralab2 a_cab a_df-ral f0_ralab2 f4_ralab2 f3_ralab2 p_nfsab1 f1_ralab2 f4_ralab2 p_nfv f3_ralab2 a_sup_set_class f0_ralab2 f4_ralab2 a_cab a_wcel f1_ralab2 f4_ralab2 p_nfim f0_ralab2 f2_ralab2 a_wi f3_ralab2 p_nfv f3_ralab2 a_sup_set_class f4_ralab2 a_sup_set_class f0_ralab2 f4_ralab2 a_cab p_eleq1 f0_ralab2 f4_ralab2 p_abid f3_ralab2 a_sup_set_class f4_ralab2 a_sup_set_class a_wceq f3_ralab2 a_sup_set_class f0_ralab2 f4_ralab2 a_cab a_wcel f4_ralab2 a_sup_set_class f0_ralab2 f4_ralab2 a_cab a_wcel f0_ralab2 p_syl6bb e0_ralab2 f3_ralab2 a_sup_set_class f4_ralab2 a_sup_set_class a_wceq f3_ralab2 a_sup_set_class f0_ralab2 f4_ralab2 a_cab a_wcel f0_ralab2 f1_ralab2 f2_ralab2 p_imbi12d f3_ralab2 a_sup_set_class f0_ralab2 f4_ralab2 a_cab a_wcel f1_ralab2 a_wi f0_ralab2 f2_ralab2 a_wi f3_ralab2 f4_ralab2 p_cbval f1_ralab2 f3_ralab2 f0_ralab2 f4_ralab2 a_cab a_wral f3_ralab2 a_sup_set_class f0_ralab2 f4_ralab2 a_cab a_wcel f1_ralab2 a_wi f3_ralab2 a_wal f0_ralab2 f2_ralab2 a_wi f4_ralab2 a_wal p_bitri $.
$}

$(Universal quantification over a restricted class abstraction.
       (Contributed by Mario Carneiro, 3-Sep-2015.) $)

${
	$v ph ps ch x y A  $.
	$d x y  $.
	$d x A  $.
	$d x ch  $.
	$d x ph  $.
	$d y ps  $.
	f0_ralrab2 $f wff ph $.
	f1_ralrab2 $f wff ps $.
	f2_ralrab2 $f wff ch $.
	f3_ralrab2 $f set x $.
	f4_ralrab2 $f set y $.
	f5_ralrab2 $f class A $.
	e0_ralrab2 $e |- ( x = y -> ( ps <-> ch ) ) $.
	p_ralrab2 $p |- ( A. x e. { y e. A | ph } ps <-> A. y e. A ( ph -> ch ) ) $= f0_ralrab2 f4_ralrab2 f5_ralrab2 a_df-rab f1_ralrab2 f3_ralrab2 f0_ralrab2 f4_ralrab2 f5_ralrab2 a_crab f4_ralrab2 a_sup_set_class f5_ralrab2 a_wcel f0_ralrab2 a_wa f4_ralrab2 a_cab p_raleqi e0_ralrab2 f4_ralrab2 a_sup_set_class f5_ralrab2 a_wcel f0_ralrab2 a_wa f1_ralrab2 f2_ralrab2 f3_ralrab2 f4_ralrab2 p_ralab2 f4_ralrab2 a_sup_set_class f5_ralrab2 a_wcel f0_ralrab2 f2_ralrab2 p_impexp f4_ralrab2 a_sup_set_class f5_ralrab2 a_wcel f0_ralrab2 a_wa f2_ralrab2 a_wi f4_ralrab2 a_sup_set_class f5_ralrab2 a_wcel f0_ralrab2 f2_ralrab2 a_wi a_wi f4_ralrab2 p_albii f0_ralrab2 f2_ralrab2 a_wi f4_ralrab2 f5_ralrab2 a_df-ral f4_ralrab2 a_sup_set_class f5_ralrab2 a_wcel f0_ralrab2 a_wa f2_ralrab2 a_wi f4_ralrab2 a_wal f4_ralrab2 a_sup_set_class f5_ralrab2 a_wcel f0_ralrab2 f2_ralrab2 a_wi a_wi f4_ralrab2 a_wal f0_ralrab2 f2_ralrab2 a_wi f4_ralrab2 f5_ralrab2 a_wral p_bitr4i f1_ralrab2 f3_ralrab2 f0_ralrab2 f4_ralrab2 f5_ralrab2 a_crab a_wral f1_ralrab2 f3_ralrab2 f4_ralrab2 a_sup_set_class f5_ralrab2 a_wcel f0_ralrab2 a_wa f4_ralrab2 a_cab a_wral f4_ralrab2 a_sup_set_class f5_ralrab2 a_wcel f0_ralrab2 a_wa f2_ralrab2 a_wi f4_ralrab2 a_wal f0_ralrab2 f2_ralrab2 a_wi f4_ralrab2 f5_ralrab2 a_wral p_3bitri $.
$}

$(Existential quantification over a class abstraction.  (Contributed by
       Mario Carneiro, 3-Sep-2015.) $)

${
	$v ph ps ch x y  $.
	$d x y  $.
	$d x  $.
	$d x ch  $.
	$d x ph  $.
	$d y ps  $.
	f0_rexab2 $f wff ph $.
	f1_rexab2 $f wff ps $.
	f2_rexab2 $f wff ch $.
	f3_rexab2 $f set x $.
	f4_rexab2 $f set y $.
	e0_rexab2 $e |- ( x = y -> ( ps <-> ch ) ) $.
	p_rexab2 $p |- ( E. x e. { y | ph } ps <-> E. y ( ph /\ ch ) ) $= f1_rexab2 f3_rexab2 f0_rexab2 f4_rexab2 a_cab a_df-rex f0_rexab2 f4_rexab2 f3_rexab2 p_nfsab1 f1_rexab2 f4_rexab2 p_nfv f3_rexab2 a_sup_set_class f0_rexab2 f4_rexab2 a_cab a_wcel f1_rexab2 f4_rexab2 p_nfan f0_rexab2 f2_rexab2 a_wa f3_rexab2 p_nfv f3_rexab2 a_sup_set_class f4_rexab2 a_sup_set_class f0_rexab2 f4_rexab2 a_cab p_eleq1 f0_rexab2 f4_rexab2 p_abid f3_rexab2 a_sup_set_class f4_rexab2 a_sup_set_class a_wceq f3_rexab2 a_sup_set_class f0_rexab2 f4_rexab2 a_cab a_wcel f4_rexab2 a_sup_set_class f0_rexab2 f4_rexab2 a_cab a_wcel f0_rexab2 p_syl6bb e0_rexab2 f3_rexab2 a_sup_set_class f4_rexab2 a_sup_set_class a_wceq f3_rexab2 a_sup_set_class f0_rexab2 f4_rexab2 a_cab a_wcel f0_rexab2 f1_rexab2 f2_rexab2 p_anbi12d f3_rexab2 a_sup_set_class f0_rexab2 f4_rexab2 a_cab a_wcel f1_rexab2 a_wa f0_rexab2 f2_rexab2 a_wa f3_rexab2 f4_rexab2 p_cbvex f1_rexab2 f3_rexab2 f0_rexab2 f4_rexab2 a_cab a_wrex f3_rexab2 a_sup_set_class f0_rexab2 f4_rexab2 a_cab a_wcel f1_rexab2 a_wa f3_rexab2 a_wex f0_rexab2 f2_rexab2 a_wa f4_rexab2 a_wex p_bitri $.
$}

$(Existential quantification over a class abstraction.  (Contributed by
       Mario Carneiro, 3-Sep-2015.) $)

${
	$v ph ps ch x y A  $.
	$d x y  $.
	$d x A  $.
	$d x ch  $.
	$d x ph  $.
	$d y ps  $.
	f0_rexrab2 $f wff ph $.
	f1_rexrab2 $f wff ps $.
	f2_rexrab2 $f wff ch $.
	f3_rexrab2 $f set x $.
	f4_rexrab2 $f set y $.
	f5_rexrab2 $f class A $.
	e0_rexrab2 $e |- ( x = y -> ( ps <-> ch ) ) $.
	p_rexrab2 $p |- ( E. x e. { y e. A | ph } ps <-> E. y e. A ( ph /\ ch ) ) $= f0_rexrab2 f4_rexrab2 f5_rexrab2 a_df-rab f1_rexrab2 f3_rexrab2 f0_rexrab2 f4_rexrab2 f5_rexrab2 a_crab f4_rexrab2 a_sup_set_class f5_rexrab2 a_wcel f0_rexrab2 a_wa f4_rexrab2 a_cab p_rexeqi e0_rexrab2 f4_rexrab2 a_sup_set_class f5_rexrab2 a_wcel f0_rexrab2 a_wa f1_rexrab2 f2_rexrab2 f3_rexrab2 f4_rexrab2 p_rexab2 f4_rexrab2 a_sup_set_class f5_rexrab2 a_wcel f0_rexrab2 f2_rexrab2 p_anass f4_rexrab2 a_sup_set_class f5_rexrab2 a_wcel f0_rexrab2 a_wa f2_rexrab2 a_wa f4_rexrab2 a_sup_set_class f5_rexrab2 a_wcel f0_rexrab2 f2_rexrab2 a_wa a_wa f4_rexrab2 p_exbii f0_rexrab2 f2_rexrab2 a_wa f4_rexrab2 f5_rexrab2 a_df-rex f4_rexrab2 a_sup_set_class f5_rexrab2 a_wcel f0_rexrab2 a_wa f2_rexrab2 a_wa f4_rexrab2 a_wex f4_rexrab2 a_sup_set_class f5_rexrab2 a_wcel f0_rexrab2 f2_rexrab2 a_wa a_wa f4_rexrab2 a_wex f0_rexrab2 f2_rexrab2 a_wa f4_rexrab2 f5_rexrab2 a_wrex p_bitr4i f1_rexrab2 f3_rexrab2 f0_rexrab2 f4_rexrab2 f5_rexrab2 a_crab a_wrex f1_rexrab2 f3_rexrab2 f4_rexrab2 a_sup_set_class f5_rexrab2 a_wcel f0_rexrab2 a_wa f4_rexrab2 a_cab a_wrex f4_rexrab2 a_sup_set_class f5_rexrab2 a_wcel f0_rexrab2 a_wa f2_rexrab2 a_wa f4_rexrab2 a_wex f0_rexrab2 f2_rexrab2 a_wa f4_rexrab2 f5_rexrab2 a_wrex p_3bitri $.
$}

$(Identity used to create closed-form versions of bound-variable
       hypothesis builders for class expressions.  (Contributed by NM,
       10-Nov-2005.)  (Proof shortened by Mario Carneiro, 12-Oct-2016.) $)

${
	$v x z A  $.
	$d A  $.
	$d x z  $.
	$d x  $.
	$d A z  $.
	f0_abidnf $f set x $.
	f1_abidnf $f set z $.
	f2_abidnf $f class A $.
	p_abidnf $p |- ( F/_ x A -> { z | A. x z e. A } = A ) $= f1_abidnf a_sup_set_class f2_abidnf a_wcel f0_abidnf p_sp f0_abidnf f1_abidnf f2_abidnf p_nfcr f0_abidnf f2_abidnf a_wnfc f1_abidnf a_sup_set_class f2_abidnf a_wcel f0_abidnf p_nfrd f0_abidnf f2_abidnf a_wnfc f1_abidnf a_sup_set_class f2_abidnf a_wcel f0_abidnf a_wal f1_abidnf a_sup_set_class f2_abidnf a_wcel p_impbid2 f0_abidnf f2_abidnf a_wnfc f1_abidnf a_sup_set_class f2_abidnf a_wcel f0_abidnf a_wal f1_abidnf f2_abidnf p_abbi1dv $.
$}

$(A deduction theorem for converting the inference ` |- F/_ x A ` =>
       ` |- ph ` into a closed theorem.  Use ~ nfa1 and ~ nfab to eliminate the
       hypothesis of the substitution instance ` ps ` of the inference.  For
       converting the inference form into a deduction form, ~ abidnf is
       useful.  (Contributed by NM, 8-Dec-2006.) $)

${
	$v ph ps x z A  $.
	$d A  $.
	$d x z  $.
	$d x  $.
	$d z A  $.
	f0_dedhb $f wff ph $.
	f1_dedhb $f wff ps $.
	f2_dedhb $f set x $.
	f3_dedhb $f set z $.
	f4_dedhb $f class A $.
	e0_dedhb $e |- ( A = { z | A. x z e. A } -> ( ph <-> ps ) ) $.
	e1_dedhb $e |- ps $.
	p_dedhb $p |- ( F/_ x A -> ph ) $= e1_dedhb f2_dedhb f3_dedhb f4_dedhb p_abidnf f2_dedhb f4_dedhb a_wnfc f3_dedhb a_sup_set_class f4_dedhb a_wcel f2_dedhb a_wal f3_dedhb a_cab f4_dedhb p_eqcomd e0_dedhb f2_dedhb f4_dedhb a_wnfc f4_dedhb f3_dedhb a_sup_set_class f4_dedhb a_wcel f2_dedhb a_wal f3_dedhb a_cab a_wceq f0_dedhb f1_dedhb a_wb p_syl f2_dedhb f4_dedhb a_wnfc f0_dedhb f1_dedhb p_mpbiri $.
$}

$(A condition which implies existential uniqueness.  (Contributed by Jeff
       Hankins, 8-Sep-2009.) $)

${
	$v ph ps x A B  $.
	$d y ph  $.
	$d x y ps  $.
	$d x y A  $.
	f0_eqeu $f wff ph $.
	f1_eqeu $f wff ps $.
	f2_eqeu $f set x $.
	f3_eqeu $f class A $.
	f4_eqeu $f class B $.
	i0_eqeu $f set y $.
	e0_eqeu $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_eqeu $p |- ( ( A e. B /\ ps /\ A. x ( ph -> x = A ) ) -> E! x ph ) $= e0_eqeu f0_eqeu f1_eqeu f2_eqeu f3_eqeu f4_eqeu p_spcegv f3_eqeu f4_eqeu a_wcel f1_eqeu f0_eqeu f2_eqeu a_wex p_imp f3_eqeu f4_eqeu a_wcel f1_eqeu f0_eqeu f2_eqeu a_wex f0_eqeu f2_eqeu a_sup_set_class f3_eqeu a_wceq a_wi f2_eqeu a_wal p_3adant3 i0_eqeu a_sup_set_class f3_eqeu f2_eqeu a_sup_set_class p_eqeq2 i0_eqeu a_sup_set_class f3_eqeu a_wceq f2_eqeu a_sup_set_class i0_eqeu a_sup_set_class a_wceq f2_eqeu a_sup_set_class f3_eqeu a_wceq f0_eqeu p_imbi2d i0_eqeu a_sup_set_class f3_eqeu a_wceq f0_eqeu f2_eqeu a_sup_set_class i0_eqeu a_sup_set_class a_wceq a_wi f0_eqeu f2_eqeu a_sup_set_class f3_eqeu a_wceq a_wi f2_eqeu p_albidv f0_eqeu f2_eqeu a_sup_set_class i0_eqeu a_sup_set_class a_wceq a_wi f2_eqeu a_wal f0_eqeu f2_eqeu a_sup_set_class f3_eqeu a_wceq a_wi f2_eqeu a_wal i0_eqeu f3_eqeu f4_eqeu p_spcegv f3_eqeu f4_eqeu a_wcel f0_eqeu f2_eqeu a_sup_set_class f3_eqeu a_wceq a_wi f2_eqeu a_wal f0_eqeu f2_eqeu a_sup_set_class i0_eqeu a_sup_set_class a_wceq a_wi f2_eqeu a_wal i0_eqeu a_wex p_imp f3_eqeu f4_eqeu a_wcel f0_eqeu f2_eqeu a_sup_set_class f3_eqeu a_wceq a_wi f2_eqeu a_wal f0_eqeu f2_eqeu a_sup_set_class i0_eqeu a_sup_set_class a_wceq a_wi f2_eqeu a_wal i0_eqeu a_wex f1_eqeu p_3adant2 f0_eqeu i0_eqeu p_nfv f0_eqeu f2_eqeu i0_eqeu p_eu3 f3_eqeu f4_eqeu a_wcel f1_eqeu f0_eqeu f2_eqeu a_sup_set_class f3_eqeu a_wceq a_wi f2_eqeu a_wal a_w3a f0_eqeu f2_eqeu a_wex f0_eqeu f2_eqeu a_sup_set_class i0_eqeu a_sup_set_class a_wceq a_wi f2_eqeu a_wal i0_eqeu a_wex f0_eqeu f2_eqeu a_weu p_sylanbrc $.
$}

$(Equality has existential uniqueness.  (Contributed by NM,
       25-Nov-1994.) $)

${
	$v x A  $.
	$d x y A  $.
	f0_eueq $f set x $.
	f1_eueq $f class A $.
	i0_eueq $f set y $.
	p_eueq $p |- ( A e. _V <-> E! x x = A ) $= f0_eueq a_sup_set_class i0_eueq a_sup_set_class f1_eueq p_eqtr3 f0_eueq a_sup_set_class f1_eueq a_wceq i0_eueq a_sup_set_class f1_eueq a_wceq a_wa f0_eueq a_sup_set_class i0_eueq a_sup_set_class a_wceq a_wi f0_eueq i0_eueq p_gen2 f0_eueq a_sup_set_class f1_eueq a_wceq i0_eueq a_sup_set_class f1_eueq a_wceq a_wa f0_eueq a_sup_set_class i0_eueq a_sup_set_class a_wceq a_wi i0_eueq a_wal f0_eueq a_wal f0_eueq a_sup_set_class f1_eueq a_wceq f0_eueq a_wex p_biantru f0_eueq f1_eueq p_isset f0_eueq a_sup_set_class i0_eueq a_sup_set_class f1_eueq p_eqeq1 f0_eueq a_sup_set_class f1_eueq a_wceq i0_eueq a_sup_set_class f1_eueq a_wceq f0_eueq i0_eueq p_eu4 f0_eueq a_sup_set_class f1_eueq a_wceq f0_eueq a_wex f0_eueq a_sup_set_class f1_eueq a_wceq f0_eueq a_wex f0_eueq a_sup_set_class f1_eueq a_wceq i0_eueq a_sup_set_class f1_eueq a_wceq a_wa f0_eueq a_sup_set_class i0_eueq a_sup_set_class a_wceq a_wi i0_eueq a_wal f0_eueq a_wal a_wa f1_eueq a_cvv a_wcel f0_eueq a_sup_set_class f1_eueq a_wceq f0_eueq a_weu p_3bitr4i $.
$}

$(Equality has existential uniqueness.  (Contributed by NM,
       5-Apr-1995.) $)

${
	$v x A  $.
	$d x A  $.
	f0_eueq1 $f set x $.
	f1_eueq1 $f class A $.
	e0_eueq1 $e |- A e. _V $.
	p_eueq1 $p |- E! x x = A $= e0_eueq1 f0_eueq1 f1_eueq1 p_eueq f1_eueq1 a_cvv a_wcel f0_eueq1 a_sup_set_class f1_eueq1 a_wceq f0_eueq1 a_weu p_mpbi $.
$}

$(Equality has existential uniqueness (split into 2 cases).  (Contributed
       by NM, 5-Apr-1995.) $)

${
	$v ph x A B  $.
	$d x ph  $.
	$d x A  $.
	$d x B  $.
	f0_eueq2 $f wff ph $.
	f1_eueq2 $f set x $.
	f2_eueq2 $f class A $.
	f3_eueq2 $f class B $.
	e0_eueq2 $e |- A e. _V $.
	e1_eueq2 $e |- B e. _V $.
	p_eueq2 $p |- E! x ( ( ph /\ x = A ) \/ ( -. ph /\ x = B ) ) $= f0_eueq2 p_notnot1 e0_eueq2 f1_eueq2 f2_eueq2 p_eueq1 f0_eueq2 f1_eueq2 a_sup_set_class f2_eueq2 a_wceq f1_eueq2 p_euanv f0_eueq2 f1_eueq2 a_sup_set_class f2_eueq2 a_wceq a_wa f1_eueq2 a_weu f0_eueq2 f1_eueq2 a_sup_set_class f2_eueq2 a_wceq f1_eueq2 a_weu a_wa p_biimpri f0_eueq2 f1_eueq2 a_sup_set_class f2_eueq2 a_wceq f1_eueq2 a_weu f0_eueq2 f1_eueq2 a_sup_set_class f2_eueq2 a_wceq a_wa f1_eueq2 a_weu p_mpan2 f0_eueq2 a_wn f0_eueq2 f1_eueq2 a_sup_set_class f2_eueq2 a_wceq a_wa f1_eueq2 p_euorv f0_eueq2 f0_eueq2 a_wn a_wn f0_eueq2 f1_eueq2 a_sup_set_class f2_eueq2 a_wceq a_wa f1_eueq2 a_weu f0_eueq2 a_wn f0_eueq2 f1_eueq2 a_sup_set_class f2_eueq2 a_wceq a_wa a_wo f1_eueq2 a_weu p_syl2anc f0_eueq2 a_wn f0_eueq2 f1_eueq2 a_sup_set_class f2_eueq2 a_wceq a_wa p_orcom f0_eueq2 p_notnot1 f0_eueq2 f0_eueq2 a_wn f1_eueq2 a_sup_set_class f3_eueq2 a_wceq p_bianfd f0_eueq2 f0_eueq2 a_wn f0_eueq2 a_wn f1_eueq2 a_sup_set_class f3_eueq2 a_wceq a_wa f0_eueq2 f1_eueq2 a_sup_set_class f2_eueq2 a_wceq a_wa p_orbi2d f0_eueq2 a_wn f0_eueq2 f1_eueq2 a_sup_set_class f2_eueq2 a_wceq a_wa a_wo f0_eueq2 f1_eueq2 a_sup_set_class f2_eueq2 a_wceq a_wa f0_eueq2 a_wn a_wo f0_eueq2 f0_eueq2 f1_eueq2 a_sup_set_class f2_eueq2 a_wceq a_wa f0_eueq2 a_wn f1_eueq2 a_sup_set_class f3_eueq2 a_wceq a_wa a_wo p_syl5bb f0_eueq2 f0_eueq2 a_wn f0_eueq2 f1_eueq2 a_sup_set_class f2_eueq2 a_wceq a_wa a_wo f0_eueq2 f1_eueq2 a_sup_set_class f2_eueq2 a_wceq a_wa f0_eueq2 a_wn f1_eueq2 a_sup_set_class f3_eueq2 a_wceq a_wa a_wo f1_eueq2 p_eubidv f0_eueq2 f0_eueq2 a_wn f0_eueq2 f1_eueq2 a_sup_set_class f2_eueq2 a_wceq a_wa a_wo f1_eueq2 a_weu f0_eueq2 f1_eueq2 a_sup_set_class f2_eueq2 a_wceq a_wa f0_eueq2 a_wn f1_eueq2 a_sup_set_class f3_eueq2 a_wceq a_wa a_wo f1_eueq2 a_weu p_mpbid e1_eueq2 f1_eueq2 f3_eueq2 p_eueq1 f0_eueq2 a_wn f1_eueq2 a_sup_set_class f3_eueq2 a_wceq f1_eueq2 p_euanv f0_eueq2 a_wn f1_eueq2 a_sup_set_class f3_eueq2 a_wceq a_wa f1_eueq2 a_weu f0_eueq2 a_wn f1_eueq2 a_sup_set_class f3_eueq2 a_wceq f1_eueq2 a_weu a_wa p_biimpri f0_eueq2 a_wn f1_eueq2 a_sup_set_class f3_eueq2 a_wceq f1_eueq2 a_weu f0_eueq2 a_wn f1_eueq2 a_sup_set_class f3_eueq2 a_wceq a_wa f1_eueq2 a_weu p_mpan2 f0_eueq2 f0_eueq2 a_wn f1_eueq2 a_sup_set_class f3_eueq2 a_wceq a_wa f1_eueq2 p_euorv f0_eueq2 a_wn f0_eueq2 a_wn f1_eueq2 a_sup_set_class f3_eueq2 a_wceq a_wa f1_eueq2 a_weu f0_eueq2 f0_eueq2 a_wn f1_eueq2 a_sup_set_class f3_eueq2 a_wceq a_wa a_wo f1_eueq2 a_weu p_mpdan f0_eueq2 a_wn p_id f0_eueq2 a_wn f0_eueq2 f1_eueq2 a_sup_set_class f2_eueq2 a_wceq p_bianfd f0_eueq2 a_wn f0_eueq2 f0_eueq2 f1_eueq2 a_sup_set_class f2_eueq2 a_wceq a_wa f0_eueq2 a_wn f1_eueq2 a_sup_set_class f3_eueq2 a_wceq a_wa p_orbi1d f0_eueq2 a_wn f0_eueq2 f0_eueq2 a_wn f1_eueq2 a_sup_set_class f3_eueq2 a_wceq a_wa a_wo f0_eueq2 f1_eueq2 a_sup_set_class f2_eueq2 a_wceq a_wa f0_eueq2 a_wn f1_eueq2 a_sup_set_class f3_eueq2 a_wceq a_wa a_wo f1_eueq2 p_eubidv f0_eueq2 a_wn f0_eueq2 f0_eueq2 a_wn f1_eueq2 a_sup_set_class f3_eueq2 a_wceq a_wa a_wo f1_eueq2 a_weu f0_eueq2 f1_eueq2 a_sup_set_class f2_eueq2 a_wceq a_wa f0_eueq2 a_wn f1_eueq2 a_sup_set_class f3_eueq2 a_wceq a_wa a_wo f1_eueq2 a_weu p_mpbid f0_eueq2 f0_eueq2 f1_eueq2 a_sup_set_class f2_eueq2 a_wceq a_wa f0_eueq2 a_wn f1_eueq2 a_sup_set_class f3_eueq2 a_wceq a_wa a_wo f1_eueq2 a_weu p_pm2.61i $.
$}

$(Equality has existential uniqueness (split into 3 cases).  (Contributed
       by NM, 5-Apr-1995.)  (Proof shortened by Mario Carneiro,
       28-Sep-2015.) $)

${
	$v ph ps x A B C  $.
	$d x ph  $.
	$d x ps  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	f0_eueq3 $f wff ph $.
	f1_eueq3 $f wff ps $.
	f2_eueq3 $f set x $.
	f3_eueq3 $f class A $.
	f4_eueq3 $f class B $.
	f5_eueq3 $f class C $.
	e0_eueq3 $e |- A e. _V $.
	e1_eueq3 $e |- B e. _V $.
	e2_eueq3 $e |- C e. _V $.
	e3_eueq3 $e |- -. ( ph /\ ps ) $.
	p_eueq3 $p |- E! x ( ( ph /\ x = A ) \/ ( -. ( ph \/ ps ) /\ x = B ) \/ ( ps /\ x = C ) ) $= e0_eueq3 f2_eueq3 f3_eueq3 p_eueq1 f0_eueq3 f2_eueq3 a_sup_set_class f3_eueq3 a_wceq p_ibar f0_eueq3 f1_eueq3 p_pm2.45 e3_eueq3 f0_eueq3 f1_eueq3 p_imnani f0_eueq3 f1_eueq3 p_con2i f0_eueq3 f1_eueq3 a_wo a_wn f0_eueq3 a_wn f1_eueq3 p_jaoi f0_eueq3 f1_eueq3 a_wo a_wn f1_eueq3 a_wo f0_eueq3 p_con2i f0_eueq3 f1_eueq3 p_pm2.45 f0_eueq3 f1_eueq3 a_wo a_wn f0_eueq3 p_con2i f0_eueq3 f0_eueq3 f1_eueq3 a_wo a_wn f2_eueq3 a_sup_set_class f4_eueq3 a_wceq p_bianfd e3_eueq3 f0_eueq3 f1_eueq3 p_imnani f0_eueq3 f1_eueq3 f2_eueq3 a_sup_set_class f5_eueq3 a_wceq p_bianfd f0_eueq3 f0_eueq3 f1_eueq3 a_wo a_wn f0_eueq3 f1_eueq3 a_wo a_wn f2_eueq3 a_sup_set_class f4_eueq3 a_wceq a_wa f1_eueq3 f1_eueq3 f2_eueq3 a_sup_set_class f5_eueq3 a_wceq a_wa p_orbi12d f0_eueq3 f0_eueq3 f1_eueq3 a_wo a_wn f1_eueq3 a_wo f0_eueq3 f1_eueq3 a_wo a_wn f2_eueq3 a_sup_set_class f4_eueq3 a_wceq a_wa f1_eueq3 f2_eueq3 a_sup_set_class f5_eueq3 a_wceq a_wa a_wo p_mtbid f0_eueq3 f1_eueq3 a_wo a_wn f2_eueq3 a_sup_set_class f4_eueq3 a_wceq a_wa f1_eueq3 f2_eueq3 a_sup_set_class f5_eueq3 a_wceq a_wa a_wo f0_eueq3 f2_eueq3 a_sup_set_class f3_eueq3 a_wceq a_wa p_biorf f0_eueq3 f0_eueq3 f1_eueq3 a_wo a_wn f2_eueq3 a_sup_set_class f4_eueq3 a_wceq a_wa f1_eueq3 f2_eueq3 a_sup_set_class f5_eueq3 a_wceq a_wa a_wo a_wn f0_eueq3 f2_eueq3 a_sup_set_class f3_eueq3 a_wceq a_wa f0_eueq3 f1_eueq3 a_wo a_wn f2_eueq3 a_sup_set_class f4_eueq3 a_wceq a_wa f1_eueq3 f2_eueq3 a_sup_set_class f5_eueq3 a_wceq a_wa a_wo f0_eueq3 f2_eueq3 a_sup_set_class f3_eueq3 a_wceq a_wa a_wo a_wb p_syl f0_eueq3 f2_eueq3 a_sup_set_class f3_eueq3 a_wceq f0_eueq3 f2_eueq3 a_sup_set_class f3_eueq3 a_wceq a_wa f0_eueq3 f1_eueq3 a_wo a_wn f2_eueq3 a_sup_set_class f4_eueq3 a_wceq a_wa f1_eueq3 f2_eueq3 a_sup_set_class f5_eueq3 a_wceq a_wa a_wo f0_eueq3 f2_eueq3 a_sup_set_class f3_eueq3 a_wceq a_wa a_wo p_bitrd f0_eueq3 f2_eueq3 a_sup_set_class f3_eueq3 a_wceq a_wa f0_eueq3 f1_eueq3 a_wo a_wn f2_eueq3 a_sup_set_class f4_eueq3 a_wceq a_wa f1_eueq3 f2_eueq3 a_sup_set_class f5_eueq3 a_wceq a_wa p_3orrot f0_eueq3 f1_eueq3 a_wo a_wn f2_eueq3 a_sup_set_class f4_eueq3 a_wceq a_wa f1_eueq3 f2_eueq3 a_sup_set_class f5_eueq3 a_wceq a_wa f0_eueq3 f2_eueq3 a_sup_set_class f3_eueq3 a_wceq a_wa a_df-3or f0_eueq3 f2_eueq3 a_sup_set_class f3_eueq3 a_wceq a_wa f0_eueq3 f1_eueq3 a_wo a_wn f2_eueq3 a_sup_set_class f4_eueq3 a_wceq a_wa f1_eueq3 f2_eueq3 a_sup_set_class f5_eueq3 a_wceq a_wa a_w3o f0_eueq3 f1_eueq3 a_wo a_wn f2_eueq3 a_sup_set_class f4_eueq3 a_wceq a_wa f1_eueq3 f2_eueq3 a_sup_set_class f5_eueq3 a_wceq a_wa f0_eueq3 f2_eueq3 a_sup_set_class f3_eueq3 a_wceq a_wa a_w3o f0_eueq3 f1_eueq3 a_wo a_wn f2_eueq3 a_sup_set_class f4_eueq3 a_wceq a_wa f1_eueq3 f2_eueq3 a_sup_set_class f5_eueq3 a_wceq a_wa a_wo f0_eueq3 f2_eueq3 a_sup_set_class f3_eueq3 a_wceq a_wa a_wo p_bitri f0_eueq3 f2_eueq3 a_sup_set_class f3_eueq3 a_wceq f0_eueq3 f1_eueq3 a_wo a_wn f2_eueq3 a_sup_set_class f4_eueq3 a_wceq a_wa f1_eueq3 f2_eueq3 a_sup_set_class f5_eueq3 a_wceq a_wa a_wo f0_eueq3 f2_eueq3 a_sup_set_class f3_eueq3 a_wceq a_wa a_wo f0_eueq3 f2_eueq3 a_sup_set_class f3_eueq3 a_wceq a_wa f0_eueq3 f1_eueq3 a_wo a_wn f2_eueq3 a_sup_set_class f4_eueq3 a_wceq a_wa f1_eueq3 f2_eueq3 a_sup_set_class f5_eueq3 a_wceq a_wa a_w3o p_syl6bbr f0_eueq3 f2_eueq3 a_sup_set_class f3_eueq3 a_wceq f0_eueq3 f2_eueq3 a_sup_set_class f3_eueq3 a_wceq a_wa f0_eueq3 f1_eueq3 a_wo a_wn f2_eueq3 a_sup_set_class f4_eueq3 a_wceq a_wa f1_eueq3 f2_eueq3 a_sup_set_class f5_eueq3 a_wceq a_wa a_w3o f2_eueq3 p_eubidv f0_eueq3 f2_eueq3 a_sup_set_class f3_eueq3 a_wceq f2_eueq3 a_weu f0_eueq3 f2_eueq3 a_sup_set_class f3_eueq3 a_wceq a_wa f0_eueq3 f1_eueq3 a_wo a_wn f2_eueq3 a_sup_set_class f4_eueq3 a_wceq a_wa f1_eueq3 f2_eueq3 a_sup_set_class f5_eueq3 a_wceq a_wa a_w3o f2_eueq3 a_weu p_mpbii e2_eueq3 f2_eueq3 f5_eueq3 p_eueq1 f1_eueq3 f2_eueq3 a_sup_set_class f5_eueq3 a_wceq p_ibar e3_eueq3 f0_eueq3 f1_eueq3 p_imnani f0_eueq3 f1_eueq3 a_wn f2_eueq3 a_sup_set_class f3_eueq3 a_wceq p_adantr f0_eueq3 f1_eueq3 p_pm2.46 f0_eueq3 f1_eueq3 a_wo a_wn f1_eueq3 a_wn f2_eueq3 a_sup_set_class f4_eueq3 a_wceq p_adantr f0_eueq3 f2_eueq3 a_sup_set_class f3_eueq3 a_wceq a_wa f1_eueq3 a_wn f0_eueq3 f1_eueq3 a_wo a_wn f2_eueq3 a_sup_set_class f4_eueq3 a_wceq a_wa p_jaoi f0_eueq3 f2_eueq3 a_sup_set_class f3_eueq3 a_wceq a_wa f0_eueq3 f1_eueq3 a_wo a_wn f2_eueq3 a_sup_set_class f4_eueq3 a_wceq a_wa a_wo f1_eueq3 p_con2i f0_eueq3 f2_eueq3 a_sup_set_class f3_eueq3 a_wceq a_wa f0_eueq3 f1_eueq3 a_wo a_wn f2_eueq3 a_sup_set_class f4_eueq3 a_wceq a_wa a_wo f1_eueq3 f2_eueq3 a_sup_set_class f5_eueq3 a_wceq a_wa p_biorf f1_eueq3 f0_eueq3 f2_eueq3 a_sup_set_class f3_eueq3 a_wceq a_wa f0_eueq3 f1_eueq3 a_wo a_wn f2_eueq3 a_sup_set_class f4_eueq3 a_wceq a_wa a_wo a_wn f1_eueq3 f2_eueq3 a_sup_set_class f5_eueq3 a_wceq a_wa f0_eueq3 f2_eueq3 a_sup_set_class f3_eueq3 a_wceq a_wa f0_eueq3 f1_eueq3 a_wo a_wn f2_eueq3 a_sup_set_class f4_eueq3 a_wceq a_wa a_wo f1_eueq3 f2_eueq3 a_sup_set_class f5_eueq3 a_wceq a_wa a_wo a_wb p_syl f1_eueq3 f2_eueq3 a_sup_set_class f5_eueq3 a_wceq f1_eueq3 f2_eueq3 a_sup_set_class f5_eueq3 a_wceq a_wa f0_eueq3 f2_eueq3 a_sup_set_class f3_eueq3 a_wceq a_wa f0_eueq3 f1_eueq3 a_wo a_wn f2_eueq3 a_sup_set_class f4_eueq3 a_wceq a_wa a_wo f1_eueq3 f2_eueq3 a_sup_set_class f5_eueq3 a_wceq a_wa a_wo p_bitrd f0_eueq3 f2_eueq3 a_sup_set_class f3_eueq3 a_wceq a_wa f0_eueq3 f1_eueq3 a_wo a_wn f2_eueq3 a_sup_set_class f4_eueq3 a_wceq a_wa f1_eueq3 f2_eueq3 a_sup_set_class f5_eueq3 a_wceq a_wa a_df-3or f1_eueq3 f2_eueq3 a_sup_set_class f5_eueq3 a_wceq f0_eueq3 f2_eueq3 a_sup_set_class f3_eueq3 a_wceq a_wa f0_eueq3 f1_eueq3 a_wo a_wn f2_eueq3 a_sup_set_class f4_eueq3 a_wceq a_wa a_wo f1_eueq3 f2_eueq3 a_sup_set_class f5_eueq3 a_wceq a_wa a_wo f0_eueq3 f2_eueq3 a_sup_set_class f3_eueq3 a_wceq a_wa f0_eueq3 f1_eueq3 a_wo a_wn f2_eueq3 a_sup_set_class f4_eueq3 a_wceq a_wa f1_eueq3 f2_eueq3 a_sup_set_class f5_eueq3 a_wceq a_wa a_w3o p_syl6bbr f1_eueq3 f2_eueq3 a_sup_set_class f5_eueq3 a_wceq f0_eueq3 f2_eueq3 a_sup_set_class f3_eueq3 a_wceq a_wa f0_eueq3 f1_eueq3 a_wo a_wn f2_eueq3 a_sup_set_class f4_eueq3 a_wceq a_wa f1_eueq3 f2_eueq3 a_sup_set_class f5_eueq3 a_wceq a_wa a_w3o f2_eueq3 p_eubidv f1_eueq3 f2_eueq3 a_sup_set_class f5_eueq3 a_wceq f2_eueq3 a_weu f0_eueq3 f2_eueq3 a_sup_set_class f3_eueq3 a_wceq a_wa f0_eueq3 f1_eueq3 a_wo a_wn f2_eueq3 a_sup_set_class f4_eueq3 a_wceq a_wa f1_eueq3 f2_eueq3 a_sup_set_class f5_eueq3 a_wceq a_wa a_w3o f2_eueq3 a_weu p_mpbii e1_eueq3 f2_eueq3 f4_eueq3 p_eueq1 f0_eueq3 f1_eueq3 a_wo a_wn f2_eueq3 a_sup_set_class f4_eueq3 a_wceq p_ibar f0_eueq3 f2_eueq3 a_sup_set_class f3_eueq3 a_wceq p_simpl f1_eueq3 f2_eueq3 a_sup_set_class f5_eueq3 a_wceq p_simpl f0_eueq3 f2_eueq3 a_sup_set_class f3_eueq3 a_wceq a_wa f0_eueq3 f1_eueq3 f2_eueq3 a_sup_set_class f5_eueq3 a_wceq a_wa f1_eueq3 p_orim12i f0_eueq3 f2_eueq3 a_sup_set_class f3_eueq3 a_wceq a_wa f1_eueq3 f2_eueq3 a_sup_set_class f5_eueq3 a_wceq a_wa a_wo f0_eueq3 f1_eueq3 a_wo p_con3i f0_eueq3 f2_eueq3 a_sup_set_class f3_eueq3 a_wceq a_wa f1_eueq3 f2_eueq3 a_sup_set_class f5_eueq3 a_wceq a_wa a_wo f0_eueq3 f1_eueq3 a_wo a_wn f2_eueq3 a_sup_set_class f4_eueq3 a_wceq a_wa p_biorf f0_eueq3 f1_eueq3 a_wo a_wn f0_eueq3 f2_eueq3 a_sup_set_class f3_eueq3 a_wceq a_wa f1_eueq3 f2_eueq3 a_sup_set_class f5_eueq3 a_wceq a_wa a_wo a_wn f0_eueq3 f1_eueq3 a_wo a_wn f2_eueq3 a_sup_set_class f4_eueq3 a_wceq a_wa f0_eueq3 f2_eueq3 a_sup_set_class f3_eueq3 a_wceq a_wa f1_eueq3 f2_eueq3 a_sup_set_class f5_eueq3 a_wceq a_wa a_wo f0_eueq3 f1_eueq3 a_wo a_wn f2_eueq3 a_sup_set_class f4_eueq3 a_wceq a_wa a_wo a_wb p_syl f0_eueq3 f1_eueq3 a_wo a_wn f2_eueq3 a_sup_set_class f4_eueq3 a_wceq f0_eueq3 f1_eueq3 a_wo a_wn f2_eueq3 a_sup_set_class f4_eueq3 a_wceq a_wa f0_eueq3 f2_eueq3 a_sup_set_class f3_eueq3 a_wceq a_wa f1_eueq3 f2_eueq3 a_sup_set_class f5_eueq3 a_wceq a_wa a_wo f0_eueq3 f1_eueq3 a_wo a_wn f2_eueq3 a_sup_set_class f4_eueq3 a_wceq a_wa a_wo p_bitrd f0_eueq3 f2_eueq3 a_sup_set_class f3_eueq3 a_wceq a_wa f0_eueq3 f1_eueq3 a_wo a_wn f2_eueq3 a_sup_set_class f4_eueq3 a_wceq a_wa f1_eueq3 f2_eueq3 a_sup_set_class f5_eueq3 a_wceq a_wa p_3orcomb f0_eueq3 f2_eueq3 a_sup_set_class f3_eueq3 a_wceq a_wa f1_eueq3 f2_eueq3 a_sup_set_class f5_eueq3 a_wceq a_wa f0_eueq3 f1_eueq3 a_wo a_wn f2_eueq3 a_sup_set_class f4_eueq3 a_wceq a_wa a_df-3or f0_eueq3 f2_eueq3 a_sup_set_class f3_eueq3 a_wceq a_wa f0_eueq3 f1_eueq3 a_wo a_wn f2_eueq3 a_sup_set_class f4_eueq3 a_wceq a_wa f1_eueq3 f2_eueq3 a_sup_set_class f5_eueq3 a_wceq a_wa a_w3o f0_eueq3 f2_eueq3 a_sup_set_class f3_eueq3 a_wceq a_wa f1_eueq3 f2_eueq3 a_sup_set_class f5_eueq3 a_wceq a_wa f0_eueq3 f1_eueq3 a_wo a_wn f2_eueq3 a_sup_set_class f4_eueq3 a_wceq a_wa a_w3o f0_eueq3 f2_eueq3 a_sup_set_class f3_eueq3 a_wceq a_wa f1_eueq3 f2_eueq3 a_sup_set_class f5_eueq3 a_wceq a_wa a_wo f0_eueq3 f1_eueq3 a_wo a_wn f2_eueq3 a_sup_set_class f4_eueq3 a_wceq a_wa a_wo p_bitri f0_eueq3 f1_eueq3 a_wo a_wn f2_eueq3 a_sup_set_class f4_eueq3 a_wceq f0_eueq3 f2_eueq3 a_sup_set_class f3_eueq3 a_wceq a_wa f1_eueq3 f2_eueq3 a_sup_set_class f5_eueq3 a_wceq a_wa a_wo f0_eueq3 f1_eueq3 a_wo a_wn f2_eueq3 a_sup_set_class f4_eueq3 a_wceq a_wa a_wo f0_eueq3 f2_eueq3 a_sup_set_class f3_eueq3 a_wceq a_wa f0_eueq3 f1_eueq3 a_wo a_wn f2_eueq3 a_sup_set_class f4_eueq3 a_wceq a_wa f1_eueq3 f2_eueq3 a_sup_set_class f5_eueq3 a_wceq a_wa a_w3o p_syl6bbr f0_eueq3 f1_eueq3 a_wo a_wn f2_eueq3 a_sup_set_class f4_eueq3 a_wceq f0_eueq3 f2_eueq3 a_sup_set_class f3_eueq3 a_wceq a_wa f0_eueq3 f1_eueq3 a_wo a_wn f2_eueq3 a_sup_set_class f4_eueq3 a_wceq a_wa f1_eueq3 f2_eueq3 a_sup_set_class f5_eueq3 a_wceq a_wa a_w3o f2_eueq3 p_eubidv f0_eueq3 f1_eueq3 a_wo a_wn f2_eueq3 a_sup_set_class f4_eueq3 a_wceq f2_eueq3 a_weu f0_eueq3 f2_eueq3 a_sup_set_class f3_eueq3 a_wceq a_wa f0_eueq3 f1_eueq3 a_wo a_wn f2_eueq3 a_sup_set_class f4_eueq3 a_wceq a_wa f1_eueq3 f2_eueq3 a_sup_set_class f5_eueq3 a_wceq a_wa a_w3o f2_eueq3 a_weu p_mpbii f0_eueq3 f1_eueq3 f0_eueq3 f2_eueq3 a_sup_set_class f3_eueq3 a_wceq a_wa f0_eueq3 f1_eueq3 a_wo a_wn f2_eueq3 a_sup_set_class f4_eueq3 a_wceq a_wa f1_eueq3 f2_eueq3 a_sup_set_class f5_eueq3 a_wceq a_wa a_w3o f2_eueq3 a_weu p_ecase3 $.
$}

$(There is at most one set equal to a class.  (Contributed by NM,
       8-Mar-1995.) $)

${
	$v x A  $.
	$d x A  $.
	f0_moeq $f set x $.
	f1_moeq $f class A $.
	p_moeq $p |- E* x x = A $= f0_moeq f1_moeq p_isset f0_moeq f1_moeq p_eueq f0_moeq a_sup_set_class f1_moeq a_wceq f0_moeq a_wex f1_moeq a_cvv a_wcel f0_moeq a_sup_set_class f1_moeq a_wceq f0_moeq a_weu p_bitr3i f0_moeq a_sup_set_class f1_moeq a_wceq f0_moeq a_wex f0_moeq a_sup_set_class f1_moeq a_wceq f0_moeq a_weu p_biimpi f0_moeq a_sup_set_class f1_moeq a_wceq f0_moeq a_df-mo f0_moeq a_sup_set_class f1_moeq a_wceq f0_moeq a_wmo f0_moeq a_sup_set_class f1_moeq a_wceq f0_moeq a_wex f0_moeq a_sup_set_class f1_moeq a_wceq f0_moeq a_weu a_wi p_mpbir $.
$}

$("At most one" property of equality (split into 3 cases).  (The first 2
       hypotheses could be eliminated with longer proof.)  (Contributed by NM,
       23-Apr-1995.) $)

${
	$v ph ps x A B C  $.
	$d x y ph  $.
	$d x y ps  $.
	$d x y A  $.
	$d x y B  $.
	$d x y C  $.
	f0_moeq3 $f wff ph $.
	f1_moeq3 $f wff ps $.
	f2_moeq3 $f set x $.
	f3_moeq3 $f class A $.
	f4_moeq3 $f class B $.
	f5_moeq3 $f class C $.
	i0_moeq3 $f set y $.
	e0_moeq3 $e |- B e. _V $.
	e1_moeq3 $e |- C e. _V $.
	e2_moeq3 $e |- -. ( ph /\ ps ) $.
	p_moeq3 $p |- E* x ( ( ph /\ x = A ) \/ ( -. ( ph \/ ps ) /\ x = B ) \/ ( ps /\ x = C ) ) $= i0_moeq3 a_sup_set_class f3_moeq3 f2_moeq3 a_sup_set_class p_eqeq2 i0_moeq3 a_sup_set_class f3_moeq3 a_wceq f2_moeq3 a_sup_set_class i0_moeq3 a_sup_set_class a_wceq f2_moeq3 a_sup_set_class f3_moeq3 a_wceq f0_moeq3 p_anbi2d i0_moeq3 a_sup_set_class f3_moeq3 a_wceq f0_moeq3 f1_moeq3 a_wo a_wn f2_moeq3 a_sup_set_class f4_moeq3 a_wceq a_wa p_biidd i0_moeq3 a_sup_set_class f3_moeq3 a_wceq f1_moeq3 f2_moeq3 a_sup_set_class f5_moeq3 a_wceq a_wa p_biidd i0_moeq3 a_sup_set_class f3_moeq3 a_wceq f0_moeq3 f2_moeq3 a_sup_set_class i0_moeq3 a_sup_set_class a_wceq a_wa f0_moeq3 f2_moeq3 a_sup_set_class f3_moeq3 a_wceq a_wa f0_moeq3 f1_moeq3 a_wo a_wn f2_moeq3 a_sup_set_class f4_moeq3 a_wceq a_wa f0_moeq3 f1_moeq3 a_wo a_wn f2_moeq3 a_sup_set_class f4_moeq3 a_wceq a_wa f1_moeq3 f2_moeq3 a_sup_set_class f5_moeq3 a_wceq a_wa f1_moeq3 f2_moeq3 a_sup_set_class f5_moeq3 a_wceq a_wa p_3orbi123d i0_moeq3 a_sup_set_class f3_moeq3 a_wceq f0_moeq3 f2_moeq3 a_sup_set_class i0_moeq3 a_sup_set_class a_wceq a_wa f0_moeq3 f1_moeq3 a_wo a_wn f2_moeq3 a_sup_set_class f4_moeq3 a_wceq a_wa f1_moeq3 f2_moeq3 a_sup_set_class f5_moeq3 a_wceq a_wa a_w3o f0_moeq3 f2_moeq3 a_sup_set_class f3_moeq3 a_wceq a_wa f0_moeq3 f1_moeq3 a_wo a_wn f2_moeq3 a_sup_set_class f4_moeq3 a_wceq a_wa f1_moeq3 f2_moeq3 a_sup_set_class f5_moeq3 a_wceq a_wa a_w3o f2_moeq3 p_eubidv i0_moeq3 p_vex e0_moeq3 e1_moeq3 e2_moeq3 f0_moeq3 f1_moeq3 f2_moeq3 i0_moeq3 a_sup_set_class f4_moeq3 f5_moeq3 p_eueq3 f0_moeq3 f2_moeq3 a_sup_set_class i0_moeq3 a_sup_set_class a_wceq a_wa f0_moeq3 f1_moeq3 a_wo a_wn f2_moeq3 a_sup_set_class f4_moeq3 a_wceq a_wa f1_moeq3 f2_moeq3 a_sup_set_class f5_moeq3 a_wceq a_wa a_w3o f2_moeq3 a_weu f0_moeq3 f2_moeq3 a_sup_set_class f3_moeq3 a_wceq a_wa f0_moeq3 f1_moeq3 a_wo a_wn f2_moeq3 a_sup_set_class f4_moeq3 a_wceq a_wa f1_moeq3 f2_moeq3 a_sup_set_class f5_moeq3 a_wceq a_wa a_w3o f2_moeq3 a_weu i0_moeq3 f3_moeq3 a_cvv p_vtoclg f0_moeq3 f2_moeq3 a_sup_set_class f3_moeq3 a_wceq a_wa f0_moeq3 f1_moeq3 a_wo a_wn f2_moeq3 a_sup_set_class f4_moeq3 a_wceq a_wa f1_moeq3 f2_moeq3 a_sup_set_class f5_moeq3 a_wceq a_wa a_w3o f2_moeq3 p_eumo f3_moeq3 a_cvv a_wcel f0_moeq3 f2_moeq3 a_sup_set_class f3_moeq3 a_wceq a_wa f0_moeq3 f1_moeq3 a_wo a_wn f2_moeq3 a_sup_set_class f4_moeq3 a_wceq a_wa f1_moeq3 f2_moeq3 a_sup_set_class f5_moeq3 a_wceq a_wa a_w3o f2_moeq3 a_weu f0_moeq3 f2_moeq3 a_sup_set_class f3_moeq3 a_wceq a_wa f0_moeq3 f1_moeq3 a_wo a_wn f2_moeq3 a_sup_set_class f4_moeq3 a_wceq a_wa f1_moeq3 f2_moeq3 a_sup_set_class f5_moeq3 a_wceq a_wa a_w3o f2_moeq3 a_wmo p_syl f2_moeq3 p_vex f2_moeq3 a_sup_set_class f3_moeq3 a_cvv p_eleq1 f2_moeq3 a_sup_set_class f3_moeq3 a_wceq f2_moeq3 a_sup_set_class a_cvv a_wcel f3_moeq3 a_cvv a_wcel p_mpbii f3_moeq3 a_cvv a_wcel f2_moeq3 a_sup_set_class i0_moeq3 a_sup_set_class a_wceq p_pm2.21 f2_moeq3 a_sup_set_class f3_moeq3 a_wceq f3_moeq3 a_cvv a_wcel f3_moeq3 a_cvv a_wcel a_wn f2_moeq3 a_sup_set_class i0_moeq3 a_sup_set_class a_wceq p_syl5 f3_moeq3 a_cvv a_wcel a_wn f2_moeq3 a_sup_set_class f3_moeq3 a_wceq f2_moeq3 a_sup_set_class i0_moeq3 a_sup_set_class a_wceq f0_moeq3 p_anim2d f3_moeq3 a_cvv a_wcel a_wn f0_moeq3 f2_moeq3 a_sup_set_class f3_moeq3 a_wceq a_wa f0_moeq3 f2_moeq3 a_sup_set_class i0_moeq3 a_sup_set_class a_wceq a_wa f0_moeq3 f1_moeq3 a_wo a_wn f2_moeq3 a_sup_set_class f4_moeq3 a_wceq a_wa f1_moeq3 f2_moeq3 a_sup_set_class f5_moeq3 a_wceq a_wa a_wo p_orim1d f0_moeq3 f2_moeq3 a_sup_set_class f3_moeq3 a_wceq a_wa f0_moeq3 f1_moeq3 a_wo a_wn f2_moeq3 a_sup_set_class f4_moeq3 a_wceq a_wa f1_moeq3 f2_moeq3 a_sup_set_class f5_moeq3 a_wceq a_wa p_3orass f0_moeq3 f2_moeq3 a_sup_set_class i0_moeq3 a_sup_set_class a_wceq a_wa f0_moeq3 f1_moeq3 a_wo a_wn f2_moeq3 a_sup_set_class f4_moeq3 a_wceq a_wa f1_moeq3 f2_moeq3 a_sup_set_class f5_moeq3 a_wceq a_wa p_3orass f3_moeq3 a_cvv a_wcel a_wn f0_moeq3 f2_moeq3 a_sup_set_class f3_moeq3 a_wceq a_wa f0_moeq3 f1_moeq3 a_wo a_wn f2_moeq3 a_sup_set_class f4_moeq3 a_wceq a_wa f1_moeq3 f2_moeq3 a_sup_set_class f5_moeq3 a_wceq a_wa a_wo a_wo f0_moeq3 f2_moeq3 a_sup_set_class i0_moeq3 a_sup_set_class a_wceq a_wa f0_moeq3 f1_moeq3 a_wo a_wn f2_moeq3 a_sup_set_class f4_moeq3 a_wceq a_wa f1_moeq3 f2_moeq3 a_sup_set_class f5_moeq3 a_wceq a_wa a_wo a_wo f0_moeq3 f2_moeq3 a_sup_set_class f3_moeq3 a_wceq a_wa f0_moeq3 f1_moeq3 a_wo a_wn f2_moeq3 a_sup_set_class f4_moeq3 a_wceq a_wa f1_moeq3 f2_moeq3 a_sup_set_class f5_moeq3 a_wceq a_wa a_w3o f0_moeq3 f2_moeq3 a_sup_set_class i0_moeq3 a_sup_set_class a_wceq a_wa f0_moeq3 f1_moeq3 a_wo a_wn f2_moeq3 a_sup_set_class f4_moeq3 a_wceq a_wa f1_moeq3 f2_moeq3 a_sup_set_class f5_moeq3 a_wceq a_wa a_w3o p_3imtr4g f3_moeq3 a_cvv a_wcel a_wn f0_moeq3 f2_moeq3 a_sup_set_class f3_moeq3 a_wceq a_wa f0_moeq3 f1_moeq3 a_wo a_wn f2_moeq3 a_sup_set_class f4_moeq3 a_wceq a_wa f1_moeq3 f2_moeq3 a_sup_set_class f5_moeq3 a_wceq a_wa a_w3o f0_moeq3 f2_moeq3 a_sup_set_class i0_moeq3 a_sup_set_class a_wceq a_wa f0_moeq3 f1_moeq3 a_wo a_wn f2_moeq3 a_sup_set_class f4_moeq3 a_wceq a_wa f1_moeq3 f2_moeq3 a_sup_set_class f5_moeq3 a_wceq a_wa a_w3o a_wi f2_moeq3 p_alrimiv i0_moeq3 p_vex e0_moeq3 e1_moeq3 e2_moeq3 f0_moeq3 f1_moeq3 f2_moeq3 i0_moeq3 a_sup_set_class f4_moeq3 f5_moeq3 p_eueq3 f0_moeq3 f2_moeq3 a_sup_set_class f3_moeq3 a_wceq a_wa f0_moeq3 f1_moeq3 a_wo a_wn f2_moeq3 a_sup_set_class f4_moeq3 a_wceq a_wa f1_moeq3 f2_moeq3 a_sup_set_class f5_moeq3 a_wceq a_wa a_w3o f0_moeq3 f2_moeq3 a_sup_set_class i0_moeq3 a_sup_set_class a_wceq a_wa f0_moeq3 f1_moeq3 a_wo a_wn f2_moeq3 a_sup_set_class f4_moeq3 a_wceq a_wa f1_moeq3 f2_moeq3 a_sup_set_class f5_moeq3 a_wceq a_wa a_w3o f2_moeq3 p_euimmo f3_moeq3 a_cvv a_wcel a_wn f0_moeq3 f2_moeq3 a_sup_set_class f3_moeq3 a_wceq a_wa f0_moeq3 f1_moeq3 a_wo a_wn f2_moeq3 a_sup_set_class f4_moeq3 a_wceq a_wa f1_moeq3 f2_moeq3 a_sup_set_class f5_moeq3 a_wceq a_wa a_w3o f0_moeq3 f2_moeq3 a_sup_set_class i0_moeq3 a_sup_set_class a_wceq a_wa f0_moeq3 f1_moeq3 a_wo a_wn f2_moeq3 a_sup_set_class f4_moeq3 a_wceq a_wa f1_moeq3 f2_moeq3 a_sup_set_class f5_moeq3 a_wceq a_wa a_w3o a_wi f2_moeq3 a_wal f0_moeq3 f2_moeq3 a_sup_set_class i0_moeq3 a_sup_set_class a_wceq a_wa f0_moeq3 f1_moeq3 a_wo a_wn f2_moeq3 a_sup_set_class f4_moeq3 a_wceq a_wa f1_moeq3 f2_moeq3 a_sup_set_class f5_moeq3 a_wceq a_wa a_w3o f2_moeq3 a_weu f0_moeq3 f2_moeq3 a_sup_set_class f3_moeq3 a_wceq a_wa f0_moeq3 f1_moeq3 a_wo a_wn f2_moeq3 a_sup_set_class f4_moeq3 a_wceq a_wa f1_moeq3 f2_moeq3 a_sup_set_class f5_moeq3 a_wceq a_wa a_w3o f2_moeq3 a_wmo p_ee10 f3_moeq3 a_cvv a_wcel f0_moeq3 f2_moeq3 a_sup_set_class f3_moeq3 a_wceq a_wa f0_moeq3 f1_moeq3 a_wo a_wn f2_moeq3 a_sup_set_class f4_moeq3 a_wceq a_wa f1_moeq3 f2_moeq3 a_sup_set_class f5_moeq3 a_wceq a_wa a_w3o f2_moeq3 a_wmo p_pm2.61i $.
$}

$("At most one" remains true after substitution.  (Contributed by NM,
       9-Mar-1995.) $)

${
	$v ph x y A  $.
	$d x y A  $.
	f0_mosub $f wff ph $.
	f1_mosub $f set x $.
	f2_mosub $f set y $.
	f3_mosub $f class A $.
	e0_mosub $e |- E* x ph $.
	p_mosub $p |- E* x E. y ( y = A /\ ph ) $= f2_mosub f3_mosub p_moeq e0_mosub f0_mosub f1_mosub a_wmo f2_mosub a_ax-gen f2_mosub a_sup_set_class f3_mosub a_wceq f0_mosub f2_mosub f1_mosub p_moexexv f2_mosub a_sup_set_class f3_mosub a_wceq f2_mosub a_wmo f0_mosub f1_mosub a_wmo f2_mosub a_wal f2_mosub a_sup_set_class f3_mosub a_wceq f0_mosub a_wa f2_mosub a_wex f1_mosub a_wmo p_mp2an $.
$}

$(Theorem for inferring "at most one."  (Contributed by NM,
       17-Oct-1996.) $)

${
	$v ph x A  $.
	$d x y A  $.
	$d y ph  $.
	f0_mo2icl $f wff ph $.
	f1_mo2icl $f set x $.
	f2_mo2icl $f class A $.
	i0_mo2icl $f set y $.
	p_mo2icl $p |- ( A. x ( ph -> x = A ) -> E* x ph ) $= i0_mo2icl a_sup_set_class f2_mo2icl f1_mo2icl a_sup_set_class p_eqeq2 i0_mo2icl a_sup_set_class f2_mo2icl a_wceq f1_mo2icl a_sup_set_class i0_mo2icl a_sup_set_class a_wceq f1_mo2icl a_sup_set_class f2_mo2icl a_wceq f0_mo2icl p_imbi2d i0_mo2icl a_sup_set_class f2_mo2icl a_wceq f0_mo2icl f1_mo2icl a_sup_set_class i0_mo2icl a_sup_set_class a_wceq a_wi f0_mo2icl f1_mo2icl a_sup_set_class f2_mo2icl a_wceq a_wi f1_mo2icl p_albidv i0_mo2icl a_sup_set_class f2_mo2icl a_wceq f0_mo2icl f1_mo2icl a_sup_set_class i0_mo2icl a_sup_set_class a_wceq a_wi f1_mo2icl a_wal f0_mo2icl f1_mo2icl a_sup_set_class f2_mo2icl a_wceq a_wi f1_mo2icl a_wal f0_mo2icl f1_mo2icl a_wmo p_imbi1d f0_mo2icl f1_mo2icl a_sup_set_class i0_mo2icl a_sup_set_class a_wceq a_wi f1_mo2icl a_wal i0_mo2icl p_19.8a f0_mo2icl i0_mo2icl p_nfv f0_mo2icl f1_mo2icl i0_mo2icl p_mo2 f0_mo2icl f1_mo2icl a_sup_set_class i0_mo2icl a_sup_set_class a_wceq a_wi f1_mo2icl a_wal f0_mo2icl f1_mo2icl a_sup_set_class i0_mo2icl a_sup_set_class a_wceq a_wi f1_mo2icl a_wal i0_mo2icl a_wex f0_mo2icl f1_mo2icl a_wmo p_sylibr f0_mo2icl f1_mo2icl a_sup_set_class i0_mo2icl a_sup_set_class a_wceq a_wi f1_mo2icl a_wal f0_mo2icl f1_mo2icl a_wmo a_wi f0_mo2icl f1_mo2icl a_sup_set_class f2_mo2icl a_wceq a_wi f1_mo2icl a_wal f0_mo2icl f1_mo2icl a_wmo a_wi i0_mo2icl f2_mo2icl a_cvv p_vtoclg f1_mo2icl p_vex f1_mo2icl a_sup_set_class f2_mo2icl a_cvv p_eleq1 f1_mo2icl a_sup_set_class f2_mo2icl a_wceq f1_mo2icl a_sup_set_class a_cvv a_wcel f2_mo2icl a_cvv a_wcel p_mpbii f1_mo2icl a_sup_set_class f2_mo2icl a_wceq f2_mo2icl a_cvv a_wcel f0_mo2icl p_imim2i f0_mo2icl f1_mo2icl a_sup_set_class f2_mo2icl a_wceq a_wi f0_mo2icl f2_mo2icl a_cvv a_wcel p_con3rr3 f2_mo2icl a_cvv a_wcel a_wn f0_mo2icl f1_mo2icl a_sup_set_class f2_mo2icl a_wceq a_wi f0_mo2icl a_wn f1_mo2icl p_alimdv f0_mo2icl f1_mo2icl p_alnex f0_mo2icl f1_mo2icl p_exmo f0_mo2icl f1_mo2icl a_wex f0_mo2icl f1_mo2icl a_wmo p_ori f0_mo2icl a_wn f1_mo2icl a_wal f0_mo2icl f1_mo2icl a_wex a_wn f0_mo2icl f1_mo2icl a_wmo p_sylbi f2_mo2icl a_cvv a_wcel a_wn f0_mo2icl f1_mo2icl a_sup_set_class f2_mo2icl a_wceq a_wi f1_mo2icl a_wal f0_mo2icl a_wn f1_mo2icl a_wal f0_mo2icl f1_mo2icl a_wmo p_syl6 f2_mo2icl a_cvv a_wcel f0_mo2icl f1_mo2icl a_sup_set_class f2_mo2icl a_wceq a_wi f1_mo2icl a_wal f0_mo2icl f1_mo2icl a_wmo a_wi p_pm2.61i $.
$}

$(Consequence of "at most one."  (Contributed by NM, 2-Jan-2015.) $)

${
	$v ph ps x A B  $.
	$d x y A  $.
	$d y ph  $.
	$d x y ps  $.
	f0_mob2 $f wff ph $.
	f1_mob2 $f wff ps $.
	f2_mob2 $f set x $.
	f3_mob2 $f class A $.
	f4_mob2 $f class B $.
	i0_mob2 $f set y $.
	e0_mob2 $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_mob2 $p |- ( ( A e. B /\ E* x ph /\ ph ) -> ( x = A <-> ps ) ) $= f3_mob2 f4_mob2 a_wcel f0_mob2 f2_mob2 a_wmo f0_mob2 p_simp3 e0_mob2 f3_mob2 f4_mob2 a_wcel f0_mob2 f2_mob2 a_wmo f0_mob2 a_w3a f0_mob2 f2_mob2 a_sup_set_class f3_mob2 a_wceq f1_mob2 p_syl5ibcom f0_mob2 f2_mob2 i0_mob2 p_nfs1v f0_mob2 f2_mob2 i0_mob2 p_sbequ12 f0_mob2 f0_mob2 f2_mob2 i0_mob2 a_wsb f2_mob2 i0_mob2 p_mo4f f0_mob2 f0_mob2 f2_mob2 i0_mob2 a_wsb a_wa f2_mob2 a_sup_set_class i0_mob2 a_sup_set_class a_wceq a_wi i0_mob2 a_wal f2_mob2 p_sp f0_mob2 f2_mob2 a_wmo f0_mob2 f0_mob2 f2_mob2 i0_mob2 a_wsb a_wa f2_mob2 a_sup_set_class i0_mob2 a_sup_set_class a_wceq a_wi i0_mob2 a_wal f2_mob2 a_wal f0_mob2 f0_mob2 f2_mob2 i0_mob2 a_wsb a_wa f2_mob2 a_sup_set_class i0_mob2 a_sup_set_class a_wceq a_wi i0_mob2 a_wal p_sylbi f1_mob2 f2_mob2 p_nfv e0_mob2 f0_mob2 f1_mob2 f2_mob2 i0_mob2 f3_mob2 p_sbhypf i0_mob2 a_sup_set_class f3_mob2 a_wceq f0_mob2 f2_mob2 i0_mob2 a_wsb f1_mob2 f0_mob2 p_anbi2d i0_mob2 a_sup_set_class f3_mob2 f2_mob2 a_sup_set_class p_eqeq2 i0_mob2 a_sup_set_class f3_mob2 a_wceq f0_mob2 f0_mob2 f2_mob2 i0_mob2 a_wsb a_wa f0_mob2 f1_mob2 a_wa f2_mob2 a_sup_set_class i0_mob2 a_sup_set_class a_wceq f2_mob2 a_sup_set_class f3_mob2 a_wceq p_imbi12d f0_mob2 f0_mob2 f2_mob2 i0_mob2 a_wsb a_wa f2_mob2 a_sup_set_class i0_mob2 a_sup_set_class a_wceq a_wi f0_mob2 f1_mob2 a_wa f2_mob2 a_sup_set_class f3_mob2 a_wceq a_wi i0_mob2 f3_mob2 f4_mob2 p_spcgv f0_mob2 f2_mob2 a_wmo f0_mob2 f0_mob2 f2_mob2 i0_mob2 a_wsb a_wa f2_mob2 a_sup_set_class i0_mob2 a_sup_set_class a_wceq a_wi i0_mob2 a_wal f3_mob2 f4_mob2 a_wcel f0_mob2 f1_mob2 a_wa f2_mob2 a_sup_set_class f3_mob2 a_wceq a_wi p_syl5 f3_mob2 f4_mob2 a_wcel f0_mob2 f2_mob2 a_wmo f0_mob2 f1_mob2 a_wa f2_mob2 a_sup_set_class f3_mob2 a_wceq a_wi p_imp f3_mob2 f4_mob2 a_wcel f0_mob2 f2_mob2 a_wmo a_wa f0_mob2 f1_mob2 f2_mob2 a_sup_set_class f3_mob2 a_wceq p_exp3a f3_mob2 f4_mob2 a_wcel f0_mob2 f2_mob2 a_wmo f0_mob2 f1_mob2 f2_mob2 a_sup_set_class f3_mob2 a_wceq a_wi p_3impia f3_mob2 f4_mob2 a_wcel f0_mob2 f2_mob2 a_wmo f0_mob2 a_w3a f2_mob2 a_sup_set_class f3_mob2 a_wceq f1_mob2 p_impbid $.
$}

$(Consequence of "at most one."  (Contributed by NM, 29-Jun-2008.) $)

${
	$v ph ps x A B  $.
	$d x A  $.
	$d ph  $.
	$d x ps  $.
	f0_moi2 $f wff ph $.
	f1_moi2 $f wff ps $.
	f2_moi2 $f set x $.
	f3_moi2 $f class A $.
	f4_moi2 $f class B $.
	e0_moi2 $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_moi2 $p |- ( ( ( A e. B /\ E* x ph ) /\ ( ph /\ ps ) ) -> x = A ) $= e0_moi2 f0_moi2 f1_moi2 f2_moi2 f3_moi2 f4_moi2 p_mob2 f3_moi2 f4_moi2 a_wcel f0_moi2 f2_moi2 a_wmo f0_moi2 f2_moi2 a_sup_set_class f3_moi2 a_wceq f1_moi2 a_wb p_3expa f3_moi2 f4_moi2 a_wcel f0_moi2 f2_moi2 a_wmo a_wa f0_moi2 a_wa f2_moi2 a_sup_set_class f3_moi2 a_wceq f1_moi2 p_biimprd f3_moi2 f4_moi2 a_wcel f0_moi2 f2_moi2 a_wmo a_wa f0_moi2 f1_moi2 f2_moi2 a_sup_set_class f3_moi2 a_wceq p_impr $.
$}

$(Equality implied by "at most one."  (Contributed by NM, 18-Feb-2006.) $)

${
	$v ph ps ch x A B C D  $.
	$d x A  $.
	$d x B  $.
	$d x ch  $.
	$d ph  $.
	$d x ps  $.
	f0_mob $f wff ph $.
	f1_mob $f wff ps $.
	f2_mob $f wff ch $.
	f3_mob $f set x $.
	f4_mob $f class A $.
	f5_mob $f class B $.
	f6_mob $f class C $.
	f7_mob $f class D $.
	e0_mob $e |- ( x = A -> ( ph <-> ps ) ) $.
	e1_mob $e |- ( x = B -> ( ph <-> ch ) ) $.
	p_mob $p |- ( ( ( A e. C /\ B e. D ) /\ E* x ph /\ ps ) -> ( A = B <-> ch ) ) $= f5_mob f7_mob p_elex f3_mob f4_mob p_nfcv f5_mob a_cvv a_wcel f3_mob p_nfv f0_mob f3_mob p_nfmo1 f1_mob f3_mob p_nfv f5_mob a_cvv a_wcel f0_mob f3_mob a_wmo f1_mob f3_mob p_nf3an f4_mob f5_mob a_wceq f2_mob a_wb f3_mob p_nfv f5_mob a_cvv a_wcel f0_mob f3_mob a_wmo f1_mob a_w3a f4_mob f5_mob a_wceq f2_mob a_wb f3_mob p_nfim e0_mob f3_mob a_sup_set_class f4_mob a_wceq f0_mob f1_mob f5_mob a_cvv a_wcel f0_mob f3_mob a_wmo p_3anbi3d f3_mob a_sup_set_class f4_mob f5_mob p_eqeq1 f3_mob a_sup_set_class f4_mob a_wceq f3_mob a_sup_set_class f5_mob a_wceq f4_mob f5_mob a_wceq f2_mob p_bibi1d f3_mob a_sup_set_class f4_mob a_wceq f5_mob a_cvv a_wcel f0_mob f3_mob a_wmo f0_mob a_w3a f5_mob a_cvv a_wcel f0_mob f3_mob a_wmo f1_mob a_w3a f3_mob a_sup_set_class f5_mob a_wceq f2_mob a_wb f4_mob f5_mob a_wceq f2_mob a_wb p_imbi12d e1_mob f0_mob f2_mob f3_mob f5_mob a_cvv p_mob2 f5_mob a_cvv a_wcel f0_mob f3_mob a_wmo f0_mob a_w3a f3_mob a_sup_set_class f5_mob a_wceq f2_mob a_wb a_wi f5_mob a_cvv a_wcel f0_mob f3_mob a_wmo f1_mob a_w3a f4_mob f5_mob a_wceq f2_mob a_wb a_wi f3_mob f4_mob f6_mob p_vtoclgf f4_mob f6_mob a_wcel f5_mob a_cvv a_wcel f0_mob f3_mob a_wmo f1_mob a_w3a f4_mob f5_mob a_wceq f2_mob a_wb p_com12 f5_mob a_cvv a_wcel f0_mob f3_mob a_wmo f1_mob f4_mob f6_mob a_wcel f4_mob f5_mob a_wceq f2_mob a_wb a_wi p_3expib f5_mob f7_mob a_wcel f5_mob a_cvv a_wcel f0_mob f3_mob a_wmo f1_mob a_wa f4_mob f6_mob a_wcel f4_mob f5_mob a_wceq f2_mob a_wb a_wi a_wi p_syl f5_mob f7_mob a_wcel f0_mob f3_mob a_wmo f1_mob a_wa f4_mob f6_mob a_wcel f4_mob f5_mob a_wceq f2_mob a_wb p_com3r f4_mob f6_mob a_wcel f5_mob f7_mob a_wcel f0_mob f3_mob a_wmo f1_mob a_wa f4_mob f5_mob a_wceq f2_mob a_wb a_wi p_imp f4_mob f6_mob a_wcel f5_mob f7_mob a_wcel a_wa f0_mob f3_mob a_wmo f1_mob f4_mob f5_mob a_wceq f2_mob a_wb p_3impib $.
$}

$(Equality implied by "at most one."  (Contributed by NM, 18-Feb-2006.) $)

${
	$v ph ps ch x A B C D  $.
	$d x A  $.
	$d x B  $.
	$d x ch  $.
	$d ph  $.
	$d x ps  $.
	f0_moi $f wff ph $.
	f1_moi $f wff ps $.
	f2_moi $f wff ch $.
	f3_moi $f set x $.
	f4_moi $f class A $.
	f5_moi $f class B $.
	f6_moi $f class C $.
	f7_moi $f class D $.
	e0_moi $e |- ( x = A -> ( ph <-> ps ) ) $.
	e1_moi $e |- ( x = B -> ( ph <-> ch ) ) $.
	p_moi $p |- ( ( ( A e. C /\ B e. D ) /\ E* x ph /\ ( ps /\ ch ) ) -> A = B ) $= e0_moi e1_moi f0_moi f1_moi f2_moi f3_moi f4_moi f5_moi f6_moi f7_moi p_mob f4_moi f6_moi a_wcel f5_moi f7_moi a_wcel a_wa f0_moi f3_moi a_wmo f1_moi a_w3a f4_moi f5_moi a_wceq f2_moi p_biimprd f4_moi f6_moi a_wcel f5_moi f7_moi a_wcel a_wa f0_moi f3_moi a_wmo f1_moi f2_moi f4_moi f5_moi a_wceq a_wi p_3expia f4_moi f6_moi a_wcel f5_moi f7_moi a_wcel a_wa f0_moi f3_moi a_wmo a_wa f1_moi f2_moi f4_moi f5_moi a_wceq p_imp3a f4_moi f6_moi a_wcel f5_moi f7_moi a_wcel a_wa f0_moi f3_moi a_wmo f1_moi f2_moi a_wa f4_moi f5_moi a_wceq p_3impia $.
$}

$(Derive membership from uniqueness.  (Contributed by Jeff Madsen,
       2-Sep-2009.) $)

${
	$v ph ps x A B  $.
	$d B x  $.
	$d A x  $.
	$d ph  $.
	$d ps x  $.
	f0_morex $f wff ph $.
	f1_morex $f wff ps $.
	f2_morex $f set x $.
	f3_morex $f class A $.
	f4_morex $f class B $.
	e0_morex $e |- B e. _V $.
	e1_morex $e |- ( x = B -> ( ph <-> ps ) ) $.
	p_morex $p |- ( ( E. x e. A ph /\ E* x ph ) -> ( ps -> B e. A ) ) $= f0_morex f2_morex f3_morex a_df-rex f2_morex a_sup_set_class f3_morex a_wcel f0_morex f2_morex p_exancom f0_morex f2_morex f3_morex a_wrex f2_morex a_sup_set_class f3_morex a_wcel f0_morex a_wa f2_morex a_wex f0_morex f2_morex a_sup_set_class f3_morex a_wcel a_wa f2_morex a_wex p_bitri f0_morex f2_morex p_nfmo1 f0_morex f2_morex a_sup_set_class f3_morex a_wcel a_wa f2_morex p_nfe1 f0_morex f2_morex a_wmo f0_morex f2_morex a_sup_set_class f3_morex a_wcel a_wa f2_morex a_wex f2_morex p_nfan f0_morex f2_morex a_sup_set_class f3_morex a_wcel f2_morex p_mopick f0_morex f2_morex a_wmo f0_morex f2_morex a_sup_set_class f3_morex a_wcel a_wa f2_morex a_wex a_wa f0_morex f2_morex a_sup_set_class f3_morex a_wcel a_wi f2_morex p_alrimi e0_morex e1_morex f2_morex a_sup_set_class f4_morex f3_morex p_eleq1 f2_morex a_sup_set_class f4_morex a_wceq f0_morex f1_morex f2_morex a_sup_set_class f3_morex a_wcel f4_morex f3_morex a_wcel p_imbi12d f0_morex f2_morex a_sup_set_class f3_morex a_wcel a_wi f1_morex f4_morex f3_morex a_wcel a_wi f2_morex f4_morex p_spcv f0_morex f2_morex a_wmo f0_morex f2_morex a_sup_set_class f3_morex a_wcel a_wa f2_morex a_wex a_wa f0_morex f2_morex a_sup_set_class f3_morex a_wcel a_wi f2_morex a_wal f1_morex f4_morex f3_morex a_wcel a_wi p_syl f0_morex f2_morex f3_morex a_wrex f0_morex f2_morex a_wmo f0_morex f2_morex a_sup_set_class f3_morex a_wcel a_wa f2_morex a_wex f1_morex f4_morex f3_morex a_wcel a_wi p_sylan2b f0_morex f2_morex a_wmo f0_morex f2_morex f3_morex a_wrex f1_morex f4_morex f3_morex a_wcel a_wi p_ancoms $.
$}

$(Transfer existential uniqueness from a variable ` x ` to another
       variable ` y ` contained in expression ` A ` .  (Contributed by NM,
       14-Nov-2004.) $)

${
	$v ph x y A  $.
	$d x ph  $.
	$d x A  $.
	f0_euxfr2 $f wff ph $.
	f1_euxfr2 $f set x $.
	f2_euxfr2 $f set y $.
	f3_euxfr2 $f class A $.
	e0_euxfr2 $e |- A e. _V $.
	e1_euxfr2 $e |- E* y x = A $.
	p_euxfr2 $p |- ( E! x E. y ( x = A /\ ph ) <-> E! y ph ) $= f1_euxfr2 a_sup_set_class f3_euxfr2 a_wceq f0_euxfr2 a_wa f1_euxfr2 f2_euxfr2 p_2euswap e1_euxfr2 f1_euxfr2 a_sup_set_class f3_euxfr2 a_wceq f0_euxfr2 f2_euxfr2 p_moani f0_euxfr2 f1_euxfr2 a_sup_set_class f3_euxfr2 a_wceq p_ancom f0_euxfr2 f1_euxfr2 a_sup_set_class f3_euxfr2 a_wceq a_wa f1_euxfr2 a_sup_set_class f3_euxfr2 a_wceq f0_euxfr2 a_wa f2_euxfr2 p_mobii f0_euxfr2 f1_euxfr2 a_sup_set_class f3_euxfr2 a_wceq a_wa f2_euxfr2 a_wmo f1_euxfr2 a_sup_set_class f3_euxfr2 a_wceq f0_euxfr2 a_wa f2_euxfr2 a_wmo p_mpbi f1_euxfr2 a_sup_set_class f3_euxfr2 a_wceq f0_euxfr2 a_wa f2_euxfr2 a_wmo f1_euxfr2 a_sup_set_class f3_euxfr2 a_wceq f0_euxfr2 a_wa f2_euxfr2 a_wex f1_euxfr2 a_weu f1_euxfr2 a_sup_set_class f3_euxfr2 a_wceq f0_euxfr2 a_wa f1_euxfr2 a_wex f2_euxfr2 a_weu a_wi f1_euxfr2 p_mpg f1_euxfr2 a_sup_set_class f3_euxfr2 a_wceq f0_euxfr2 a_wa f2_euxfr2 f1_euxfr2 p_2euswap f1_euxfr2 f3_euxfr2 p_moeq f1_euxfr2 a_sup_set_class f3_euxfr2 a_wceq f0_euxfr2 f1_euxfr2 p_moani f0_euxfr2 f1_euxfr2 a_sup_set_class f3_euxfr2 a_wceq p_ancom f0_euxfr2 f1_euxfr2 a_sup_set_class f3_euxfr2 a_wceq a_wa f1_euxfr2 a_sup_set_class f3_euxfr2 a_wceq f0_euxfr2 a_wa f1_euxfr2 p_mobii f0_euxfr2 f1_euxfr2 a_sup_set_class f3_euxfr2 a_wceq a_wa f1_euxfr2 a_wmo f1_euxfr2 a_sup_set_class f3_euxfr2 a_wceq f0_euxfr2 a_wa f1_euxfr2 a_wmo p_mpbi f1_euxfr2 a_sup_set_class f3_euxfr2 a_wceq f0_euxfr2 a_wa f1_euxfr2 a_wmo f1_euxfr2 a_sup_set_class f3_euxfr2 a_wceq f0_euxfr2 a_wa f1_euxfr2 a_wex f2_euxfr2 a_weu f1_euxfr2 a_sup_set_class f3_euxfr2 a_wceq f0_euxfr2 a_wa f2_euxfr2 a_wex f1_euxfr2 a_weu a_wi f2_euxfr2 p_mpg f1_euxfr2 a_sup_set_class f3_euxfr2 a_wceq f0_euxfr2 a_wa f2_euxfr2 a_wex f1_euxfr2 a_weu f1_euxfr2 a_sup_set_class f3_euxfr2 a_wceq f0_euxfr2 a_wa f1_euxfr2 a_wex f2_euxfr2 a_weu p_impbii e0_euxfr2 f1_euxfr2 a_sup_set_class f3_euxfr2 a_wceq f0_euxfr2 p_biidd f0_euxfr2 f0_euxfr2 f1_euxfr2 f3_euxfr2 p_ceqsexv f1_euxfr2 a_sup_set_class f3_euxfr2 a_wceq f0_euxfr2 a_wa f1_euxfr2 a_wex f0_euxfr2 f2_euxfr2 p_eubii f1_euxfr2 a_sup_set_class f3_euxfr2 a_wceq f0_euxfr2 a_wa f2_euxfr2 a_wex f1_euxfr2 a_weu f1_euxfr2 a_sup_set_class f3_euxfr2 a_wceq f0_euxfr2 a_wa f1_euxfr2 a_wex f2_euxfr2 a_weu f0_euxfr2 f2_euxfr2 a_weu p_bitri $.
$}

$(Transfer existential uniqueness from a variable ` x ` to another
       variable ` y ` contained in expression ` A ` .  (Contributed by NM,
       14-Nov-2004.) $)

${
	$v ph ps x y A  $.
	$d x ps  $.
	$d y ph  $.
	$d x A  $.
	f0_euxfr $f wff ph $.
	f1_euxfr $f wff ps $.
	f2_euxfr $f set x $.
	f3_euxfr $f set y $.
	f4_euxfr $f class A $.
	e0_euxfr $e |- A e. _V $.
	e1_euxfr $e |- E! y x = A $.
	e2_euxfr $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_euxfr $p |- ( E! x ph <-> E! y ps ) $= e1_euxfr f2_euxfr a_sup_set_class f4_euxfr a_wceq f3_euxfr p_euex f2_euxfr a_sup_set_class f4_euxfr a_wceq f3_euxfr a_weu f2_euxfr a_sup_set_class f4_euxfr a_wceq f3_euxfr a_wex a_ax-mp f2_euxfr a_sup_set_class f4_euxfr a_wceq f3_euxfr a_wex f0_euxfr p_biantrur f2_euxfr a_sup_set_class f4_euxfr a_wceq f0_euxfr f3_euxfr p_19.41v e2_euxfr f2_euxfr a_sup_set_class f4_euxfr a_wceq f0_euxfr f1_euxfr p_pm5.32i f2_euxfr a_sup_set_class f4_euxfr a_wceq f0_euxfr a_wa f2_euxfr a_sup_set_class f4_euxfr a_wceq f1_euxfr a_wa f3_euxfr p_exbii f0_euxfr f2_euxfr a_sup_set_class f4_euxfr a_wceq f3_euxfr a_wex f0_euxfr a_wa f2_euxfr a_sup_set_class f4_euxfr a_wceq f0_euxfr a_wa f3_euxfr a_wex f2_euxfr a_sup_set_class f4_euxfr a_wceq f1_euxfr a_wa f3_euxfr a_wex p_3bitr2i f0_euxfr f2_euxfr a_sup_set_class f4_euxfr a_wceq f1_euxfr a_wa f3_euxfr a_wex f2_euxfr p_eubii e0_euxfr e1_euxfr f2_euxfr a_sup_set_class f4_euxfr a_wceq f3_euxfr p_eumoi f1_euxfr f2_euxfr f3_euxfr f4_euxfr p_euxfr2 f0_euxfr f2_euxfr a_weu f2_euxfr a_sup_set_class f4_euxfr a_wceq f1_euxfr a_wa f3_euxfr a_wex f2_euxfr a_weu f1_euxfr f3_euxfr a_weu p_bitri $.
$}

$(Existential uniqueness via an indirect equality.  (Contributed by NM,
       11-Oct-2010.) $)

${
	$v ph ps x y z A B  $.
	$d y z w ph  $.
	$d x z ps  $.
	$d y z w A  $.
	$d x z B  $.
	$d x y w  $.
	f0_euind $f wff ph $.
	f1_euind $f wff ps $.
	f2_euind $f set x $.
	f3_euind $f set y $.
	f4_euind $f set z $.
	f5_euind $f class A $.
	f6_euind $f class B $.
	i0_euind $f set w $.
	e0_euind $e |- B e. _V $.
	e1_euind $e |- ( x = y -> ( ph <-> ps ) ) $.
	e2_euind $e |- ( x = y -> A = B ) $.
	p_euind $p |- ( ( A. x A. y ( ( ph /\ ps ) -> A = B ) /\ E. x ph ) -> E! z A. x ( ph -> z = A ) ) $= e1_euind f0_euind f1_euind f2_euind f3_euind p_cbvexv e0_euind f4_euind f6_euind p_isseti f4_euind a_sup_set_class f6_euind a_wceq f4_euind a_wex f1_euind p_biantrur f1_euind f4_euind a_sup_set_class f6_euind a_wceq f4_euind a_wex f1_euind a_wa f3_euind p_exbii f4_euind a_sup_set_class f6_euind a_wceq f1_euind f4_euind p_19.41v f4_euind a_sup_set_class f6_euind a_wceq f1_euind a_wa f4_euind a_wex f4_euind a_sup_set_class f6_euind a_wceq f4_euind a_wex f1_euind a_wa f3_euind p_exbii f4_euind a_sup_set_class f6_euind a_wceq f1_euind a_wa f3_euind f4_euind p_excom f4_euind a_sup_set_class f6_euind a_wceq f4_euind a_wex f1_euind a_wa f3_euind a_wex f4_euind a_sup_set_class f6_euind a_wceq f1_euind a_wa f4_euind a_wex f3_euind a_wex f4_euind a_sup_set_class f6_euind a_wceq f1_euind a_wa f3_euind a_wex f4_euind a_wex p_bitr3i f1_euind f3_euind a_wex f4_euind a_sup_set_class f6_euind a_wceq f4_euind a_wex f1_euind a_wa f3_euind a_wex f4_euind a_sup_set_class f6_euind a_wceq f1_euind a_wa f3_euind a_wex f4_euind a_wex p_bitri f0_euind f2_euind a_wex f1_euind f3_euind a_wex f4_euind a_sup_set_class f6_euind a_wceq f1_euind a_wa f3_euind a_wex f4_euind a_wex p_bitri f5_euind f6_euind f4_euind a_sup_set_class p_eqeq2 f5_euind f6_euind a_wceq f4_euind a_sup_set_class f5_euind a_wceq f4_euind a_sup_set_class f6_euind a_wceq a_wb f0_euind f1_euind a_wa p_imim2i f4_euind a_sup_set_class f5_euind a_wceq f4_euind a_sup_set_class f6_euind a_wceq p_bi2 f4_euind a_sup_set_class f5_euind a_wceq f4_euind a_sup_set_class f6_euind a_wceq a_wb f4_euind a_sup_set_class f6_euind a_wceq f4_euind a_sup_set_class f5_euind a_wceq a_wi f0_euind f1_euind a_wa p_imim2i f0_euind f1_euind f4_euind a_sup_set_class f6_euind a_wceq p_an31 f0_euind f1_euind a_wa f4_euind a_sup_set_class f6_euind a_wceq a_wa f4_euind a_sup_set_class f6_euind a_wceq f1_euind a_wa f0_euind a_wa f4_euind a_sup_set_class f5_euind a_wceq p_imbi1i f0_euind f1_euind a_wa f4_euind a_sup_set_class f6_euind a_wceq f4_euind a_sup_set_class f5_euind a_wceq p_impexp f4_euind a_sup_set_class f6_euind a_wceq f1_euind a_wa f0_euind f4_euind a_sup_set_class f5_euind a_wceq p_impexp f0_euind f1_euind a_wa f4_euind a_sup_set_class f6_euind a_wceq a_wa f4_euind a_sup_set_class f5_euind a_wceq a_wi f4_euind a_sup_set_class f6_euind a_wceq f1_euind a_wa f0_euind a_wa f4_euind a_sup_set_class f5_euind a_wceq a_wi f0_euind f1_euind a_wa f4_euind a_sup_set_class f6_euind a_wceq f4_euind a_sup_set_class f5_euind a_wceq a_wi a_wi f4_euind a_sup_set_class f6_euind a_wceq f1_euind a_wa f0_euind f4_euind a_sup_set_class f5_euind a_wceq a_wi a_wi p_3bitr3i f0_euind f1_euind a_wa f4_euind a_sup_set_class f5_euind a_wceq f4_euind a_sup_set_class f6_euind a_wceq a_wb a_wi f0_euind f1_euind a_wa f4_euind a_sup_set_class f6_euind a_wceq f4_euind a_sup_set_class f5_euind a_wceq a_wi a_wi f4_euind a_sup_set_class f6_euind a_wceq f1_euind a_wa f0_euind f4_euind a_sup_set_class f5_euind a_wceq a_wi a_wi p_sylib f0_euind f1_euind a_wa f5_euind f6_euind a_wceq a_wi f0_euind f1_euind a_wa f4_euind a_sup_set_class f5_euind a_wceq f4_euind a_sup_set_class f6_euind a_wceq a_wb a_wi f4_euind a_sup_set_class f6_euind a_wceq f1_euind a_wa f0_euind f4_euind a_sup_set_class f5_euind a_wceq a_wi a_wi p_syl f0_euind f1_euind a_wa f5_euind f6_euind a_wceq a_wi f4_euind a_sup_set_class f6_euind a_wceq f1_euind a_wa f0_euind f4_euind a_sup_set_class f5_euind a_wceq a_wi a_wi f2_euind f3_euind p_2alimi f4_euind a_sup_set_class f6_euind a_wceq f1_euind a_wa f0_euind f4_euind a_sup_set_class f5_euind a_wceq a_wi f3_euind p_19.23v f4_euind a_sup_set_class f6_euind a_wceq f1_euind a_wa f0_euind f4_euind a_sup_set_class f5_euind a_wceq a_wi a_wi f3_euind a_wal f4_euind a_sup_set_class f6_euind a_wceq f1_euind a_wa f3_euind a_wex f0_euind f4_euind a_sup_set_class f5_euind a_wceq a_wi a_wi f2_euind p_albii f4_euind a_sup_set_class f6_euind a_wceq f1_euind a_wa f3_euind a_wex f0_euind f4_euind a_sup_set_class f5_euind a_wceq a_wi f2_euind p_19.21v f4_euind a_sup_set_class f6_euind a_wceq f1_euind a_wa f0_euind f4_euind a_sup_set_class f5_euind a_wceq a_wi a_wi f3_euind a_wal f2_euind a_wal f4_euind a_sup_set_class f6_euind a_wceq f1_euind a_wa f3_euind a_wex f0_euind f4_euind a_sup_set_class f5_euind a_wceq a_wi a_wi f2_euind a_wal f4_euind a_sup_set_class f6_euind a_wceq f1_euind a_wa f3_euind a_wex f0_euind f4_euind a_sup_set_class f5_euind a_wceq a_wi f2_euind a_wal a_wi p_bitri f0_euind f1_euind a_wa f5_euind f6_euind a_wceq a_wi f3_euind a_wal f2_euind a_wal f4_euind a_sup_set_class f6_euind a_wceq f1_euind a_wa f0_euind f4_euind a_sup_set_class f5_euind a_wceq a_wi a_wi f3_euind a_wal f2_euind a_wal f4_euind a_sup_set_class f6_euind a_wceq f1_euind a_wa f3_euind a_wex f0_euind f4_euind a_sup_set_class f5_euind a_wceq a_wi f2_euind a_wal a_wi p_sylib f0_euind f1_euind a_wa f5_euind f6_euind a_wceq a_wi f3_euind a_wal f2_euind a_wal f4_euind a_sup_set_class f6_euind a_wceq f1_euind a_wa f3_euind a_wex f0_euind f4_euind a_sup_set_class f5_euind a_wceq a_wi f2_euind a_wal f4_euind p_eximdv f0_euind f2_euind a_wex f4_euind a_sup_set_class f6_euind a_wceq f1_euind a_wa f3_euind a_wex f4_euind a_wex f0_euind f1_euind a_wa f5_euind f6_euind a_wceq a_wi f3_euind a_wal f2_euind a_wal f0_euind f4_euind a_sup_set_class f5_euind a_wceq a_wi f2_euind a_wal f4_euind a_wex p_syl5bi f0_euind f1_euind a_wa f5_euind f6_euind a_wceq a_wi f3_euind a_wal f2_euind a_wal f0_euind f2_euind a_wex f0_euind f4_euind a_sup_set_class f5_euind a_wceq a_wi f2_euind a_wal f4_euind a_wex p_imp f0_euind p_pm4.24 f0_euind f0_euind f0_euind a_wa p_biimpi f0_euind f4_euind a_sup_set_class f5_euind a_wceq f0_euind i0_euind a_sup_set_class f5_euind a_wceq p_prth f4_euind a_sup_set_class i0_euind a_sup_set_class f5_euind p_eqtr3 f0_euind f0_euind f0_euind a_wa f0_euind f4_euind a_sup_set_class f5_euind a_wceq a_wi f0_euind i0_euind a_sup_set_class f5_euind a_wceq a_wi a_wa f4_euind a_sup_set_class f5_euind a_wceq i0_euind a_sup_set_class f5_euind a_wceq a_wa f4_euind a_sup_set_class i0_euind a_sup_set_class a_wceq p_syl56 f0_euind f4_euind a_sup_set_class f5_euind a_wceq a_wi f0_euind i0_euind a_sup_set_class f5_euind a_wceq a_wi f0_euind f4_euind a_sup_set_class i0_euind a_sup_set_class a_wceq a_wi f2_euind p_alanimi f0_euind f4_euind a_sup_set_class i0_euind a_sup_set_class a_wceq f2_euind p_19.23v f0_euind f4_euind a_sup_set_class i0_euind a_sup_set_class a_wceq a_wi f2_euind a_wal f0_euind f2_euind a_wex f4_euind a_sup_set_class i0_euind a_sup_set_class a_wceq a_wi p_biimpi f0_euind f4_euind a_sup_set_class i0_euind a_sup_set_class a_wceq a_wi f2_euind a_wal f0_euind f2_euind a_wex f4_euind a_sup_set_class i0_euind a_sup_set_class a_wceq p_com12 f0_euind f4_euind a_sup_set_class f5_euind a_wceq a_wi f2_euind a_wal f0_euind i0_euind a_sup_set_class f5_euind a_wceq a_wi f2_euind a_wal a_wa f0_euind f4_euind a_sup_set_class i0_euind a_sup_set_class a_wceq a_wi f2_euind a_wal f0_euind f2_euind a_wex f4_euind a_sup_set_class i0_euind a_sup_set_class a_wceq p_syl5 f0_euind f2_euind a_wex f0_euind f4_euind a_sup_set_class f5_euind a_wceq a_wi f2_euind a_wal f0_euind i0_euind a_sup_set_class f5_euind a_wceq a_wi f2_euind a_wal a_wa f4_euind a_sup_set_class i0_euind a_sup_set_class a_wceq a_wi f4_euind i0_euind p_alrimivv f0_euind f2_euind a_wex f0_euind f4_euind a_sup_set_class f5_euind a_wceq a_wi f2_euind a_wal f0_euind i0_euind a_sup_set_class f5_euind a_wceq a_wi f2_euind a_wal a_wa f4_euind a_sup_set_class i0_euind a_sup_set_class a_wceq a_wi i0_euind a_wal f4_euind a_wal f0_euind f1_euind a_wa f5_euind f6_euind a_wceq a_wi f3_euind a_wal f2_euind a_wal p_adantl f4_euind a_sup_set_class i0_euind a_sup_set_class f5_euind p_eqeq1 f4_euind a_sup_set_class i0_euind a_sup_set_class a_wceq f4_euind a_sup_set_class f5_euind a_wceq i0_euind a_sup_set_class f5_euind a_wceq f0_euind p_imbi2d f4_euind a_sup_set_class i0_euind a_sup_set_class a_wceq f0_euind f4_euind a_sup_set_class f5_euind a_wceq a_wi f0_euind i0_euind a_sup_set_class f5_euind a_wceq a_wi f2_euind p_albidv f0_euind f4_euind a_sup_set_class f5_euind a_wceq a_wi f2_euind a_wal f0_euind i0_euind a_sup_set_class f5_euind a_wceq a_wi f2_euind a_wal f4_euind i0_euind p_eu4 f0_euind f1_euind a_wa f5_euind f6_euind a_wceq a_wi f3_euind a_wal f2_euind a_wal f0_euind f2_euind a_wex a_wa f0_euind f4_euind a_sup_set_class f5_euind a_wceq a_wi f2_euind a_wal f4_euind a_wex f0_euind f4_euind a_sup_set_class f5_euind a_wceq a_wi f2_euind a_wal f0_euind i0_euind a_sup_set_class f5_euind a_wceq a_wi f2_euind a_wal a_wa f4_euind a_sup_set_class i0_euind a_sup_set_class a_wceq a_wi i0_euind a_wal f4_euind a_wal f0_euind f4_euind a_sup_set_class f5_euind a_wceq a_wi f2_euind a_wal f4_euind a_weu p_sylanbrc $.
$}

$(A way to express restricted uniqueness.  (Contributed by NM,
       22-Nov-1994.) $)

${
	$v ph x y A  $.
	$d x y A  $.
	$d x y  $.
	$d y ph  $.
	$d x  $.
	f0_reu2 $f wff ph $.
	f1_reu2 $f set x $.
	f2_reu2 $f set y $.
	f3_reu2 $f class A $.
	p_reu2 $p |- ( E! x e. A ph <-> ( E. x e. A ph /\ A. x e. A A. y e. A ( ( ph /\ [ y / x ] ph ) -> x = y ) ) ) $= f1_reu2 a_sup_set_class f3_reu2 a_wcel f0_reu2 a_wa f2_reu2 p_nfv f1_reu2 a_sup_set_class f3_reu2 a_wcel f0_reu2 a_wa f1_reu2 f2_reu2 p_eu2 f0_reu2 f1_reu2 f3_reu2 a_df-reu f0_reu2 f1_reu2 f3_reu2 a_df-rex f0_reu2 f0_reu2 f1_reu2 f2_reu2 a_wsb a_wa f1_reu2 a_sup_set_class f2_reu2 a_sup_set_class a_wceq a_wi f2_reu2 f3_reu2 a_wral f1_reu2 f3_reu2 a_df-ral f1_reu2 a_sup_set_class f3_reu2 a_wcel f2_reu2 a_sup_set_class f3_reu2 a_wcel f0_reu2 f0_reu2 f1_reu2 f2_reu2 a_wsb a_wa f1_reu2 a_sup_set_class f2_reu2 a_sup_set_class a_wceq a_wi a_wi f2_reu2 p_19.21v f2_reu2 a_sup_set_class f3_reu2 a_wcel f1_reu2 p_nfv f0_reu2 f1_reu2 f2_reu2 p_nfs1v f2_reu2 a_sup_set_class f3_reu2 a_wcel f0_reu2 f1_reu2 f2_reu2 a_wsb f1_reu2 p_nfan f1_reu2 a_sup_set_class f2_reu2 a_sup_set_class f3_reu2 p_eleq1 f0_reu2 f1_reu2 f2_reu2 p_sbequ12 f1_reu2 a_sup_set_class f2_reu2 a_sup_set_class a_wceq f1_reu2 a_sup_set_class f3_reu2 a_wcel f2_reu2 a_sup_set_class f3_reu2 a_wcel f0_reu2 f0_reu2 f1_reu2 f2_reu2 a_wsb p_anbi12d f1_reu2 a_sup_set_class f3_reu2 a_wcel f0_reu2 a_wa f2_reu2 a_sup_set_class f3_reu2 a_wcel f0_reu2 f1_reu2 f2_reu2 a_wsb a_wa f1_reu2 f2_reu2 p_sbie f1_reu2 a_sup_set_class f3_reu2 a_wcel f0_reu2 a_wa f1_reu2 f2_reu2 a_wsb f2_reu2 a_sup_set_class f3_reu2 a_wcel f0_reu2 f1_reu2 f2_reu2 a_wsb a_wa f1_reu2 a_sup_set_class f3_reu2 a_wcel f0_reu2 a_wa p_anbi2i f1_reu2 a_sup_set_class f3_reu2 a_wcel f0_reu2 f2_reu2 a_sup_set_class f3_reu2 a_wcel f0_reu2 f1_reu2 f2_reu2 a_wsb p_an4 f1_reu2 a_sup_set_class f3_reu2 a_wcel f0_reu2 a_wa f1_reu2 a_sup_set_class f3_reu2 a_wcel f0_reu2 a_wa f1_reu2 f2_reu2 a_wsb a_wa f1_reu2 a_sup_set_class f3_reu2 a_wcel f0_reu2 a_wa f2_reu2 a_sup_set_class f3_reu2 a_wcel f0_reu2 f1_reu2 f2_reu2 a_wsb a_wa a_wa f1_reu2 a_sup_set_class f3_reu2 a_wcel f2_reu2 a_sup_set_class f3_reu2 a_wcel a_wa f0_reu2 f0_reu2 f1_reu2 f2_reu2 a_wsb a_wa a_wa p_bitri f1_reu2 a_sup_set_class f3_reu2 a_wcel f0_reu2 a_wa f1_reu2 a_sup_set_class f3_reu2 a_wcel f0_reu2 a_wa f1_reu2 f2_reu2 a_wsb a_wa f1_reu2 a_sup_set_class f3_reu2 a_wcel f2_reu2 a_sup_set_class f3_reu2 a_wcel a_wa f0_reu2 f0_reu2 f1_reu2 f2_reu2 a_wsb a_wa a_wa f1_reu2 a_sup_set_class f2_reu2 a_sup_set_class a_wceq p_imbi1i f1_reu2 a_sup_set_class f3_reu2 a_wcel f2_reu2 a_sup_set_class f3_reu2 a_wcel a_wa f0_reu2 f0_reu2 f1_reu2 f2_reu2 a_wsb a_wa f1_reu2 a_sup_set_class f2_reu2 a_sup_set_class a_wceq p_impexp f1_reu2 a_sup_set_class f3_reu2 a_wcel f2_reu2 a_sup_set_class f3_reu2 a_wcel f0_reu2 f0_reu2 f1_reu2 f2_reu2 a_wsb a_wa f1_reu2 a_sup_set_class f2_reu2 a_sup_set_class a_wceq a_wi p_impexp f1_reu2 a_sup_set_class f3_reu2 a_wcel f0_reu2 a_wa f1_reu2 a_sup_set_class f3_reu2 a_wcel f0_reu2 a_wa f1_reu2 f2_reu2 a_wsb a_wa f1_reu2 a_sup_set_class f2_reu2 a_sup_set_class a_wceq a_wi f1_reu2 a_sup_set_class f3_reu2 a_wcel f2_reu2 a_sup_set_class f3_reu2 a_wcel a_wa f0_reu2 f0_reu2 f1_reu2 f2_reu2 a_wsb a_wa a_wa f1_reu2 a_sup_set_class f2_reu2 a_sup_set_class a_wceq a_wi f1_reu2 a_sup_set_class f3_reu2 a_wcel f2_reu2 a_sup_set_class f3_reu2 a_wcel a_wa f0_reu2 f0_reu2 f1_reu2 f2_reu2 a_wsb a_wa f1_reu2 a_sup_set_class f2_reu2 a_sup_set_class a_wceq a_wi a_wi f1_reu2 a_sup_set_class f3_reu2 a_wcel f2_reu2 a_sup_set_class f3_reu2 a_wcel f0_reu2 f0_reu2 f1_reu2 f2_reu2 a_wsb a_wa f1_reu2 a_sup_set_class f2_reu2 a_sup_set_class a_wceq a_wi a_wi a_wi p_3bitri f1_reu2 a_sup_set_class f3_reu2 a_wcel f0_reu2 a_wa f1_reu2 a_sup_set_class f3_reu2 a_wcel f0_reu2 a_wa f1_reu2 f2_reu2 a_wsb a_wa f1_reu2 a_sup_set_class f2_reu2 a_sup_set_class a_wceq a_wi f1_reu2 a_sup_set_class f3_reu2 a_wcel f2_reu2 a_sup_set_class f3_reu2 a_wcel f0_reu2 f0_reu2 f1_reu2 f2_reu2 a_wsb a_wa f1_reu2 a_sup_set_class f2_reu2 a_sup_set_class a_wceq a_wi a_wi a_wi f2_reu2 p_albii f0_reu2 f0_reu2 f1_reu2 f2_reu2 a_wsb a_wa f1_reu2 a_sup_set_class f2_reu2 a_sup_set_class a_wceq a_wi f2_reu2 f3_reu2 a_df-ral f0_reu2 f0_reu2 f1_reu2 f2_reu2 a_wsb a_wa f1_reu2 a_sup_set_class f2_reu2 a_sup_set_class a_wceq a_wi f2_reu2 f3_reu2 a_wral f2_reu2 a_sup_set_class f3_reu2 a_wcel f0_reu2 f0_reu2 f1_reu2 f2_reu2 a_wsb a_wa f1_reu2 a_sup_set_class f2_reu2 a_sup_set_class a_wceq a_wi a_wi f2_reu2 a_wal f1_reu2 a_sup_set_class f3_reu2 a_wcel p_imbi2i f1_reu2 a_sup_set_class f3_reu2 a_wcel f2_reu2 a_sup_set_class f3_reu2 a_wcel f0_reu2 f0_reu2 f1_reu2 f2_reu2 a_wsb a_wa f1_reu2 a_sup_set_class f2_reu2 a_sup_set_class a_wceq a_wi a_wi a_wi f2_reu2 a_wal f1_reu2 a_sup_set_class f3_reu2 a_wcel f2_reu2 a_sup_set_class f3_reu2 a_wcel f0_reu2 f0_reu2 f1_reu2 f2_reu2 a_wsb a_wa f1_reu2 a_sup_set_class f2_reu2 a_sup_set_class a_wceq a_wi a_wi f2_reu2 a_wal a_wi f1_reu2 a_sup_set_class f3_reu2 a_wcel f0_reu2 a_wa f1_reu2 a_sup_set_class f3_reu2 a_wcel f0_reu2 a_wa f1_reu2 f2_reu2 a_wsb a_wa f1_reu2 a_sup_set_class f2_reu2 a_sup_set_class a_wceq a_wi f2_reu2 a_wal f1_reu2 a_sup_set_class f3_reu2 a_wcel f0_reu2 f0_reu2 f1_reu2 f2_reu2 a_wsb a_wa f1_reu2 a_sup_set_class f2_reu2 a_sup_set_class a_wceq a_wi f2_reu2 f3_reu2 a_wral a_wi p_3bitr4i f1_reu2 a_sup_set_class f3_reu2 a_wcel f0_reu2 a_wa f1_reu2 a_sup_set_class f3_reu2 a_wcel f0_reu2 a_wa f1_reu2 f2_reu2 a_wsb a_wa f1_reu2 a_sup_set_class f2_reu2 a_sup_set_class a_wceq a_wi f2_reu2 a_wal f1_reu2 a_sup_set_class f3_reu2 a_wcel f0_reu2 f0_reu2 f1_reu2 f2_reu2 a_wsb a_wa f1_reu2 a_sup_set_class f2_reu2 a_sup_set_class a_wceq a_wi f2_reu2 f3_reu2 a_wral a_wi f1_reu2 p_albii f0_reu2 f0_reu2 f1_reu2 f2_reu2 a_wsb a_wa f1_reu2 a_sup_set_class f2_reu2 a_sup_set_class a_wceq a_wi f2_reu2 f3_reu2 a_wral f1_reu2 f3_reu2 a_wral f1_reu2 a_sup_set_class f3_reu2 a_wcel f0_reu2 f0_reu2 f1_reu2 f2_reu2 a_wsb a_wa f1_reu2 a_sup_set_class f2_reu2 a_sup_set_class a_wceq a_wi f2_reu2 f3_reu2 a_wral a_wi f1_reu2 a_wal f1_reu2 a_sup_set_class f3_reu2 a_wcel f0_reu2 a_wa f1_reu2 a_sup_set_class f3_reu2 a_wcel f0_reu2 a_wa f1_reu2 f2_reu2 a_wsb a_wa f1_reu2 a_sup_set_class f2_reu2 a_sup_set_class a_wceq a_wi f2_reu2 a_wal f1_reu2 a_wal p_bitr4i f0_reu2 f1_reu2 f3_reu2 a_wrex f1_reu2 a_sup_set_class f3_reu2 a_wcel f0_reu2 a_wa f1_reu2 a_wex f0_reu2 f0_reu2 f1_reu2 f2_reu2 a_wsb a_wa f1_reu2 a_sup_set_class f2_reu2 a_sup_set_class a_wceq a_wi f2_reu2 f3_reu2 a_wral f1_reu2 f3_reu2 a_wral f1_reu2 a_sup_set_class f3_reu2 a_wcel f0_reu2 a_wa f1_reu2 a_sup_set_class f3_reu2 a_wcel f0_reu2 a_wa f1_reu2 f2_reu2 a_wsb a_wa f1_reu2 a_sup_set_class f2_reu2 a_sup_set_class a_wceq a_wi f2_reu2 a_wal f1_reu2 a_wal p_anbi12i f1_reu2 a_sup_set_class f3_reu2 a_wcel f0_reu2 a_wa f1_reu2 a_weu f1_reu2 a_sup_set_class f3_reu2 a_wcel f0_reu2 a_wa f1_reu2 a_wex f1_reu2 a_sup_set_class f3_reu2 a_wcel f0_reu2 a_wa f1_reu2 a_sup_set_class f3_reu2 a_wcel f0_reu2 a_wa f1_reu2 f2_reu2 a_wsb a_wa f1_reu2 a_sup_set_class f2_reu2 a_sup_set_class a_wceq a_wi f2_reu2 a_wal f1_reu2 a_wal a_wa f0_reu2 f1_reu2 f3_reu2 a_wreu f0_reu2 f1_reu2 f3_reu2 a_wrex f0_reu2 f0_reu2 f1_reu2 f2_reu2 a_wsb a_wa f1_reu2 a_sup_set_class f2_reu2 a_sup_set_class a_wceq a_wi f2_reu2 f3_reu2 a_wral f1_reu2 f3_reu2 a_wral a_wa p_3bitr4i $.
$}

$(A way to express restricted uniqueness.  (Contributed by NM,
       20-Oct-2006.) $)

${
	$v ph x y A  $.
	$d x y A  $.
	$d x y  $.
	$d y ph  $.
	$d x  $.
	f0_reu6 $f wff ph $.
	f1_reu6 $f set x $.
	f2_reu6 $f set y $.
	f3_reu6 $f class A $.
	p_reu6 $p |- ( E! x e. A ph <-> E. y e. A A. x e. A ( ph <-> x = y ) ) $= f0_reu6 f1_reu6 f3_reu6 a_df-reu f2_reu6 a_sup_set_class f3_reu6 a_wcel f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wb a_wi f1_reu6 p_19.28v f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class f3_reu6 p_eleq1 f0_reu6 f1_reu6 f2_reu6 p_sbequ12 f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq f1_reu6 a_sup_set_class f3_reu6 a_wcel f2_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 f0_reu6 f1_reu6 f2_reu6 a_wsb p_anbi12d f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class f2_reu6 a_sup_set_class p_eqeq1 f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 a_wa f2_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 f1_reu6 f2_reu6 a_wsb a_wa f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq f2_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq p_bibi12d f2_reu6 a_sup_set_class p_eqid f2_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq f2_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 f1_reu6 f2_reu6 a_wsb a_wa p_tbt f2_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 f1_reu6 f2_reu6 a_wsb p_simpl f2_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 f1_reu6 f2_reu6 a_wsb a_wa f2_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wb f2_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 f1_reu6 f2_reu6 a_wsb a_wa f2_reu6 a_sup_set_class f3_reu6 a_wcel p_sylbir f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 a_wa f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wb f2_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 f1_reu6 f2_reu6 a_wsb a_wa f2_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wb f2_reu6 a_sup_set_class f3_reu6 a_wcel p_syl6bi f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 a_wa f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wb f2_reu6 a_sup_set_class f3_reu6 a_wcel f1_reu6 f2_reu6 p_spimv f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 a_wa f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq p_bi1 f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 a_wa f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wb f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq p_expdimp f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 a_wa f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq p_bi2 f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 p_simpr f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 a_wa f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wb f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 a_wa f0_reu6 p_syl6 f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 a_wa f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wb f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq f0_reu6 a_wi f1_reu6 a_sup_set_class f3_reu6 a_wcel p_adantr f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 a_wa f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wb f1_reu6 a_sup_set_class f3_reu6 a_wcel a_wa f0_reu6 f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq p_impbid f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 a_wa f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wb f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wb p_ex f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 a_wa f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wb f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wb a_wi f1_reu6 p_sps f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 a_wa f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wb f1_reu6 a_wal f2_reu6 a_sup_set_class f3_reu6 a_wcel f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wb a_wi p_jca f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 a_wa f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wb f2_reu6 a_sup_set_class f3_reu6 a_wcel f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wb a_wi a_wa f1_reu6 p_a5i f0_reu6 f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq p_bi1 f0_reu6 f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wb f0_reu6 f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wi f1_reu6 a_sup_set_class f3_reu6 a_wcel p_imim2i f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wb a_wi f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq p_imp3a f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wb a_wi f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 a_wa f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wi f2_reu6 a_sup_set_class f3_reu6 a_wcel p_adantl f2_reu6 a_sup_set_class f3_reu6 f1_reu6 a_sup_set_class p_eleq1a f2_reu6 a_sup_set_class f3_reu6 a_wcel f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq f1_reu6 a_sup_set_class f3_reu6 a_wcel a_wi f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wb a_wi p_adantr f2_reu6 a_sup_set_class f3_reu6 a_wcel f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wb a_wi a_wa f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq f1_reu6 a_sup_set_class f3_reu6 a_wcel p_imp f0_reu6 f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq p_bi2 f0_reu6 f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wb f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq f0_reu6 a_wi f1_reu6 a_sup_set_class f3_reu6 a_wcel p_imim2i f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wb a_wi f1_reu6 a_sup_set_class f3_reu6 a_wcel f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq f0_reu6 p_com23 f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wb a_wi f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 a_wi p_imp f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wb a_wi f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 a_wi f2_reu6 a_sup_set_class f3_reu6 a_wcel p_adantll f2_reu6 a_sup_set_class f3_reu6 a_wcel f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wb a_wi a_wa f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wa f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 p_jcai f2_reu6 a_sup_set_class f3_reu6 a_wcel f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wb a_wi a_wa f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 a_wa p_ex f2_reu6 a_sup_set_class f3_reu6 a_wcel f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wb a_wi a_wa f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 a_wa f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq p_impbid f2_reu6 a_sup_set_class f3_reu6 a_wcel f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wb a_wi a_wa f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 a_wa f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wb f1_reu6 p_alimi f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 a_wa f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wb f1_reu6 a_wal f2_reu6 a_sup_set_class f3_reu6 a_wcel f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wb a_wi a_wa f1_reu6 a_wal p_impbii f0_reu6 f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wb f1_reu6 f3_reu6 a_df-ral f0_reu6 f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wb f1_reu6 f3_reu6 a_wral f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wb a_wi f1_reu6 a_wal f2_reu6 a_sup_set_class f3_reu6 a_wcel p_anbi2i f2_reu6 a_sup_set_class f3_reu6 a_wcel f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wb a_wi a_wa f1_reu6 a_wal f2_reu6 a_sup_set_class f3_reu6 a_wcel f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wb a_wi f1_reu6 a_wal a_wa f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 a_wa f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wb f1_reu6 a_wal f2_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wb f1_reu6 f3_reu6 a_wral a_wa p_3bitr4i f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 a_wa f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wb f1_reu6 a_wal f2_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wb f1_reu6 f3_reu6 a_wral a_wa f2_reu6 p_exbii f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 a_wa f1_reu6 f2_reu6 a_df-eu f0_reu6 f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wb f1_reu6 f3_reu6 a_wral f2_reu6 f3_reu6 a_df-rex f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 a_wa f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wb f1_reu6 a_wal f2_reu6 a_wex f2_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wb f1_reu6 f3_reu6 a_wral a_wa f2_reu6 a_wex f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 a_wa f1_reu6 a_weu f0_reu6 f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wb f1_reu6 f3_reu6 a_wral f2_reu6 f3_reu6 a_wrex p_3bitr4i f0_reu6 f1_reu6 f3_reu6 a_wreu f1_reu6 a_sup_set_class f3_reu6 a_wcel f0_reu6 a_wa f1_reu6 a_weu f0_reu6 f1_reu6 a_sup_set_class f2_reu6 a_sup_set_class a_wceq a_wb f1_reu6 f3_reu6 a_wral f2_reu6 f3_reu6 a_wrex p_bitri $.
$}

$(A way to express restricted uniqueness.  (Contributed by NM,
       24-Oct-2006.) $)

${
	$v ph x y A  $.
	$d x y A  $.
	$d x y  $.
	$d y ph  $.
	$d x  $.
	f0_reu3 $f wff ph $.
	f1_reu3 $f set x $.
	f2_reu3 $f set y $.
	f3_reu3 $f class A $.
	p_reu3 $p |- ( E! x e. A ph <-> ( E. x e. A ph /\ E. y e. A A. x e. A ( ph -> x = y ) ) ) $= f0_reu3 f1_reu3 f3_reu3 p_reurex f0_reu3 f1_reu3 f2_reu3 f3_reu3 p_reu6 f0_reu3 f1_reu3 a_sup_set_class f2_reu3 a_sup_set_class a_wceq p_bi1 f0_reu3 f1_reu3 a_sup_set_class f2_reu3 a_sup_set_class a_wceq a_wb f0_reu3 f1_reu3 a_sup_set_class f2_reu3 a_sup_set_class a_wceq a_wi f1_reu3 f3_reu3 p_ralimi f0_reu3 f1_reu3 a_sup_set_class f2_reu3 a_sup_set_class a_wceq a_wb f1_reu3 f3_reu3 a_wral f0_reu3 f1_reu3 a_sup_set_class f2_reu3 a_sup_set_class a_wceq a_wi f1_reu3 f3_reu3 a_wral f2_reu3 f3_reu3 p_reximi f0_reu3 f1_reu3 f3_reu3 a_wreu f0_reu3 f1_reu3 a_sup_set_class f2_reu3 a_sup_set_class a_wceq a_wb f1_reu3 f3_reu3 a_wral f2_reu3 f3_reu3 a_wrex f0_reu3 f1_reu3 a_sup_set_class f2_reu3 a_sup_set_class a_wceq a_wi f1_reu3 f3_reu3 a_wral f2_reu3 f3_reu3 a_wrex p_sylbi f0_reu3 f1_reu3 f3_reu3 a_wreu f0_reu3 f1_reu3 f3_reu3 a_wrex f0_reu3 f1_reu3 a_sup_set_class f2_reu3 a_sup_set_class a_wceq a_wi f1_reu3 f3_reu3 a_wral f2_reu3 f3_reu3 a_wrex p_jca f0_reu3 f1_reu3 a_sup_set_class f2_reu3 a_sup_set_class a_wceq a_wi f1_reu3 f3_reu3 a_wral f2_reu3 f3_reu3 p_rexex f0_reu3 f1_reu3 a_sup_set_class f2_reu3 a_sup_set_class a_wceq a_wi f1_reu3 f3_reu3 a_wral f2_reu3 f3_reu3 a_wrex f0_reu3 f1_reu3 a_sup_set_class f2_reu3 a_sup_set_class a_wceq a_wi f1_reu3 f3_reu3 a_wral f2_reu3 a_wex f0_reu3 f1_reu3 f3_reu3 a_wrex p_anim2i f1_reu3 a_sup_set_class f3_reu3 a_wcel f0_reu3 a_wa f2_reu3 p_nfv f1_reu3 a_sup_set_class f3_reu3 a_wcel f0_reu3 a_wa f1_reu3 f2_reu3 p_eu3 f0_reu3 f1_reu3 f3_reu3 a_df-reu f0_reu3 f1_reu3 f3_reu3 a_df-rex f0_reu3 f1_reu3 a_sup_set_class f2_reu3 a_sup_set_class a_wceq a_wi f1_reu3 f3_reu3 a_df-ral f1_reu3 a_sup_set_class f3_reu3 a_wcel f0_reu3 f1_reu3 a_sup_set_class f2_reu3 a_sup_set_class a_wceq p_impexp f1_reu3 a_sup_set_class f3_reu3 a_wcel f0_reu3 a_wa f1_reu3 a_sup_set_class f2_reu3 a_sup_set_class a_wceq a_wi f1_reu3 a_sup_set_class f3_reu3 a_wcel f0_reu3 f1_reu3 a_sup_set_class f2_reu3 a_sup_set_class a_wceq a_wi a_wi f1_reu3 p_albii f0_reu3 f1_reu3 a_sup_set_class f2_reu3 a_sup_set_class a_wceq a_wi f1_reu3 f3_reu3 a_wral f1_reu3 a_sup_set_class f3_reu3 a_wcel f0_reu3 f1_reu3 a_sup_set_class f2_reu3 a_sup_set_class a_wceq a_wi a_wi f1_reu3 a_wal f1_reu3 a_sup_set_class f3_reu3 a_wcel f0_reu3 a_wa f1_reu3 a_sup_set_class f2_reu3 a_sup_set_class a_wceq a_wi f1_reu3 a_wal p_bitr4i f0_reu3 f1_reu3 a_sup_set_class f2_reu3 a_sup_set_class a_wceq a_wi f1_reu3 f3_reu3 a_wral f1_reu3 a_sup_set_class f3_reu3 a_wcel f0_reu3 a_wa f1_reu3 a_sup_set_class f2_reu3 a_sup_set_class a_wceq a_wi f1_reu3 a_wal f2_reu3 p_exbii f0_reu3 f1_reu3 f3_reu3 a_wrex f1_reu3 a_sup_set_class f3_reu3 a_wcel f0_reu3 a_wa f1_reu3 a_wex f0_reu3 f1_reu3 a_sup_set_class f2_reu3 a_sup_set_class a_wceq a_wi f1_reu3 f3_reu3 a_wral f2_reu3 a_wex f1_reu3 a_sup_set_class f3_reu3 a_wcel f0_reu3 a_wa f1_reu3 a_sup_set_class f2_reu3 a_sup_set_class a_wceq a_wi f1_reu3 a_wal f2_reu3 a_wex p_anbi12i f1_reu3 a_sup_set_class f3_reu3 a_wcel f0_reu3 a_wa f1_reu3 a_weu f1_reu3 a_sup_set_class f3_reu3 a_wcel f0_reu3 a_wa f1_reu3 a_wex f1_reu3 a_sup_set_class f3_reu3 a_wcel f0_reu3 a_wa f1_reu3 a_sup_set_class f2_reu3 a_sup_set_class a_wceq a_wi f1_reu3 a_wal f2_reu3 a_wex a_wa f0_reu3 f1_reu3 f3_reu3 a_wreu f0_reu3 f1_reu3 f3_reu3 a_wrex f0_reu3 f1_reu3 a_sup_set_class f2_reu3 a_sup_set_class a_wceq a_wi f1_reu3 f3_reu3 a_wral f2_reu3 a_wex a_wa p_3bitr4i f0_reu3 f1_reu3 f3_reu3 a_wrex f0_reu3 f1_reu3 a_sup_set_class f2_reu3 a_sup_set_class a_wceq a_wi f1_reu3 f3_reu3 a_wral f2_reu3 f3_reu3 a_wrex a_wa f0_reu3 f1_reu3 f3_reu3 a_wrex f0_reu3 f1_reu3 a_sup_set_class f2_reu3 a_sup_set_class a_wceq a_wi f1_reu3 f3_reu3 a_wral f2_reu3 a_wex a_wa f0_reu3 f1_reu3 f3_reu3 a_wreu p_sylibr f0_reu3 f1_reu3 f3_reu3 a_wreu f0_reu3 f1_reu3 f3_reu3 a_wrex f0_reu3 f1_reu3 a_sup_set_class f2_reu3 a_sup_set_class a_wceq a_wi f1_reu3 f3_reu3 a_wral f2_reu3 f3_reu3 a_wrex a_wa p_impbii $.
$}

$(A condition which implies existential uniqueness.  (Contributed by Mario
       Carneiro, 2-Oct-2015.) $)

${
	$v ph x A B  $.
	$d x y A  $.
	$d x y B  $.
	$d y ph  $.
	$d x  $.
	f0_reu6i $f wff ph $.
	f1_reu6i $f set x $.
	f2_reu6i $f class A $.
	f3_reu6i $f class B $.
	i0_reu6i $f set y $.
	p_reu6i $p |- ( ( B e. A /\ A. x e. A ( ph <-> x = B ) ) -> E! x e. A ph ) $= i0_reu6i a_sup_set_class f3_reu6i f1_reu6i a_sup_set_class p_eqeq2 i0_reu6i a_sup_set_class f3_reu6i a_wceq f1_reu6i a_sup_set_class i0_reu6i a_sup_set_class a_wceq f1_reu6i a_sup_set_class f3_reu6i a_wceq f0_reu6i p_bibi2d i0_reu6i a_sup_set_class f3_reu6i a_wceq f0_reu6i f1_reu6i a_sup_set_class i0_reu6i a_sup_set_class a_wceq a_wb f0_reu6i f1_reu6i a_sup_set_class f3_reu6i a_wceq a_wb f1_reu6i f2_reu6i p_ralbidv f0_reu6i f1_reu6i a_sup_set_class i0_reu6i a_sup_set_class a_wceq a_wb f1_reu6i f2_reu6i a_wral f0_reu6i f1_reu6i a_sup_set_class f3_reu6i a_wceq a_wb f1_reu6i f2_reu6i a_wral i0_reu6i f3_reu6i f2_reu6i p_rspcev f0_reu6i f1_reu6i i0_reu6i f2_reu6i p_reu6 f3_reu6i f2_reu6i a_wcel f0_reu6i f1_reu6i a_sup_set_class f3_reu6i a_wceq a_wb f1_reu6i f2_reu6i a_wral a_wa f0_reu6i f1_reu6i a_sup_set_class i0_reu6i a_sup_set_class a_wceq a_wb f1_reu6i f2_reu6i a_wral i0_reu6i f2_reu6i a_wrex f0_reu6i f1_reu6i f2_reu6i a_wreu p_sylibr $.
$}

$(A condition which implies existential uniqueness.  (Contributed by Mario
       Carneiro, 2-Oct-2015.) $)

${
	$v ph ps x A B  $.
	$d x A  $.
	$d x B  $.
	$d ph  $.
	$d x ps  $.
	f0_eqreu $f wff ph $.
	f1_eqreu $f wff ps $.
	f2_eqreu $f set x $.
	f3_eqreu $f class A $.
	f4_eqreu $f class B $.
	e0_eqreu $e |- ( x = B -> ( ph <-> ps ) ) $.
	p_eqreu $p |- ( ( B e. A /\ ps /\ A. x e. A ( ph -> x = B ) ) -> E! x e. A ph ) $= f0_eqreu f2_eqreu a_sup_set_class f4_eqreu a_wceq f2_eqreu f3_eqreu p_ralbiim e0_eqreu f0_eqreu f1_eqreu f2_eqreu f4_eqreu f3_eqreu p_ceqsralv f4_eqreu f3_eqreu a_wcel f2_eqreu a_sup_set_class f4_eqreu a_wceq f0_eqreu a_wi f2_eqreu f3_eqreu a_wral f1_eqreu f0_eqreu f2_eqreu a_sup_set_class f4_eqreu a_wceq a_wi f2_eqreu f3_eqreu a_wral p_anbi2d f0_eqreu f2_eqreu a_sup_set_class f4_eqreu a_wceq a_wb f2_eqreu f3_eqreu a_wral f0_eqreu f2_eqreu a_sup_set_class f4_eqreu a_wceq a_wi f2_eqreu f3_eqreu a_wral f2_eqreu a_sup_set_class f4_eqreu a_wceq f0_eqreu a_wi f2_eqreu f3_eqreu a_wral a_wa f4_eqreu f3_eqreu a_wcel f0_eqreu f2_eqreu a_sup_set_class f4_eqreu a_wceq a_wi f2_eqreu f3_eqreu a_wral f1_eqreu a_wa p_syl5bb f0_eqreu f2_eqreu f3_eqreu f4_eqreu p_reu6i f4_eqreu f3_eqreu a_wcel f0_eqreu f2_eqreu a_sup_set_class f4_eqreu a_wceq a_wb f2_eqreu f3_eqreu a_wral f0_eqreu f2_eqreu f3_eqreu a_wreu p_ex f4_eqreu f3_eqreu a_wcel f0_eqreu f2_eqreu a_sup_set_class f4_eqreu a_wceq a_wi f2_eqreu f3_eqreu a_wral f1_eqreu a_wa f0_eqreu f2_eqreu a_sup_set_class f4_eqreu a_wceq a_wb f2_eqreu f3_eqreu a_wral f0_eqreu f2_eqreu f3_eqreu a_wreu p_sylbird f4_eqreu f3_eqreu a_wcel f0_eqreu f2_eqreu a_sup_set_class f4_eqreu a_wceq a_wi f2_eqreu f3_eqreu a_wral f1_eqreu f0_eqreu f2_eqreu f3_eqreu a_wreu p_3impib f4_eqreu f3_eqreu a_wcel f0_eqreu f2_eqreu a_sup_set_class f4_eqreu a_wceq a_wi f2_eqreu f3_eqreu a_wral f1_eqreu f0_eqreu f2_eqreu f3_eqreu a_wreu p_3com23 $.
$}

$(Restricted "at most one" using implicit substitution.  (Contributed by
       NM, 24-Oct-2006.)  (Revised by NM, 16-Jun-2017.) $)

${
	$v ph ps x y A  $.
	$d x y A  $.
	$d y ph  $.
	$d x ps  $.
	f0_rmo4 $f wff ph $.
	f1_rmo4 $f wff ps $.
	f2_rmo4 $f set x $.
	f3_rmo4 $f set y $.
	f4_rmo4 $f class A $.
	e0_rmo4 $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_rmo4 $p |- ( E* x e. A ph <-> A. x e. A A. y e. A ( ( ph /\ ps ) -> x = y ) ) $= f0_rmo4 f2_rmo4 f4_rmo4 a_df-rmo f2_rmo4 a_sup_set_class f4_rmo4 a_wcel f0_rmo4 f3_rmo4 a_sup_set_class f4_rmo4 a_wcel f1_rmo4 p_an4 f2_rmo4 a_sup_set_class f4_rmo4 a_wcel f3_rmo4 a_sup_set_class f4_rmo4 a_wcel p_ancom f2_rmo4 a_sup_set_class f4_rmo4 a_wcel f3_rmo4 a_sup_set_class f4_rmo4 a_wcel a_wa f3_rmo4 a_sup_set_class f4_rmo4 a_wcel f2_rmo4 a_sup_set_class f4_rmo4 a_wcel a_wa f0_rmo4 f1_rmo4 a_wa p_anbi1i f2_rmo4 a_sup_set_class f4_rmo4 a_wcel f0_rmo4 a_wa f3_rmo4 a_sup_set_class f4_rmo4 a_wcel f1_rmo4 a_wa a_wa f2_rmo4 a_sup_set_class f4_rmo4 a_wcel f3_rmo4 a_sup_set_class f4_rmo4 a_wcel a_wa f0_rmo4 f1_rmo4 a_wa a_wa f3_rmo4 a_sup_set_class f4_rmo4 a_wcel f2_rmo4 a_sup_set_class f4_rmo4 a_wcel a_wa f0_rmo4 f1_rmo4 a_wa a_wa p_bitri f2_rmo4 a_sup_set_class f4_rmo4 a_wcel f0_rmo4 a_wa f3_rmo4 a_sup_set_class f4_rmo4 a_wcel f1_rmo4 a_wa a_wa f3_rmo4 a_sup_set_class f4_rmo4 a_wcel f2_rmo4 a_sup_set_class f4_rmo4 a_wcel a_wa f0_rmo4 f1_rmo4 a_wa a_wa f2_rmo4 a_sup_set_class f3_rmo4 a_sup_set_class a_wceq p_imbi1i f3_rmo4 a_sup_set_class f4_rmo4 a_wcel f2_rmo4 a_sup_set_class f4_rmo4 a_wcel a_wa f0_rmo4 f1_rmo4 a_wa f2_rmo4 a_sup_set_class f3_rmo4 a_sup_set_class a_wceq p_impexp f3_rmo4 a_sup_set_class f4_rmo4 a_wcel f2_rmo4 a_sup_set_class f4_rmo4 a_wcel f0_rmo4 f1_rmo4 a_wa f2_rmo4 a_sup_set_class f3_rmo4 a_sup_set_class a_wceq a_wi p_impexp f2_rmo4 a_sup_set_class f4_rmo4 a_wcel f0_rmo4 a_wa f3_rmo4 a_sup_set_class f4_rmo4 a_wcel f1_rmo4 a_wa a_wa f2_rmo4 a_sup_set_class f3_rmo4 a_sup_set_class a_wceq a_wi f3_rmo4 a_sup_set_class f4_rmo4 a_wcel f2_rmo4 a_sup_set_class f4_rmo4 a_wcel a_wa f0_rmo4 f1_rmo4 a_wa a_wa f2_rmo4 a_sup_set_class f3_rmo4 a_sup_set_class a_wceq a_wi f3_rmo4 a_sup_set_class f4_rmo4 a_wcel f2_rmo4 a_sup_set_class f4_rmo4 a_wcel a_wa f0_rmo4 f1_rmo4 a_wa f2_rmo4 a_sup_set_class f3_rmo4 a_sup_set_class a_wceq a_wi a_wi f3_rmo4 a_sup_set_class f4_rmo4 a_wcel f2_rmo4 a_sup_set_class f4_rmo4 a_wcel f0_rmo4 f1_rmo4 a_wa f2_rmo4 a_sup_set_class f3_rmo4 a_sup_set_class a_wceq a_wi a_wi a_wi p_3bitri f2_rmo4 a_sup_set_class f4_rmo4 a_wcel f0_rmo4 a_wa f3_rmo4 a_sup_set_class f4_rmo4 a_wcel f1_rmo4 a_wa a_wa f2_rmo4 a_sup_set_class f3_rmo4 a_sup_set_class a_wceq a_wi f3_rmo4 a_sup_set_class f4_rmo4 a_wcel f2_rmo4 a_sup_set_class f4_rmo4 a_wcel f0_rmo4 f1_rmo4 a_wa f2_rmo4 a_sup_set_class f3_rmo4 a_sup_set_class a_wceq a_wi a_wi a_wi f3_rmo4 p_albii f2_rmo4 a_sup_set_class f4_rmo4 a_wcel f0_rmo4 f1_rmo4 a_wa f2_rmo4 a_sup_set_class f3_rmo4 a_sup_set_class a_wceq a_wi a_wi f3_rmo4 f4_rmo4 a_df-ral f2_rmo4 a_sup_set_class f4_rmo4 a_wcel f0_rmo4 f1_rmo4 a_wa f2_rmo4 a_sup_set_class f3_rmo4 a_sup_set_class a_wceq a_wi f3_rmo4 f4_rmo4 p_r19.21v f2_rmo4 a_sup_set_class f4_rmo4 a_wcel f0_rmo4 a_wa f3_rmo4 a_sup_set_class f4_rmo4 a_wcel f1_rmo4 a_wa a_wa f2_rmo4 a_sup_set_class f3_rmo4 a_sup_set_class a_wceq a_wi f3_rmo4 a_wal f3_rmo4 a_sup_set_class f4_rmo4 a_wcel f2_rmo4 a_sup_set_class f4_rmo4 a_wcel f0_rmo4 f1_rmo4 a_wa f2_rmo4 a_sup_set_class f3_rmo4 a_sup_set_class a_wceq a_wi a_wi a_wi f3_rmo4 a_wal f2_rmo4 a_sup_set_class f4_rmo4 a_wcel f0_rmo4 f1_rmo4 a_wa f2_rmo4 a_sup_set_class f3_rmo4 a_sup_set_class a_wceq a_wi a_wi f3_rmo4 f4_rmo4 a_wral f2_rmo4 a_sup_set_class f4_rmo4 a_wcel f0_rmo4 f1_rmo4 a_wa f2_rmo4 a_sup_set_class f3_rmo4 a_sup_set_class a_wceq a_wi f3_rmo4 f4_rmo4 a_wral a_wi p_3bitr2i f2_rmo4 a_sup_set_class f4_rmo4 a_wcel f0_rmo4 a_wa f3_rmo4 a_sup_set_class f4_rmo4 a_wcel f1_rmo4 a_wa a_wa f2_rmo4 a_sup_set_class f3_rmo4 a_sup_set_class a_wceq a_wi f3_rmo4 a_wal f2_rmo4 a_sup_set_class f4_rmo4 a_wcel f0_rmo4 f1_rmo4 a_wa f2_rmo4 a_sup_set_class f3_rmo4 a_sup_set_class a_wceq a_wi f3_rmo4 f4_rmo4 a_wral a_wi f2_rmo4 p_albii f2_rmo4 a_sup_set_class f3_rmo4 a_sup_set_class f4_rmo4 p_eleq1 e0_rmo4 f2_rmo4 a_sup_set_class f3_rmo4 a_sup_set_class a_wceq f2_rmo4 a_sup_set_class f4_rmo4 a_wcel f3_rmo4 a_sup_set_class f4_rmo4 a_wcel f0_rmo4 f1_rmo4 p_anbi12d f2_rmo4 a_sup_set_class f4_rmo4 a_wcel f0_rmo4 a_wa f3_rmo4 a_sup_set_class f4_rmo4 a_wcel f1_rmo4 a_wa f2_rmo4 f3_rmo4 p_mo4 f0_rmo4 f1_rmo4 a_wa f2_rmo4 a_sup_set_class f3_rmo4 a_sup_set_class a_wceq a_wi f3_rmo4 f4_rmo4 a_wral f2_rmo4 f4_rmo4 a_df-ral f2_rmo4 a_sup_set_class f4_rmo4 a_wcel f0_rmo4 a_wa f3_rmo4 a_sup_set_class f4_rmo4 a_wcel f1_rmo4 a_wa a_wa f2_rmo4 a_sup_set_class f3_rmo4 a_sup_set_class a_wceq a_wi f3_rmo4 a_wal f2_rmo4 a_wal f2_rmo4 a_sup_set_class f4_rmo4 a_wcel f0_rmo4 f1_rmo4 a_wa f2_rmo4 a_sup_set_class f3_rmo4 a_sup_set_class a_wceq a_wi f3_rmo4 f4_rmo4 a_wral a_wi f2_rmo4 a_wal f2_rmo4 a_sup_set_class f4_rmo4 a_wcel f0_rmo4 a_wa f2_rmo4 a_wmo f0_rmo4 f1_rmo4 a_wa f2_rmo4 a_sup_set_class f3_rmo4 a_sup_set_class a_wceq a_wi f3_rmo4 f4_rmo4 a_wral f2_rmo4 f4_rmo4 a_wral p_3bitr4i f0_rmo4 f2_rmo4 f4_rmo4 a_wrmo f2_rmo4 a_sup_set_class f4_rmo4 a_wcel f0_rmo4 a_wa f2_rmo4 a_wmo f0_rmo4 f1_rmo4 a_wa f2_rmo4 a_sup_set_class f3_rmo4 a_sup_set_class a_wceq a_wi f3_rmo4 f4_rmo4 a_wral f2_rmo4 f4_rmo4 a_wral p_bitri $.
$}

$(Restricted uniqueness using implicit substitution.  (Contributed by NM,
       23-Nov-1994.) $)

${
	$v ph ps x y A  $.
	$d x y A  $.
	$d y ph  $.
	$d x ps  $.
	f0_reu4 $f wff ph $.
	f1_reu4 $f wff ps $.
	f2_reu4 $f set x $.
	f3_reu4 $f set y $.
	f4_reu4 $f class A $.
	e0_reu4 $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_reu4 $p |- ( E! x e. A ph <-> ( E. x e. A ph /\ A. x e. A A. y e. A ( ( ph /\ ps ) -> x = y ) ) ) $= f0_reu4 f2_reu4 f4_reu4 p_reu5 e0_reu4 f0_reu4 f1_reu4 f2_reu4 f3_reu4 f4_reu4 p_rmo4 f0_reu4 f2_reu4 f4_reu4 a_wrmo f0_reu4 f1_reu4 a_wa f2_reu4 a_sup_set_class f3_reu4 a_sup_set_class a_wceq a_wi f3_reu4 f4_reu4 a_wral f2_reu4 f4_reu4 a_wral f0_reu4 f2_reu4 f4_reu4 a_wrex p_anbi2i f0_reu4 f2_reu4 f4_reu4 a_wreu f0_reu4 f2_reu4 f4_reu4 a_wrex f0_reu4 f2_reu4 f4_reu4 a_wrmo a_wa f0_reu4 f2_reu4 f4_reu4 a_wrex f0_reu4 f1_reu4 a_wa f2_reu4 a_sup_set_class f3_reu4 a_sup_set_class a_wceq a_wi f3_reu4 f4_reu4 a_wral f2_reu4 f4_reu4 a_wral a_wa p_bitri $.
$}

$(Restricted uniqueness using implicit substitution.  (Contributed by NM,
       24-Oct-2006.) $)

${
	$v ph ps x y A  $.
	$d x y z A  $.
	$d y z ph  $.
	$d x z ps  $.
	f0_reu7 $f wff ph $.
	f1_reu7 $f wff ps $.
	f2_reu7 $f set x $.
	f3_reu7 $f set y $.
	f4_reu7 $f class A $.
	i0_reu7 $f set z $.
	e0_reu7 $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_reu7 $p |- ( E! x e. A ph <-> ( E. x e. A ph /\ E. x e. A A. y e. A ( ps -> x = y ) ) ) $= f0_reu7 f2_reu7 i0_reu7 f4_reu7 p_reu3 e0_reu7 f2_reu7 a_sup_set_class f3_reu7 a_sup_set_class i0_reu7 a_sup_set_class p_eqeq1 f3_reu7 a_sup_set_class i0_reu7 a_sup_set_class p_eqcom f2_reu7 a_sup_set_class f3_reu7 a_sup_set_class a_wceq f2_reu7 a_sup_set_class i0_reu7 a_sup_set_class a_wceq f3_reu7 a_sup_set_class i0_reu7 a_sup_set_class a_wceq i0_reu7 a_sup_set_class f3_reu7 a_sup_set_class a_wceq p_syl6bb f2_reu7 a_sup_set_class f3_reu7 a_sup_set_class a_wceq f0_reu7 f1_reu7 f2_reu7 a_sup_set_class i0_reu7 a_sup_set_class a_wceq i0_reu7 a_sup_set_class f3_reu7 a_sup_set_class a_wceq p_imbi12d f0_reu7 f2_reu7 a_sup_set_class i0_reu7 a_sup_set_class a_wceq a_wi f1_reu7 i0_reu7 a_sup_set_class f3_reu7 a_sup_set_class a_wceq a_wi f2_reu7 f3_reu7 f4_reu7 p_cbvralv f0_reu7 f2_reu7 a_sup_set_class i0_reu7 a_sup_set_class a_wceq a_wi f2_reu7 f4_reu7 a_wral f1_reu7 i0_reu7 a_sup_set_class f3_reu7 a_sup_set_class a_wceq a_wi f3_reu7 f4_reu7 a_wral i0_reu7 f4_reu7 p_rexbii i0_reu7 a_sup_set_class f2_reu7 a_sup_set_class f3_reu7 a_sup_set_class p_eqeq1 i0_reu7 a_sup_set_class f2_reu7 a_sup_set_class a_wceq i0_reu7 a_sup_set_class f3_reu7 a_sup_set_class a_wceq f2_reu7 a_sup_set_class f3_reu7 a_sup_set_class a_wceq f1_reu7 p_imbi2d i0_reu7 a_sup_set_class f2_reu7 a_sup_set_class a_wceq f1_reu7 i0_reu7 a_sup_set_class f3_reu7 a_sup_set_class a_wceq a_wi f1_reu7 f2_reu7 a_sup_set_class f3_reu7 a_sup_set_class a_wceq a_wi f3_reu7 f4_reu7 p_ralbidv f1_reu7 i0_reu7 a_sup_set_class f3_reu7 a_sup_set_class a_wceq a_wi f3_reu7 f4_reu7 a_wral f1_reu7 f2_reu7 a_sup_set_class f3_reu7 a_sup_set_class a_wceq a_wi f3_reu7 f4_reu7 a_wral i0_reu7 f2_reu7 f4_reu7 p_cbvrexv f0_reu7 f2_reu7 a_sup_set_class i0_reu7 a_sup_set_class a_wceq a_wi f2_reu7 f4_reu7 a_wral i0_reu7 f4_reu7 a_wrex f1_reu7 i0_reu7 a_sup_set_class f3_reu7 a_sup_set_class a_wceq a_wi f3_reu7 f4_reu7 a_wral i0_reu7 f4_reu7 a_wrex f1_reu7 f2_reu7 a_sup_set_class f3_reu7 a_sup_set_class a_wceq a_wi f3_reu7 f4_reu7 a_wral f2_reu7 f4_reu7 a_wrex p_bitri f0_reu7 f2_reu7 a_sup_set_class i0_reu7 a_sup_set_class a_wceq a_wi f2_reu7 f4_reu7 a_wral i0_reu7 f4_reu7 a_wrex f1_reu7 f2_reu7 a_sup_set_class f3_reu7 a_sup_set_class a_wceq a_wi f3_reu7 f4_reu7 a_wral f2_reu7 f4_reu7 a_wrex f0_reu7 f2_reu7 f4_reu7 a_wrex p_anbi2i f0_reu7 f2_reu7 f4_reu7 a_wreu f0_reu7 f2_reu7 f4_reu7 a_wrex f0_reu7 f2_reu7 a_sup_set_class i0_reu7 a_sup_set_class a_wceq a_wi f2_reu7 f4_reu7 a_wral i0_reu7 f4_reu7 a_wrex a_wa f0_reu7 f2_reu7 f4_reu7 a_wrex f1_reu7 f2_reu7 a_sup_set_class f3_reu7 a_sup_set_class a_wceq a_wi f3_reu7 f4_reu7 a_wral f2_reu7 f4_reu7 a_wrex a_wa p_bitri $.
$}

$(Restricted uniqueness using implicit substitution.  (Contributed by NM,
       24-Oct-2006.) $)

${
	$v ph ps x y A  $.
	$d x y A  $.
	$d y ph  $.
	$d x ps  $.
	f0_reu8 $f wff ph $.
	f1_reu8 $f wff ps $.
	f2_reu8 $f set x $.
	f3_reu8 $f set y $.
	f4_reu8 $f class A $.
	e0_reu8 $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_reu8 $p |- ( E! x e. A ph <-> E. x e. A ( ph /\ A. y e. A ( ps -> x = y ) ) ) $= e0_reu8 f0_reu8 f1_reu8 f2_reu8 f3_reu8 f4_reu8 p_cbvreuv f1_reu8 f3_reu8 f2_reu8 f4_reu8 p_reu6 f1_reu8 f3_reu8 a_sup_set_class f2_reu8 a_sup_set_class a_wceq p_dfbi2 f1_reu8 f3_reu8 a_sup_set_class f2_reu8 a_sup_set_class a_wceq a_wb f1_reu8 f3_reu8 a_sup_set_class f2_reu8 a_sup_set_class a_wceq a_wi f3_reu8 a_sup_set_class f2_reu8 a_sup_set_class a_wceq f1_reu8 a_wi a_wa f3_reu8 f4_reu8 p_ralbii f0_reu8 f1_reu8 f2_reu8 a_sup_set_class f3_reu8 a_sup_set_class a_wceq a_wi f3_reu8 f4_reu8 a_wral p_ancom f2_reu8 f3_reu8 p_equcom f2_reu8 a_sup_set_class f3_reu8 a_sup_set_class a_wceq f3_reu8 a_sup_set_class f2_reu8 a_sup_set_class a_wceq f1_reu8 p_imbi2i f1_reu8 f2_reu8 a_sup_set_class f3_reu8 a_sup_set_class a_wceq a_wi f1_reu8 f3_reu8 a_sup_set_class f2_reu8 a_sup_set_class a_wceq a_wi f3_reu8 f4_reu8 p_ralbii f1_reu8 f2_reu8 a_sup_set_class f3_reu8 a_sup_set_class a_wceq a_wi f3_reu8 f4_reu8 a_wral f1_reu8 f3_reu8 a_sup_set_class f2_reu8 a_sup_set_class a_wceq a_wi f3_reu8 f4_reu8 a_wral a_wb f2_reu8 a_sup_set_class f4_reu8 a_wcel p_a1i f2_reu8 a_sup_set_class f4_reu8 a_wcel f0_reu8 p_biimt f3_reu8 a_sup_set_class f2_reu8 a_sup_set_class a_wceq f1_reu8 a_wi f3_reu8 f4_reu8 a_df-ral f3_reu8 a_sup_set_class f4_reu8 a_wcel f3_reu8 a_sup_set_class f2_reu8 a_sup_set_class a_wceq f1_reu8 p_bi2.04 f3_reu8 a_sup_set_class f4_reu8 a_wcel f3_reu8 a_sup_set_class f2_reu8 a_sup_set_class a_wceq f1_reu8 a_wi a_wi f3_reu8 a_sup_set_class f2_reu8 a_sup_set_class a_wceq f3_reu8 a_sup_set_class f4_reu8 a_wcel f1_reu8 a_wi a_wi f3_reu8 p_albii f2_reu8 p_vex f2_reu8 a_sup_set_class f3_reu8 a_sup_set_class f4_reu8 p_eleq1 e0_reu8 f2_reu8 a_sup_set_class f3_reu8 a_sup_set_class a_wceq f2_reu8 a_sup_set_class f4_reu8 a_wcel f3_reu8 a_sup_set_class f4_reu8 a_wcel f0_reu8 f1_reu8 p_imbi12d f2_reu8 a_sup_set_class f3_reu8 a_sup_set_class a_wceq f2_reu8 a_sup_set_class f4_reu8 a_wcel f0_reu8 a_wi f3_reu8 a_sup_set_class f4_reu8 a_wcel f1_reu8 a_wi p_bicomd f3_reu8 a_sup_set_class f4_reu8 a_wcel f1_reu8 a_wi f2_reu8 a_sup_set_class f4_reu8 a_wcel f0_reu8 a_wi a_wb f2_reu8 f3_reu8 p_equcoms f3_reu8 a_sup_set_class f4_reu8 a_wcel f1_reu8 a_wi f2_reu8 a_sup_set_class f4_reu8 a_wcel f0_reu8 a_wi f3_reu8 f2_reu8 a_sup_set_class p_ceqsalv f3_reu8 a_sup_set_class f2_reu8 a_sup_set_class a_wceq f1_reu8 a_wi f3_reu8 f4_reu8 a_wral f3_reu8 a_sup_set_class f4_reu8 a_wcel f3_reu8 a_sup_set_class f2_reu8 a_sup_set_class a_wceq f1_reu8 a_wi a_wi f3_reu8 a_wal f3_reu8 a_sup_set_class f2_reu8 a_sup_set_class a_wceq f3_reu8 a_sup_set_class f4_reu8 a_wcel f1_reu8 a_wi a_wi f3_reu8 a_wal f2_reu8 a_sup_set_class f4_reu8 a_wcel f0_reu8 a_wi p_3bitrri f2_reu8 a_sup_set_class f4_reu8 a_wcel f0_reu8 f2_reu8 a_sup_set_class f4_reu8 a_wcel f0_reu8 a_wi f3_reu8 a_sup_set_class f2_reu8 a_sup_set_class a_wceq f1_reu8 a_wi f3_reu8 f4_reu8 a_wral p_syl6bb f2_reu8 a_sup_set_class f4_reu8 a_wcel f1_reu8 f2_reu8 a_sup_set_class f3_reu8 a_sup_set_class a_wceq a_wi f3_reu8 f4_reu8 a_wral f1_reu8 f3_reu8 a_sup_set_class f2_reu8 a_sup_set_class a_wceq a_wi f3_reu8 f4_reu8 a_wral f0_reu8 f3_reu8 a_sup_set_class f2_reu8 a_sup_set_class a_wceq f1_reu8 a_wi f3_reu8 f4_reu8 a_wral p_anbi12d f0_reu8 f1_reu8 f2_reu8 a_sup_set_class f3_reu8 a_sup_set_class a_wceq a_wi f3_reu8 f4_reu8 a_wral a_wa f1_reu8 f2_reu8 a_sup_set_class f3_reu8 a_sup_set_class a_wceq a_wi f3_reu8 f4_reu8 a_wral f0_reu8 a_wa f2_reu8 a_sup_set_class f4_reu8 a_wcel f1_reu8 f3_reu8 a_sup_set_class f2_reu8 a_sup_set_class a_wceq a_wi f3_reu8 f4_reu8 a_wral f3_reu8 a_sup_set_class f2_reu8 a_sup_set_class a_wceq f1_reu8 a_wi f3_reu8 f4_reu8 a_wral a_wa p_syl5bb f1_reu8 f3_reu8 a_sup_set_class f2_reu8 a_sup_set_class a_wceq a_wi f3_reu8 a_sup_set_class f2_reu8 a_sup_set_class a_wceq f1_reu8 a_wi f3_reu8 f4_reu8 p_r19.26 f2_reu8 a_sup_set_class f4_reu8 a_wcel f0_reu8 f1_reu8 f2_reu8 a_sup_set_class f3_reu8 a_sup_set_class a_wceq a_wi f3_reu8 f4_reu8 a_wral a_wa f1_reu8 f3_reu8 a_sup_set_class f2_reu8 a_sup_set_class a_wceq a_wi f3_reu8 f4_reu8 a_wral f3_reu8 a_sup_set_class f2_reu8 a_sup_set_class a_wceq f1_reu8 a_wi f3_reu8 f4_reu8 a_wral a_wa f1_reu8 f3_reu8 a_sup_set_class f2_reu8 a_sup_set_class a_wceq a_wi f3_reu8 a_sup_set_class f2_reu8 a_sup_set_class a_wceq f1_reu8 a_wi a_wa f3_reu8 f4_reu8 a_wral p_syl6rbbr f1_reu8 f3_reu8 a_sup_set_class f2_reu8 a_sup_set_class a_wceq a_wb f3_reu8 f4_reu8 a_wral f1_reu8 f3_reu8 a_sup_set_class f2_reu8 a_sup_set_class a_wceq a_wi f3_reu8 a_sup_set_class f2_reu8 a_sup_set_class a_wceq f1_reu8 a_wi a_wa f3_reu8 f4_reu8 a_wral f2_reu8 a_sup_set_class f4_reu8 a_wcel f0_reu8 f1_reu8 f2_reu8 a_sup_set_class f3_reu8 a_sup_set_class a_wceq a_wi f3_reu8 f4_reu8 a_wral a_wa p_syl5bb f1_reu8 f3_reu8 a_sup_set_class f2_reu8 a_sup_set_class a_wceq a_wb f3_reu8 f4_reu8 a_wral f0_reu8 f1_reu8 f2_reu8 a_sup_set_class f3_reu8 a_sup_set_class a_wceq a_wi f3_reu8 f4_reu8 a_wral a_wa f2_reu8 f4_reu8 p_rexbiia f0_reu8 f2_reu8 f4_reu8 a_wreu f1_reu8 f3_reu8 f4_reu8 a_wreu f1_reu8 f3_reu8 a_sup_set_class f2_reu8 a_sup_set_class a_wceq a_wb f3_reu8 f4_reu8 a_wral f2_reu8 f4_reu8 a_wrex f0_reu8 f1_reu8 f2_reu8 a_sup_set_class f3_reu8 a_sup_set_class a_wceq a_wi f3_reu8 f4_reu8 a_wral a_wa f2_reu8 f4_reu8 a_wrex p_3bitri $.
$}

$(Equality has existential uniqueness.  (Contributed by Mario Carneiro,
       1-Sep-2015.) $)

${
	$v x A B  $.
	$d x A  $.
	$d x B  $.
	f0_reueq $f set x $.
	f1_reueq $f class A $.
	f2_reueq $f class B $.
	p_reueq $p |- ( B e. A <-> E! x e. A x = B ) $= f0_reueq f2_reueq f1_reueq p_risset f0_reueq f2_reueq p_moeq f0_reueq a_sup_set_class f2_reueq a_wceq f0_reueq f1_reueq p_mormo f0_reueq a_sup_set_class f2_reueq a_wceq f0_reueq a_wmo f0_reueq a_sup_set_class f2_reueq a_wceq f0_reueq f1_reueq a_wrmo a_ax-mp f0_reueq a_sup_set_class f2_reueq a_wceq f0_reueq f1_reueq p_reu5 f0_reueq a_sup_set_class f2_reueq a_wceq f0_reueq f1_reueq a_wreu f0_reueq a_sup_set_class f2_reueq a_wceq f0_reueq f1_reueq a_wrex f0_reueq a_sup_set_class f2_reueq a_wceq f0_reueq f1_reueq a_wrmo p_mpbiran2 f2_reueq f1_reueq a_wcel f0_reueq a_sup_set_class f2_reueq a_wceq f0_reueq f1_reueq a_wrex f0_reueq a_sup_set_class f2_reueq a_wceq f0_reueq f1_reueq a_wreu p_bitr4i $.
$}

$(Restricted "at most one" still holds when a conjunct is added.
     (Contributed by NM, 16-Jun-2017.) $)

${
	$v ph ps x A  $.
	f0_rmoan $f wff ph $.
	f1_rmoan $f wff ps $.
	f2_rmoan $f set x $.
	f3_rmoan $f class A $.
	p_rmoan $p |- ( E* x e. A ph -> E* x e. A ( ps /\ ph ) ) $= f2_rmoan a_sup_set_class f3_rmoan a_wcel f0_rmoan a_wa f1_rmoan f2_rmoan p_moan f1_rmoan f2_rmoan a_sup_set_class f3_rmoan a_wcel f0_rmoan p_an12 f1_rmoan f2_rmoan a_sup_set_class f3_rmoan a_wcel f0_rmoan a_wa a_wa f2_rmoan a_sup_set_class f3_rmoan a_wcel f1_rmoan f0_rmoan a_wa a_wa f2_rmoan p_mobii f2_rmoan a_sup_set_class f3_rmoan a_wcel f0_rmoan a_wa f2_rmoan a_wmo f1_rmoan f2_rmoan a_sup_set_class f3_rmoan a_wcel f0_rmoan a_wa a_wa f2_rmoan a_wmo f2_rmoan a_sup_set_class f3_rmoan a_wcel f1_rmoan f0_rmoan a_wa a_wa f2_rmoan a_wmo p_sylib f0_rmoan f2_rmoan f3_rmoan a_df-rmo f1_rmoan f0_rmoan a_wa f2_rmoan f3_rmoan a_df-rmo f2_rmoan a_sup_set_class f3_rmoan a_wcel f0_rmoan a_wa f2_rmoan a_wmo f2_rmoan a_sup_set_class f3_rmoan a_wcel f1_rmoan f0_rmoan a_wa a_wa f2_rmoan a_wmo f0_rmoan f2_rmoan f3_rmoan a_wrmo f1_rmoan f0_rmoan a_wa f2_rmoan f3_rmoan a_wrmo p_3imtr4i $.
$}

$(Restricted "at most one" is preserved through implication (note wff
     reversal).  (Contributed by Alexander van der Vekens, 17-Jun-2017.) $)

${
	$v ph ps x A  $.
	f0_rmoim $f wff ph $.
	f1_rmoim $f wff ps $.
	f2_rmoim $f set x $.
	f3_rmoim $f class A $.
	p_rmoim $p |- ( A. x e. A ( ph -> ps ) -> ( E* x e. A ps -> E* x e. A ph ) ) $= f0_rmoim f1_rmoim a_wi f2_rmoim f3_rmoim a_df-ral f2_rmoim a_sup_set_class f3_rmoim a_wcel f0_rmoim f1_rmoim p_imdistan f2_rmoim a_sup_set_class f3_rmoim a_wcel f0_rmoim f1_rmoim a_wi a_wi f2_rmoim a_sup_set_class f3_rmoim a_wcel f0_rmoim a_wa f2_rmoim a_sup_set_class f3_rmoim a_wcel f1_rmoim a_wa a_wi f2_rmoim p_albii f0_rmoim f1_rmoim a_wi f2_rmoim f3_rmoim a_wral f2_rmoim a_sup_set_class f3_rmoim a_wcel f0_rmoim f1_rmoim a_wi a_wi f2_rmoim a_wal f2_rmoim a_sup_set_class f3_rmoim a_wcel f0_rmoim a_wa f2_rmoim a_sup_set_class f3_rmoim a_wcel f1_rmoim a_wa a_wi f2_rmoim a_wal p_bitri f2_rmoim a_sup_set_class f3_rmoim a_wcel f0_rmoim a_wa f2_rmoim a_sup_set_class f3_rmoim a_wcel f1_rmoim a_wa f2_rmoim p_moim f1_rmoim f2_rmoim f3_rmoim a_df-rmo f0_rmoim f2_rmoim f3_rmoim a_df-rmo f2_rmoim a_sup_set_class f3_rmoim a_wcel f0_rmoim a_wa f2_rmoim a_sup_set_class f3_rmoim a_wcel f1_rmoim a_wa a_wi f2_rmoim a_wal f2_rmoim a_sup_set_class f3_rmoim a_wcel f1_rmoim a_wa f2_rmoim a_wmo f2_rmoim a_sup_set_class f3_rmoim a_wcel f0_rmoim a_wa f2_rmoim a_wmo f1_rmoim f2_rmoim f3_rmoim a_wrmo f0_rmoim f2_rmoim f3_rmoim a_wrmo p_3imtr4g f0_rmoim f1_rmoim a_wi f2_rmoim f3_rmoim a_wral f2_rmoim a_sup_set_class f3_rmoim a_wcel f0_rmoim a_wa f2_rmoim a_sup_set_class f3_rmoim a_wcel f1_rmoim a_wa a_wi f2_rmoim a_wal f1_rmoim f2_rmoim f3_rmoim a_wrmo f0_rmoim f2_rmoim f3_rmoim a_wrmo a_wi p_sylbi $.
$}

$(Restricted "at most one" is preserved through implication (note wff
       reversal).  (Contributed by Alexander van der Vekens, 17-Jun-2017.) $)

${
	$v ph ps x A  $.
	f0_rmoimia $f wff ph $.
	f1_rmoimia $f wff ps $.
	f2_rmoimia $f set x $.
	f3_rmoimia $f class A $.
	e0_rmoimia $e |- ( x e. A -> ( ph -> ps ) ) $.
	p_rmoimia $p |- ( E* x e. A ps -> E* x e. A ph ) $= f0_rmoimia f1_rmoimia f2_rmoimia f3_rmoimia p_rmoim e0_rmoimia f0_rmoimia f1_rmoimia a_wi f1_rmoimia f2_rmoimia f3_rmoimia a_wrmo f0_rmoimia f2_rmoimia f3_rmoimia a_wrmo a_wi f2_rmoimia f3_rmoimia p_mprg $.
$}

$(Restricted "at most one" is preserved through implication (note wff
       reversal).  (Contributed by Alexander van der Vekens, 17-Jun-2017.) $)

${
	$v ph ps x A B  $.
	f0_rmoimi2 $f wff ph $.
	f1_rmoimi2 $f wff ps $.
	f2_rmoimi2 $f set x $.
	f3_rmoimi2 $f class A $.
	f4_rmoimi2 $f class B $.
	e0_rmoimi2 $e |- A. x ( ( x e. A /\ ph ) -> ( x e. B /\ ps ) ) $.
	p_rmoimi2 $p |- ( E* x e. B ps -> E* x e. A ph ) $= e0_rmoimi2 f2_rmoimi2 a_sup_set_class f3_rmoimi2 a_wcel f0_rmoimi2 a_wa f2_rmoimi2 a_sup_set_class f4_rmoimi2 a_wcel f1_rmoimi2 a_wa f2_rmoimi2 p_moim f2_rmoimi2 a_sup_set_class f3_rmoimi2 a_wcel f0_rmoimi2 a_wa f2_rmoimi2 a_sup_set_class f4_rmoimi2 a_wcel f1_rmoimi2 a_wa a_wi f2_rmoimi2 a_wal f2_rmoimi2 a_sup_set_class f4_rmoimi2 a_wcel f1_rmoimi2 a_wa f2_rmoimi2 a_wmo f2_rmoimi2 a_sup_set_class f3_rmoimi2 a_wcel f0_rmoimi2 a_wa f2_rmoimi2 a_wmo a_wi a_ax-mp f1_rmoimi2 f2_rmoimi2 f4_rmoimi2 a_df-rmo f0_rmoimi2 f2_rmoimi2 f3_rmoimi2 a_df-rmo f2_rmoimi2 a_sup_set_class f4_rmoimi2 a_wcel f1_rmoimi2 a_wa f2_rmoimi2 a_wmo f2_rmoimi2 a_sup_set_class f3_rmoimi2 a_wcel f0_rmoimi2 a_wa f2_rmoimi2 a_wmo f1_rmoimi2 f2_rmoimi2 f4_rmoimi2 a_wrmo f0_rmoimi2 f2_rmoimi2 f3_rmoimi2 a_wrmo p_3imtr4i $.
$}

$(A condition allowing swap of uniqueness and existential quantifiers.
       (Contributed by Thierry Arnoux, 7-Apr-2017.)  (Revised by NM,
       16-Jun-2017.) $)

${
	$v ph x y A B  $.
	$d x y A  $.
	$d x B  $.
	f0_2reuswap $f wff ph $.
	f1_2reuswap $f set x $.
	f2_2reuswap $f set y $.
	f3_2reuswap $f class A $.
	f4_2reuswap $f class B $.
	p_2reuswap $p |- ( A. x e. A E* y e. B ph -> ( E! x e. A E. y e. B ph -> E! y e. B E. x e. A ph ) ) $= f0_2reuswap f2_2reuswap f4_2reuswap a_df-rmo f0_2reuswap f2_2reuswap f4_2reuswap a_wrmo f2_2reuswap a_sup_set_class f4_2reuswap a_wcel f0_2reuswap a_wa f2_2reuswap a_wmo f1_2reuswap f3_2reuswap p_ralbii f2_2reuswap a_sup_set_class f4_2reuswap a_wcel f0_2reuswap a_wa f2_2reuswap a_wmo f1_2reuswap f3_2reuswap a_df-ral f1_2reuswap a_sup_set_class f3_2reuswap a_wcel f2_2reuswap a_sup_set_class f4_2reuswap a_wcel f0_2reuswap a_wa f2_2reuswap p_moanimv f1_2reuswap a_sup_set_class f3_2reuswap a_wcel f2_2reuswap a_sup_set_class f4_2reuswap a_wcel f0_2reuswap a_wa a_wa f2_2reuswap a_wmo f1_2reuswap a_sup_set_class f3_2reuswap a_wcel f2_2reuswap a_sup_set_class f4_2reuswap a_wcel f0_2reuswap a_wa f2_2reuswap a_wmo a_wi f1_2reuswap p_albii f2_2reuswap a_sup_set_class f4_2reuswap a_wcel f0_2reuswap a_wa f2_2reuswap a_wmo f1_2reuswap f3_2reuswap a_wral f1_2reuswap a_sup_set_class f3_2reuswap a_wcel f2_2reuswap a_sup_set_class f4_2reuswap a_wcel f0_2reuswap a_wa f2_2reuswap a_wmo a_wi f1_2reuswap a_wal f1_2reuswap a_sup_set_class f3_2reuswap a_wcel f2_2reuswap a_sup_set_class f4_2reuswap a_wcel f0_2reuswap a_wa a_wa f2_2reuswap a_wmo f1_2reuswap a_wal p_bitr4i f1_2reuswap a_sup_set_class f3_2reuswap a_wcel f2_2reuswap a_sup_set_class f4_2reuswap a_wcel f0_2reuswap a_wa a_wa f1_2reuswap f2_2reuswap p_2euswap f0_2reuswap f2_2reuswap f4_2reuswap a_wrex f1_2reuswap f3_2reuswap a_df-reu f1_2reuswap a_sup_set_class f3_2reuswap a_wcel f0_2reuswap f2_2reuswap f4_2reuswap p_r19.42v f1_2reuswap a_sup_set_class f3_2reuswap a_wcel f0_2reuswap a_wa f2_2reuswap f4_2reuswap a_df-rex f1_2reuswap a_sup_set_class f3_2reuswap a_wcel f0_2reuswap f2_2reuswap f4_2reuswap a_wrex a_wa f1_2reuswap a_sup_set_class f3_2reuswap a_wcel f0_2reuswap a_wa f2_2reuswap f4_2reuswap a_wrex f2_2reuswap a_sup_set_class f4_2reuswap a_wcel f1_2reuswap a_sup_set_class f3_2reuswap a_wcel f0_2reuswap a_wa a_wa f2_2reuswap a_wex p_bitr3i f2_2reuswap a_sup_set_class f4_2reuswap a_wcel f1_2reuswap a_sup_set_class f3_2reuswap a_wcel f0_2reuswap p_an12 f2_2reuswap a_sup_set_class f4_2reuswap a_wcel f1_2reuswap a_sup_set_class f3_2reuswap a_wcel f0_2reuswap a_wa a_wa f1_2reuswap a_sup_set_class f3_2reuswap a_wcel f2_2reuswap a_sup_set_class f4_2reuswap a_wcel f0_2reuswap a_wa a_wa f2_2reuswap p_exbii f1_2reuswap a_sup_set_class f3_2reuswap a_wcel f0_2reuswap f2_2reuswap f4_2reuswap a_wrex a_wa f2_2reuswap a_sup_set_class f4_2reuswap a_wcel f1_2reuswap a_sup_set_class f3_2reuswap a_wcel f0_2reuswap a_wa a_wa f2_2reuswap a_wex f1_2reuswap a_sup_set_class f3_2reuswap a_wcel f2_2reuswap a_sup_set_class f4_2reuswap a_wcel f0_2reuswap a_wa a_wa f2_2reuswap a_wex p_bitri f1_2reuswap a_sup_set_class f3_2reuswap a_wcel f0_2reuswap f2_2reuswap f4_2reuswap a_wrex a_wa f1_2reuswap a_sup_set_class f3_2reuswap a_wcel f2_2reuswap a_sup_set_class f4_2reuswap a_wcel f0_2reuswap a_wa a_wa f2_2reuswap a_wex f1_2reuswap p_eubii f0_2reuswap f2_2reuswap f4_2reuswap a_wrex f1_2reuswap f3_2reuswap a_wreu f1_2reuswap a_sup_set_class f3_2reuswap a_wcel f0_2reuswap f2_2reuswap f4_2reuswap a_wrex a_wa f1_2reuswap a_weu f1_2reuswap a_sup_set_class f3_2reuswap a_wcel f2_2reuswap a_sup_set_class f4_2reuswap a_wcel f0_2reuswap a_wa a_wa f2_2reuswap a_wex f1_2reuswap a_weu p_bitri f0_2reuswap f1_2reuswap f3_2reuswap a_wrex f2_2reuswap f4_2reuswap a_df-reu f2_2reuswap a_sup_set_class f4_2reuswap a_wcel f0_2reuswap f1_2reuswap f3_2reuswap p_r19.42v f2_2reuswap a_sup_set_class f4_2reuswap a_wcel f0_2reuswap a_wa f1_2reuswap f3_2reuswap a_df-rex f2_2reuswap a_sup_set_class f4_2reuswap a_wcel f0_2reuswap f1_2reuswap f3_2reuswap a_wrex a_wa f2_2reuswap a_sup_set_class f4_2reuswap a_wcel f0_2reuswap a_wa f1_2reuswap f3_2reuswap a_wrex f1_2reuswap a_sup_set_class f3_2reuswap a_wcel f2_2reuswap a_sup_set_class f4_2reuswap a_wcel f0_2reuswap a_wa a_wa f1_2reuswap a_wex p_bitr3i f2_2reuswap a_sup_set_class f4_2reuswap a_wcel f0_2reuswap f1_2reuswap f3_2reuswap a_wrex a_wa f1_2reuswap a_sup_set_class f3_2reuswap a_wcel f2_2reuswap a_sup_set_class f4_2reuswap a_wcel f0_2reuswap a_wa a_wa f1_2reuswap a_wex f2_2reuswap p_eubii f0_2reuswap f1_2reuswap f3_2reuswap a_wrex f2_2reuswap f4_2reuswap a_wreu f2_2reuswap a_sup_set_class f4_2reuswap a_wcel f0_2reuswap f1_2reuswap f3_2reuswap a_wrex a_wa f2_2reuswap a_weu f1_2reuswap a_sup_set_class f3_2reuswap a_wcel f2_2reuswap a_sup_set_class f4_2reuswap a_wcel f0_2reuswap a_wa a_wa f1_2reuswap a_wex f2_2reuswap a_weu p_bitri f1_2reuswap a_sup_set_class f3_2reuswap a_wcel f2_2reuswap a_sup_set_class f4_2reuswap a_wcel f0_2reuswap a_wa a_wa f2_2reuswap a_wmo f1_2reuswap a_wal f1_2reuswap a_sup_set_class f3_2reuswap a_wcel f2_2reuswap a_sup_set_class f4_2reuswap a_wcel f0_2reuswap a_wa a_wa f2_2reuswap a_wex f1_2reuswap a_weu f1_2reuswap a_sup_set_class f3_2reuswap a_wcel f2_2reuswap a_sup_set_class f4_2reuswap a_wcel f0_2reuswap a_wa a_wa f1_2reuswap a_wex f2_2reuswap a_weu f0_2reuswap f2_2reuswap f4_2reuswap a_wrex f1_2reuswap f3_2reuswap a_wreu f0_2reuswap f1_2reuswap f3_2reuswap a_wrex f2_2reuswap f4_2reuswap a_wreu p_3imtr4g f2_2reuswap a_sup_set_class f4_2reuswap a_wcel f0_2reuswap a_wa f2_2reuswap a_wmo f1_2reuswap f3_2reuswap a_wral f1_2reuswap a_sup_set_class f3_2reuswap a_wcel f2_2reuswap a_sup_set_class f4_2reuswap a_wcel f0_2reuswap a_wa a_wa f2_2reuswap a_wmo f1_2reuswap a_wal f0_2reuswap f2_2reuswap f4_2reuswap a_wrex f1_2reuswap f3_2reuswap a_wreu f0_2reuswap f1_2reuswap f3_2reuswap a_wrex f2_2reuswap f4_2reuswap a_wreu a_wi p_sylbi f0_2reuswap f2_2reuswap f4_2reuswap a_wrmo f1_2reuswap f3_2reuswap a_wral f2_2reuswap a_sup_set_class f4_2reuswap a_wcel f0_2reuswap a_wa f2_2reuswap a_wmo f1_2reuswap f3_2reuswap a_wral f0_2reuswap f2_2reuswap f4_2reuswap a_wrex f1_2reuswap f3_2reuswap a_wreu f0_2reuswap f1_2reuswap f3_2reuswap a_wrex f2_2reuswap f4_2reuswap a_wreu a_wi p_sylbi $.
$}

$(Existential uniqueness via an indirect equality.  (Contributed by NM,
       16-Oct-2010.) $)

${
	$v ph ps x y z A B C  $.
	$d w y z A  $.
	$d x z B  $.
	$d w x y z C  $.
	$d w y z ph  $.
	$d x z ps  $.
	f0_reuind $f wff ph $.
	f1_reuind $f wff ps $.
	f2_reuind $f set x $.
	f3_reuind $f set y $.
	f4_reuind $f set z $.
	f5_reuind $f class A $.
	f6_reuind $f class B $.
	f7_reuind $f class C $.
	i0_reuind $f set w $.
	e0_reuind $e |- ( x = y -> ( ph <-> ps ) ) $.
	e1_reuind $e |- ( x = y -> A = B ) $.
	p_reuind $p |- ( ( A. x A. y ( ( ( A e. C /\ ph ) /\ ( B e. C /\ ps ) ) -> A = B ) /\ E. x ( A e. C /\ ph ) ) -> E! z e. C A. x ( ( A e. C /\ ph ) -> z = A ) ) $= e1_reuind f2_reuind a_sup_set_class f3_reuind a_sup_set_class a_wceq f5_reuind f6_reuind f7_reuind p_eleq1d e0_reuind f2_reuind a_sup_set_class f3_reuind a_sup_set_class a_wceq f5_reuind f7_reuind a_wcel f6_reuind f7_reuind a_wcel f0_reuind f1_reuind p_anbi12d f5_reuind f7_reuind a_wcel f0_reuind a_wa f6_reuind f7_reuind a_wcel f1_reuind a_wa f2_reuind f3_reuind p_cbvexv f4_reuind a_sup_set_class f6_reuind a_wceq f1_reuind f4_reuind f7_reuind p_r19.41v f4_reuind a_sup_set_class f6_reuind a_wceq f1_reuind a_wa f4_reuind f7_reuind a_wrex f4_reuind a_sup_set_class f6_reuind a_wceq f4_reuind f7_reuind a_wrex f1_reuind a_wa f3_reuind p_exbii f4_reuind a_sup_set_class f6_reuind a_wceq f1_reuind a_wa f4_reuind f3_reuind f7_reuind p_rexcom4 f4_reuind f6_reuind f7_reuind p_risset f6_reuind f7_reuind a_wcel f4_reuind a_sup_set_class f6_reuind a_wceq f4_reuind f7_reuind a_wrex f1_reuind p_anbi1i f6_reuind f7_reuind a_wcel f1_reuind a_wa f4_reuind a_sup_set_class f6_reuind a_wceq f4_reuind f7_reuind a_wrex f1_reuind a_wa f3_reuind p_exbii f4_reuind a_sup_set_class f6_reuind a_wceq f1_reuind a_wa f4_reuind f7_reuind a_wrex f3_reuind a_wex f4_reuind a_sup_set_class f6_reuind a_wceq f4_reuind f7_reuind a_wrex f1_reuind a_wa f3_reuind a_wex f4_reuind a_sup_set_class f6_reuind a_wceq f1_reuind a_wa f3_reuind a_wex f4_reuind f7_reuind a_wrex f6_reuind f7_reuind a_wcel f1_reuind a_wa f3_reuind a_wex p_3bitr4ri f5_reuind f7_reuind a_wcel f0_reuind a_wa f2_reuind a_wex f6_reuind f7_reuind a_wcel f1_reuind a_wa f3_reuind a_wex f4_reuind a_sup_set_class f6_reuind a_wceq f1_reuind a_wa f3_reuind a_wex f4_reuind f7_reuind a_wrex p_bitri f5_reuind f6_reuind f4_reuind a_sup_set_class p_eqeq2 f5_reuind f6_reuind a_wceq f4_reuind a_sup_set_class f5_reuind a_wceq f4_reuind a_sup_set_class f6_reuind a_wceq a_wb f5_reuind f7_reuind a_wcel f0_reuind a_wa f6_reuind f7_reuind a_wcel f1_reuind a_wa a_wa p_imim2i f4_reuind a_sup_set_class f5_reuind a_wceq f4_reuind a_sup_set_class f6_reuind a_wceq p_bi2 f4_reuind a_sup_set_class f5_reuind a_wceq f4_reuind a_sup_set_class f6_reuind a_wceq a_wb f4_reuind a_sup_set_class f6_reuind a_wceq f4_reuind a_sup_set_class f5_reuind a_wceq a_wi f5_reuind f7_reuind a_wcel f0_reuind a_wa f6_reuind f7_reuind a_wcel f1_reuind a_wa a_wa p_imim2i f5_reuind f7_reuind a_wcel f0_reuind a_wa f6_reuind f7_reuind a_wcel f1_reuind a_wa f4_reuind a_sup_set_class f6_reuind a_wceq p_an31 f5_reuind f7_reuind a_wcel f0_reuind a_wa f6_reuind f7_reuind a_wcel f1_reuind a_wa a_wa f4_reuind a_sup_set_class f6_reuind a_wceq a_wa f4_reuind a_sup_set_class f6_reuind a_wceq f6_reuind f7_reuind a_wcel f1_reuind a_wa a_wa f5_reuind f7_reuind a_wcel f0_reuind a_wa a_wa f4_reuind a_sup_set_class f5_reuind a_wceq p_imbi1i f5_reuind f7_reuind a_wcel f0_reuind a_wa f6_reuind f7_reuind a_wcel f1_reuind a_wa a_wa f4_reuind a_sup_set_class f6_reuind a_wceq f4_reuind a_sup_set_class f5_reuind a_wceq p_impexp f4_reuind a_sup_set_class f6_reuind a_wceq f6_reuind f7_reuind a_wcel f1_reuind a_wa a_wa f5_reuind f7_reuind a_wcel f0_reuind a_wa f4_reuind a_sup_set_class f5_reuind a_wceq p_impexp f5_reuind f7_reuind a_wcel f0_reuind a_wa f6_reuind f7_reuind a_wcel f1_reuind a_wa a_wa f4_reuind a_sup_set_class f6_reuind a_wceq a_wa f4_reuind a_sup_set_class f5_reuind a_wceq a_wi f4_reuind a_sup_set_class f6_reuind a_wceq f6_reuind f7_reuind a_wcel f1_reuind a_wa a_wa f5_reuind f7_reuind a_wcel f0_reuind a_wa a_wa f4_reuind a_sup_set_class f5_reuind a_wceq a_wi f5_reuind f7_reuind a_wcel f0_reuind a_wa f6_reuind f7_reuind a_wcel f1_reuind a_wa a_wa f4_reuind a_sup_set_class f6_reuind a_wceq f4_reuind a_sup_set_class f5_reuind a_wceq a_wi a_wi f4_reuind a_sup_set_class f6_reuind a_wceq f6_reuind f7_reuind a_wcel f1_reuind a_wa a_wa f5_reuind f7_reuind a_wcel f0_reuind a_wa f4_reuind a_sup_set_class f5_reuind a_wceq a_wi a_wi p_3bitr3i f5_reuind f7_reuind a_wcel f0_reuind a_wa f6_reuind f7_reuind a_wcel f1_reuind a_wa a_wa f4_reuind a_sup_set_class f5_reuind a_wceq f4_reuind a_sup_set_class f6_reuind a_wceq a_wb a_wi f5_reuind f7_reuind a_wcel f0_reuind a_wa f6_reuind f7_reuind a_wcel f1_reuind a_wa a_wa f4_reuind a_sup_set_class f6_reuind a_wceq f4_reuind a_sup_set_class f5_reuind a_wceq a_wi a_wi f4_reuind a_sup_set_class f6_reuind a_wceq f6_reuind f7_reuind a_wcel f1_reuind a_wa a_wa f5_reuind f7_reuind a_wcel f0_reuind a_wa f4_reuind a_sup_set_class f5_reuind a_wceq a_wi a_wi p_sylib f5_reuind f7_reuind a_wcel f0_reuind a_wa f6_reuind f7_reuind a_wcel f1_reuind a_wa a_wa f5_reuind f6_reuind a_wceq a_wi f5_reuind f7_reuind a_wcel f0_reuind a_wa f6_reuind f7_reuind a_wcel f1_reuind a_wa a_wa f4_reuind a_sup_set_class f5_reuind a_wceq f4_reuind a_sup_set_class f6_reuind a_wceq a_wb a_wi f4_reuind a_sup_set_class f6_reuind a_wceq f6_reuind f7_reuind a_wcel f1_reuind a_wa a_wa f5_reuind f7_reuind a_wcel f0_reuind a_wa f4_reuind a_sup_set_class f5_reuind a_wceq a_wi a_wi p_syl f5_reuind f7_reuind a_wcel f0_reuind a_wa f6_reuind f7_reuind a_wcel f1_reuind a_wa a_wa f5_reuind f6_reuind a_wceq a_wi f4_reuind a_sup_set_class f6_reuind a_wceq f6_reuind f7_reuind a_wcel f1_reuind a_wa a_wa f5_reuind f7_reuind a_wcel f0_reuind a_wa f4_reuind a_sup_set_class f5_reuind a_wceq a_wi a_wi f2_reuind f3_reuind p_2alimi f4_reuind a_sup_set_class f6_reuind a_wceq f6_reuind f7_reuind a_wcel f1_reuind a_wa a_wa f5_reuind f7_reuind a_wcel f0_reuind a_wa f4_reuind a_sup_set_class f5_reuind a_wceq a_wi f3_reuind p_19.23v f4_reuind a_sup_set_class f6_reuind a_wceq f6_reuind f7_reuind a_wcel f1_reuind p_an12 f4_reuind a_sup_set_class f6_reuind f7_reuind p_eleq1 f4_reuind a_sup_set_class f6_reuind a_wceq f4_reuind a_sup_set_class f7_reuind a_wcel f6_reuind f7_reuind a_wcel a_wb f1_reuind p_adantr f4_reuind a_sup_set_class f6_reuind a_wceq f1_reuind a_wa f4_reuind a_sup_set_class f7_reuind a_wcel f6_reuind f7_reuind a_wcel p_pm5.32ri f4_reuind a_sup_set_class f6_reuind a_wceq f6_reuind f7_reuind a_wcel f1_reuind a_wa a_wa f6_reuind f7_reuind a_wcel f4_reuind a_sup_set_class f6_reuind a_wceq f1_reuind a_wa a_wa f4_reuind a_sup_set_class f7_reuind a_wcel f4_reuind a_sup_set_class f6_reuind a_wceq f1_reuind a_wa a_wa p_bitr4i f4_reuind a_sup_set_class f6_reuind a_wceq f6_reuind f7_reuind a_wcel f1_reuind a_wa a_wa f4_reuind a_sup_set_class f7_reuind a_wcel f4_reuind a_sup_set_class f6_reuind a_wceq f1_reuind a_wa a_wa f3_reuind p_exbii f4_reuind a_sup_set_class f7_reuind a_wcel f4_reuind a_sup_set_class f6_reuind a_wceq f1_reuind a_wa f3_reuind p_19.42v f4_reuind a_sup_set_class f6_reuind a_wceq f6_reuind f7_reuind a_wcel f1_reuind a_wa a_wa f3_reuind a_wex f4_reuind a_sup_set_class f7_reuind a_wcel f4_reuind a_sup_set_class f6_reuind a_wceq f1_reuind a_wa a_wa f3_reuind a_wex f4_reuind a_sup_set_class f7_reuind a_wcel f4_reuind a_sup_set_class f6_reuind a_wceq f1_reuind a_wa f3_reuind a_wex a_wa p_bitri f4_reuind a_sup_set_class f6_reuind a_wceq f6_reuind f7_reuind a_wcel f1_reuind a_wa a_wa f3_reuind a_wex f4_reuind a_sup_set_class f7_reuind a_wcel f4_reuind a_sup_set_class f6_reuind a_wceq f1_reuind a_wa f3_reuind a_wex a_wa f5_reuind f7_reuind a_wcel f0_reuind a_wa f4_reuind a_sup_set_class f5_reuind a_wceq a_wi p_imbi1i f4_reuind a_sup_set_class f6_reuind a_wceq f6_reuind f7_reuind a_wcel f1_reuind a_wa a_wa f5_reuind f7_reuind a_wcel f0_reuind a_wa f4_reuind a_sup_set_class f5_reuind a_wceq a_wi a_wi f3_reuind a_wal f4_reuind a_sup_set_class f6_reuind a_wceq f6_reuind f7_reuind a_wcel f1_reuind a_wa a_wa f3_reuind a_wex f5_reuind f7_reuind a_wcel f0_reuind a_wa f4_reuind a_sup_set_class f5_reuind a_wceq a_wi a_wi f4_reuind a_sup_set_class f7_reuind a_wcel f4_reuind a_sup_set_class f6_reuind a_wceq f1_reuind a_wa f3_reuind a_wex a_wa f5_reuind f7_reuind a_wcel f0_reuind a_wa f4_reuind a_sup_set_class f5_reuind a_wceq a_wi a_wi p_bitri f4_reuind a_sup_set_class f6_reuind a_wceq f6_reuind f7_reuind a_wcel f1_reuind a_wa a_wa f5_reuind f7_reuind a_wcel f0_reuind a_wa f4_reuind a_sup_set_class f5_reuind a_wceq a_wi a_wi f3_reuind a_wal f4_reuind a_sup_set_class f7_reuind a_wcel f4_reuind a_sup_set_class f6_reuind a_wceq f1_reuind a_wa f3_reuind a_wex a_wa f5_reuind f7_reuind a_wcel f0_reuind a_wa f4_reuind a_sup_set_class f5_reuind a_wceq a_wi a_wi f2_reuind p_albii f4_reuind a_sup_set_class f7_reuind a_wcel f4_reuind a_sup_set_class f6_reuind a_wceq f1_reuind a_wa f3_reuind a_wex a_wa f5_reuind f7_reuind a_wcel f0_reuind a_wa f4_reuind a_sup_set_class f5_reuind a_wceq a_wi f2_reuind p_19.21v f4_reuind a_sup_set_class f6_reuind a_wceq f6_reuind f7_reuind a_wcel f1_reuind a_wa a_wa f5_reuind f7_reuind a_wcel f0_reuind a_wa f4_reuind a_sup_set_class f5_reuind a_wceq a_wi a_wi f3_reuind a_wal f2_reuind a_wal f4_reuind a_sup_set_class f7_reuind a_wcel f4_reuind a_sup_set_class f6_reuind a_wceq f1_reuind a_wa f3_reuind a_wex a_wa f5_reuind f7_reuind a_wcel f0_reuind a_wa f4_reuind a_sup_set_class f5_reuind a_wceq a_wi a_wi f2_reuind a_wal f4_reuind a_sup_set_class f7_reuind a_wcel f4_reuind a_sup_set_class f6_reuind a_wceq f1_reuind a_wa f3_reuind a_wex a_wa f5_reuind f7_reuind a_wcel f0_reuind a_wa f4_reuind a_sup_set_class f5_reuind a_wceq a_wi f2_reuind a_wal a_wi p_bitri f5_reuind f7_reuind a_wcel f0_reuind a_wa f6_reuind f7_reuind a_wcel f1_reuind a_wa a_wa f5_reuind f6_reuind a_wceq a_wi f3_reuind a_wal f2_reuind a_wal f4_reuind a_sup_set_class f6_reuind a_wceq f6_reuind f7_reuind a_wcel f1_reuind a_wa a_wa f5_reuind f7_reuind a_wcel f0_reuind a_wa f4_reuind a_sup_set_class f5_reuind a_wceq a_wi a_wi f3_reuind a_wal f2_reuind a_wal f4_reuind a_sup_set_class f7_reuind a_wcel f4_reuind a_sup_set_class f6_reuind a_wceq f1_reuind a_wa f3_reuind a_wex a_wa f5_reuind f7_reuind a_wcel f0_reuind a_wa f4_reuind a_sup_set_class f5_reuind a_wceq a_wi f2_reuind a_wal a_wi p_sylib f5_reuind f7_reuind a_wcel f0_reuind a_wa f6_reuind f7_reuind a_wcel f1_reuind a_wa a_wa f5_reuind f6_reuind a_wceq a_wi f3_reuind a_wal f2_reuind a_wal f4_reuind a_sup_set_class f7_reuind a_wcel f4_reuind a_sup_set_class f6_reuind a_wceq f1_reuind a_wa f3_reuind a_wex f5_reuind f7_reuind a_wcel f0_reuind a_wa f4_reuind a_sup_set_class f5_reuind a_wceq a_wi f2_reuind a_wal p_exp3a f5_reuind f7_reuind a_wcel f0_reuind a_wa f6_reuind f7_reuind a_wcel f1_reuind a_wa a_wa f5_reuind f6_reuind a_wceq a_wi f3_reuind a_wal f2_reuind a_wal f4_reuind a_sup_set_class f6_reuind a_wceq f1_reuind a_wa f3_reuind a_wex f5_reuind f7_reuind a_wcel f0_reuind a_wa f4_reuind a_sup_set_class f5_reuind a_wceq a_wi f2_reuind a_wal f4_reuind f7_reuind p_reximdvai f5_reuind f7_reuind a_wcel f0_reuind a_wa f2_reuind a_wex f4_reuind a_sup_set_class f6_reuind a_wceq f1_reuind a_wa f3_reuind a_wex f4_reuind f7_reuind a_wrex f5_reuind f7_reuind a_wcel f0_reuind a_wa f6_reuind f7_reuind a_wcel f1_reuind a_wa a_wa f5_reuind f6_reuind a_wceq a_wi f3_reuind a_wal f2_reuind a_wal f5_reuind f7_reuind a_wcel f0_reuind a_wa f4_reuind a_sup_set_class f5_reuind a_wceq a_wi f2_reuind a_wal f4_reuind f7_reuind a_wrex p_syl5bi f5_reuind f7_reuind a_wcel f0_reuind a_wa f6_reuind f7_reuind a_wcel f1_reuind a_wa a_wa f5_reuind f6_reuind a_wceq a_wi f3_reuind a_wal f2_reuind a_wal f5_reuind f7_reuind a_wcel f0_reuind a_wa f2_reuind a_wex f5_reuind f7_reuind a_wcel f0_reuind a_wa f4_reuind a_sup_set_class f5_reuind a_wceq a_wi f2_reuind a_wal f4_reuind f7_reuind a_wrex p_imp f5_reuind f7_reuind a_wcel f0_reuind a_wa p_pm4.24 f5_reuind f7_reuind a_wcel f0_reuind a_wa f5_reuind f7_reuind a_wcel f0_reuind a_wa f5_reuind f7_reuind a_wcel f0_reuind a_wa a_wa p_biimpi f5_reuind f7_reuind a_wcel f0_reuind a_wa f4_reuind a_sup_set_class f5_reuind a_wceq f5_reuind f7_reuind a_wcel f0_reuind a_wa i0_reuind a_sup_set_class f5_reuind a_wceq p_prth f4_reuind a_sup_set_class i0_reuind a_sup_set_class f5_reuind p_eqtr3 f5_reuind f7_reuind a_wcel f0_reuind a_wa f5_reuind f7_reuind a_wcel f0_reuind a_wa f5_reuind f7_reuind a_wcel f0_reuind a_wa a_wa f5_reuind f7_reuind a_wcel f0_reuind a_wa f4_reuind a_sup_set_class f5_reuind a_wceq a_wi f5_reuind f7_reuind a_wcel f0_reuind a_wa i0_reuind a_sup_set_class f5_reuind a_wceq a_wi a_wa f4_reuind a_sup_set_class f5_reuind a_wceq i0_reuind a_sup_set_class f5_reuind a_wceq a_wa f4_reuind a_sup_set_class i0_reuind a_sup_set_class a_wceq p_syl56 f5_reuind f7_reuind a_wcel f0_reuind a_wa f4_reuind a_sup_set_class f5_reuind a_wceq a_wi f5_reuind f7_reuind a_wcel f0_reuind a_wa i0_reuind a_sup_set_class f5_reuind a_wceq a_wi f5_reuind f7_reuind a_wcel f0_reuind a_wa f4_reuind a_sup_set_class i0_reuind a_sup_set_class a_wceq a_wi f2_reuind p_alanimi f5_reuind f7_reuind a_wcel f0_reuind a_wa f4_reuind a_sup_set_class i0_reuind a_sup_set_class a_wceq f2_reuind p_19.23v f5_reuind f7_reuind a_wcel f0_reuind a_wa f4_reuind a_sup_set_class i0_reuind a_sup_set_class a_wceq a_wi f2_reuind a_wal f5_reuind f7_reuind a_wcel f0_reuind a_wa f2_reuind a_wex f4_reuind a_sup_set_class i0_reuind a_sup_set_class a_wceq a_wi p_biimpi f5_reuind f7_reuind a_wcel f0_reuind a_wa f4_reuind a_sup_set_class i0_reuind a_sup_set_class a_wceq a_wi f2_reuind a_wal f5_reuind f7_reuind a_wcel f0_reuind a_wa f2_reuind a_wex f4_reuind a_sup_set_class i0_reuind a_sup_set_class a_wceq p_com12 f5_reuind f7_reuind a_wcel f0_reuind a_wa f4_reuind a_sup_set_class f5_reuind a_wceq a_wi f2_reuind a_wal f5_reuind f7_reuind a_wcel f0_reuind a_wa i0_reuind a_sup_set_class f5_reuind a_wceq a_wi f2_reuind a_wal a_wa f5_reuind f7_reuind a_wcel f0_reuind a_wa f4_reuind a_sup_set_class i0_reuind a_sup_set_class a_wceq a_wi f2_reuind a_wal f5_reuind f7_reuind a_wcel f0_reuind a_wa f2_reuind a_wex f4_reuind a_sup_set_class i0_reuind a_sup_set_class a_wceq p_syl5 f5_reuind f7_reuind a_wcel f0_reuind a_wa f2_reuind a_wex f5_reuind f7_reuind a_wcel f0_reuind a_wa f4_reuind a_sup_set_class f5_reuind a_wceq a_wi f2_reuind a_wal f5_reuind f7_reuind a_wcel f0_reuind a_wa i0_reuind a_sup_set_class f5_reuind a_wceq a_wi f2_reuind a_wal a_wa f4_reuind a_sup_set_class i0_reuind a_sup_set_class a_wceq a_wi f4_reuind a_sup_set_class f7_reuind a_wcel i0_reuind a_sup_set_class f7_reuind a_wcel a_wa p_a1d f5_reuind f7_reuind a_wcel f0_reuind a_wa f2_reuind a_wex f5_reuind f7_reuind a_wcel f0_reuind a_wa f4_reuind a_sup_set_class f5_reuind a_wceq a_wi f2_reuind a_wal f5_reuind f7_reuind a_wcel f0_reuind a_wa i0_reuind a_sup_set_class f5_reuind a_wceq a_wi f2_reuind a_wal a_wa f4_reuind a_sup_set_class i0_reuind a_sup_set_class a_wceq a_wi f4_reuind i0_reuind f7_reuind f7_reuind p_ralrimivv f5_reuind f7_reuind a_wcel f0_reuind a_wa f2_reuind a_wex f5_reuind f7_reuind a_wcel f0_reuind a_wa f4_reuind a_sup_set_class f5_reuind a_wceq a_wi f2_reuind a_wal f5_reuind f7_reuind a_wcel f0_reuind a_wa i0_reuind a_sup_set_class f5_reuind a_wceq a_wi f2_reuind a_wal a_wa f4_reuind a_sup_set_class i0_reuind a_sup_set_class a_wceq a_wi i0_reuind f7_reuind a_wral f4_reuind f7_reuind a_wral f5_reuind f7_reuind a_wcel f0_reuind a_wa f6_reuind f7_reuind a_wcel f1_reuind a_wa a_wa f5_reuind f6_reuind a_wceq a_wi f3_reuind a_wal f2_reuind a_wal p_adantl f4_reuind a_sup_set_class i0_reuind a_sup_set_class f5_reuind p_eqeq1 f4_reuind a_sup_set_class i0_reuind a_sup_set_class a_wceq f4_reuind a_sup_set_class f5_reuind a_wceq i0_reuind a_sup_set_class f5_reuind a_wceq f5_reuind f7_reuind a_wcel f0_reuind a_wa p_imbi2d f4_reuind a_sup_set_class i0_reuind a_sup_set_class a_wceq f5_reuind f7_reuind a_wcel f0_reuind a_wa f4_reuind a_sup_set_class f5_reuind a_wceq a_wi f5_reuind f7_reuind a_wcel f0_reuind a_wa i0_reuind a_sup_set_class f5_reuind a_wceq a_wi f2_reuind p_albidv f5_reuind f7_reuind a_wcel f0_reuind a_wa f4_reuind a_sup_set_class f5_reuind a_wceq a_wi f2_reuind a_wal f5_reuind f7_reuind a_wcel f0_reuind a_wa i0_reuind a_sup_set_class f5_reuind a_wceq a_wi f2_reuind a_wal f4_reuind i0_reuind f7_reuind p_reu4 f5_reuind f7_reuind a_wcel f0_reuind a_wa f6_reuind f7_reuind a_wcel f1_reuind a_wa a_wa f5_reuind f6_reuind a_wceq a_wi f3_reuind a_wal f2_reuind a_wal f5_reuind f7_reuind a_wcel f0_reuind a_wa f2_reuind a_wex a_wa f5_reuind f7_reuind a_wcel f0_reuind a_wa f4_reuind a_sup_set_class f5_reuind a_wceq a_wi f2_reuind a_wal f4_reuind f7_reuind a_wrex f5_reuind f7_reuind a_wcel f0_reuind a_wa f4_reuind a_sup_set_class f5_reuind a_wceq a_wi f2_reuind a_wal f5_reuind f7_reuind a_wcel f0_reuind a_wa i0_reuind a_sup_set_class f5_reuind a_wceq a_wi f2_reuind a_wal a_wa f4_reuind a_sup_set_class i0_reuind a_sup_set_class a_wceq a_wi i0_reuind f7_reuind a_wral f4_reuind f7_reuind a_wral f5_reuind f7_reuind a_wcel f0_reuind a_wa f4_reuind a_sup_set_class f5_reuind a_wceq a_wi f2_reuind a_wal f4_reuind f7_reuind a_wreu p_sylanbrc $.
$}

$(Double restricted quantification with "at most one," analogous to
       ~ 2moex .  (Contributed by Alexander van der Vekens, 17-Jun-2017.) $)

${
	$v ph x y A B  $.
	$d y A  $.
	$d x B  $.
	$d x y  $.
	f0_2rmorex $f wff ph $.
	f1_2rmorex $f set x $.
	f2_2rmorex $f set y $.
	f3_2rmorex $f class A $.
	f4_2rmorex $f class B $.
	p_2rmorex $p |- ( E* x e. A E. y e. B ph -> A. y e. B E* x e. A ph ) $= f2_2rmorex f3_2rmorex p_nfcv f0_2rmorex f2_2rmorex f4_2rmorex p_nfre1 f0_2rmorex f2_2rmorex f4_2rmorex a_wrex f2_2rmorex f1_2rmorex f3_2rmorex p_nfrmo f0_2rmorex f2_2rmorex f4_2rmorex p_rspe f2_2rmorex a_sup_set_class f4_2rmorex a_wcel f0_2rmorex f0_2rmorex f2_2rmorex f4_2rmorex a_wrex p_ex f2_2rmorex a_sup_set_class f4_2rmorex a_wcel f0_2rmorex f0_2rmorex f2_2rmorex f4_2rmorex a_wrex a_wi f1_2rmorex f3_2rmorex p_ralrimivw f0_2rmorex f0_2rmorex f2_2rmorex f4_2rmorex a_wrex f1_2rmorex f3_2rmorex p_rmoim f2_2rmorex a_sup_set_class f4_2rmorex a_wcel f0_2rmorex f0_2rmorex f2_2rmorex f4_2rmorex a_wrex a_wi f1_2rmorex f3_2rmorex a_wral f0_2rmorex f2_2rmorex f4_2rmorex a_wrex f1_2rmorex f3_2rmorex a_wrmo f0_2rmorex f1_2rmorex f3_2rmorex a_wrmo a_wi p_syl f2_2rmorex a_sup_set_class f4_2rmorex a_wcel f0_2rmorex f2_2rmorex f4_2rmorex a_wrex f1_2rmorex f3_2rmorex a_wrmo f0_2rmorex f1_2rmorex f3_2rmorex a_wrmo p_com12 f0_2rmorex f2_2rmorex f4_2rmorex a_wrex f1_2rmorex f3_2rmorex a_wrmo f0_2rmorex f1_2rmorex f3_2rmorex a_wrmo f2_2rmorex f4_2rmorex p_ralrimi $.
$}

$(Lemma for ~ 2reu5 .  Note that ` E! x e. A E! y e. B ph ` does not mean
       "there is exactly one ` x ` in ` A ` and exactly one ` y ` in ` B ` such
       that ` ph ` holds;" see comment for ~ 2eu5 .  (Contributed by Alexander
       van der Vekens, 17-Jun-2017.) $)

${
	$v ph x y A B  $.
	$d y A  $.
	$d x B  $.
	$d x y  $.
	f0_2reu5lem1 $f wff ph $.
	f1_2reu5lem1 $f set x $.
	f2_2reu5lem1 $f set y $.
	f3_2reu5lem1 $f class A $.
	f4_2reu5lem1 $f class B $.
	p_2reu5lem1 $p |- ( E! x e. A E! y e. B ph <-> E! x E! y ( x e. A /\ y e. B /\ ph ) ) $= f0_2reu5lem1 f2_2reu5lem1 f4_2reu5lem1 a_df-reu f0_2reu5lem1 f2_2reu5lem1 f4_2reu5lem1 a_wreu f2_2reu5lem1 a_sup_set_class f4_2reu5lem1 a_wcel f0_2reu5lem1 a_wa f2_2reu5lem1 a_weu f1_2reu5lem1 f3_2reu5lem1 p_reubii f2_2reu5lem1 a_sup_set_class f4_2reu5lem1 a_wcel f0_2reu5lem1 a_wa f2_2reu5lem1 a_weu f1_2reu5lem1 f3_2reu5lem1 a_df-reu f1_2reu5lem1 a_sup_set_class f3_2reu5lem1 a_wcel f2_2reu5lem1 a_sup_set_class f4_2reu5lem1 a_wcel f0_2reu5lem1 a_wa f2_2reu5lem1 p_euanv f1_2reu5lem1 a_sup_set_class f3_2reu5lem1 a_wcel f2_2reu5lem1 a_sup_set_class f4_2reu5lem1 a_wcel f0_2reu5lem1 a_wa a_wa f2_2reu5lem1 a_weu f1_2reu5lem1 a_sup_set_class f3_2reu5lem1 a_wcel f2_2reu5lem1 a_sup_set_class f4_2reu5lem1 a_wcel f0_2reu5lem1 a_wa f2_2reu5lem1 a_weu a_wa p_bicomi f1_2reu5lem1 a_sup_set_class f3_2reu5lem1 a_wcel f2_2reu5lem1 a_sup_set_class f4_2reu5lem1 a_wcel f0_2reu5lem1 p_3anass f1_2reu5lem1 a_sup_set_class f3_2reu5lem1 a_wcel f2_2reu5lem1 a_sup_set_class f4_2reu5lem1 a_wcel f0_2reu5lem1 a_w3a f1_2reu5lem1 a_sup_set_class f3_2reu5lem1 a_wcel f2_2reu5lem1 a_sup_set_class f4_2reu5lem1 a_wcel f0_2reu5lem1 a_wa a_wa p_bicomi f1_2reu5lem1 a_sup_set_class f3_2reu5lem1 a_wcel f2_2reu5lem1 a_sup_set_class f4_2reu5lem1 a_wcel f0_2reu5lem1 a_wa a_wa f1_2reu5lem1 a_sup_set_class f3_2reu5lem1 a_wcel f2_2reu5lem1 a_sup_set_class f4_2reu5lem1 a_wcel f0_2reu5lem1 a_w3a f2_2reu5lem1 p_eubii f1_2reu5lem1 a_sup_set_class f3_2reu5lem1 a_wcel f2_2reu5lem1 a_sup_set_class f4_2reu5lem1 a_wcel f0_2reu5lem1 a_wa f2_2reu5lem1 a_weu a_wa f1_2reu5lem1 a_sup_set_class f3_2reu5lem1 a_wcel f2_2reu5lem1 a_sup_set_class f4_2reu5lem1 a_wcel f0_2reu5lem1 a_wa a_wa f2_2reu5lem1 a_weu f1_2reu5lem1 a_sup_set_class f3_2reu5lem1 a_wcel f2_2reu5lem1 a_sup_set_class f4_2reu5lem1 a_wcel f0_2reu5lem1 a_w3a f2_2reu5lem1 a_weu p_bitri f1_2reu5lem1 a_sup_set_class f3_2reu5lem1 a_wcel f2_2reu5lem1 a_sup_set_class f4_2reu5lem1 a_wcel f0_2reu5lem1 a_wa f2_2reu5lem1 a_weu a_wa f1_2reu5lem1 a_sup_set_class f3_2reu5lem1 a_wcel f2_2reu5lem1 a_sup_set_class f4_2reu5lem1 a_wcel f0_2reu5lem1 a_w3a f2_2reu5lem1 a_weu f1_2reu5lem1 p_eubii f2_2reu5lem1 a_sup_set_class f4_2reu5lem1 a_wcel f0_2reu5lem1 a_wa f2_2reu5lem1 a_weu f1_2reu5lem1 f3_2reu5lem1 a_wreu f1_2reu5lem1 a_sup_set_class f3_2reu5lem1 a_wcel f2_2reu5lem1 a_sup_set_class f4_2reu5lem1 a_wcel f0_2reu5lem1 a_wa f2_2reu5lem1 a_weu a_wa f1_2reu5lem1 a_weu f1_2reu5lem1 a_sup_set_class f3_2reu5lem1 a_wcel f2_2reu5lem1 a_sup_set_class f4_2reu5lem1 a_wcel f0_2reu5lem1 a_w3a f2_2reu5lem1 a_weu f1_2reu5lem1 a_weu p_bitri f0_2reu5lem1 f2_2reu5lem1 f4_2reu5lem1 a_wreu f1_2reu5lem1 f3_2reu5lem1 a_wreu f2_2reu5lem1 a_sup_set_class f4_2reu5lem1 a_wcel f0_2reu5lem1 a_wa f2_2reu5lem1 a_weu f1_2reu5lem1 f3_2reu5lem1 a_wreu f1_2reu5lem1 a_sup_set_class f3_2reu5lem1 a_wcel f2_2reu5lem1 a_sup_set_class f4_2reu5lem1 a_wcel f0_2reu5lem1 a_w3a f2_2reu5lem1 a_weu f1_2reu5lem1 a_weu p_bitri $.
$}

$(Lemma for ~ 2reu5 .  (Contributed by Alexander van der Vekens,
       17-Jun-2017.) $)

${
	$v ph x y A B  $.
	$d y A  $.
	$d x B  $.
	$d x y  $.
	f0_2reu5lem2 $f wff ph $.
	f1_2reu5lem2 $f set x $.
	f2_2reu5lem2 $f set y $.
	f3_2reu5lem2 $f class A $.
	f4_2reu5lem2 $f class B $.
	p_2reu5lem2 $p |- ( A. x e. A E* y e. B ph <-> A. x E* y ( x e. A /\ y e. B /\ ph ) ) $= f0_2reu5lem2 f2_2reu5lem2 f4_2reu5lem2 a_df-rmo f0_2reu5lem2 f2_2reu5lem2 f4_2reu5lem2 a_wrmo f2_2reu5lem2 a_sup_set_class f4_2reu5lem2 a_wcel f0_2reu5lem2 a_wa f2_2reu5lem2 a_wmo f1_2reu5lem2 f3_2reu5lem2 p_ralbii f2_2reu5lem2 a_sup_set_class f4_2reu5lem2 a_wcel f0_2reu5lem2 a_wa f2_2reu5lem2 a_wmo f1_2reu5lem2 f3_2reu5lem2 a_df-ral f1_2reu5lem2 a_sup_set_class f3_2reu5lem2 a_wcel f2_2reu5lem2 a_sup_set_class f4_2reu5lem2 a_wcel f0_2reu5lem2 a_wa f2_2reu5lem2 p_moanimv f1_2reu5lem2 a_sup_set_class f3_2reu5lem2 a_wcel f2_2reu5lem2 a_sup_set_class f4_2reu5lem2 a_wcel f0_2reu5lem2 a_wa a_wa f2_2reu5lem2 a_wmo f1_2reu5lem2 a_sup_set_class f3_2reu5lem2 a_wcel f2_2reu5lem2 a_sup_set_class f4_2reu5lem2 a_wcel f0_2reu5lem2 a_wa f2_2reu5lem2 a_wmo a_wi p_bicomi f1_2reu5lem2 a_sup_set_class f3_2reu5lem2 a_wcel f2_2reu5lem2 a_sup_set_class f4_2reu5lem2 a_wcel f0_2reu5lem2 p_3anass f1_2reu5lem2 a_sup_set_class f3_2reu5lem2 a_wcel f2_2reu5lem2 a_sup_set_class f4_2reu5lem2 a_wcel f0_2reu5lem2 a_w3a f1_2reu5lem2 a_sup_set_class f3_2reu5lem2 a_wcel f2_2reu5lem2 a_sup_set_class f4_2reu5lem2 a_wcel f0_2reu5lem2 a_wa a_wa p_bicomi f1_2reu5lem2 a_sup_set_class f3_2reu5lem2 a_wcel f2_2reu5lem2 a_sup_set_class f4_2reu5lem2 a_wcel f0_2reu5lem2 a_wa a_wa f1_2reu5lem2 a_sup_set_class f3_2reu5lem2 a_wcel f2_2reu5lem2 a_sup_set_class f4_2reu5lem2 a_wcel f0_2reu5lem2 a_w3a f2_2reu5lem2 p_mobii f1_2reu5lem2 a_sup_set_class f3_2reu5lem2 a_wcel f2_2reu5lem2 a_sup_set_class f4_2reu5lem2 a_wcel f0_2reu5lem2 a_wa f2_2reu5lem2 a_wmo a_wi f1_2reu5lem2 a_sup_set_class f3_2reu5lem2 a_wcel f2_2reu5lem2 a_sup_set_class f4_2reu5lem2 a_wcel f0_2reu5lem2 a_wa a_wa f2_2reu5lem2 a_wmo f1_2reu5lem2 a_sup_set_class f3_2reu5lem2 a_wcel f2_2reu5lem2 a_sup_set_class f4_2reu5lem2 a_wcel f0_2reu5lem2 a_w3a f2_2reu5lem2 a_wmo p_bitri f1_2reu5lem2 a_sup_set_class f3_2reu5lem2 a_wcel f2_2reu5lem2 a_sup_set_class f4_2reu5lem2 a_wcel f0_2reu5lem2 a_wa f2_2reu5lem2 a_wmo a_wi f1_2reu5lem2 a_sup_set_class f3_2reu5lem2 a_wcel f2_2reu5lem2 a_sup_set_class f4_2reu5lem2 a_wcel f0_2reu5lem2 a_w3a f2_2reu5lem2 a_wmo f1_2reu5lem2 p_albii f2_2reu5lem2 a_sup_set_class f4_2reu5lem2 a_wcel f0_2reu5lem2 a_wa f2_2reu5lem2 a_wmo f1_2reu5lem2 f3_2reu5lem2 a_wral f1_2reu5lem2 a_sup_set_class f3_2reu5lem2 a_wcel f2_2reu5lem2 a_sup_set_class f4_2reu5lem2 a_wcel f0_2reu5lem2 a_wa f2_2reu5lem2 a_wmo a_wi f1_2reu5lem2 a_wal f1_2reu5lem2 a_sup_set_class f3_2reu5lem2 a_wcel f2_2reu5lem2 a_sup_set_class f4_2reu5lem2 a_wcel f0_2reu5lem2 a_w3a f2_2reu5lem2 a_wmo f1_2reu5lem2 a_wal p_bitri f0_2reu5lem2 f2_2reu5lem2 f4_2reu5lem2 a_wrmo f1_2reu5lem2 f3_2reu5lem2 a_wral f2_2reu5lem2 a_sup_set_class f4_2reu5lem2 a_wcel f0_2reu5lem2 a_wa f2_2reu5lem2 a_wmo f1_2reu5lem2 f3_2reu5lem2 a_wral f1_2reu5lem2 a_sup_set_class f3_2reu5lem2 a_wcel f2_2reu5lem2 a_sup_set_class f4_2reu5lem2 a_wcel f0_2reu5lem2 a_w3a f2_2reu5lem2 a_wmo f1_2reu5lem2 a_wal p_bitri $.
$}

$(Lemma for ~ 2reu5 .  This lemma is interesting in its own right, showing
       that existential restriction in the last conjunct (the "at most one"
       part) is optional; compare ~ rmo2 .  (Contributed by Alexander van der
       Vekens, 17-Jun-2017.) $)

${
	$v ph x y z w A B  $.
	$d w y z A  $.
	$d w x z B  $.
	$d x y  $.
	$d ph w  $.
	$d ph z  $.
	f0_2reu5lem3 $f wff ph $.
	f1_2reu5lem3 $f set x $.
	f2_2reu5lem3 $f set y $.
	f3_2reu5lem3 $f set z $.
	f4_2reu5lem3 $f set w $.
	f5_2reu5lem3 $f class A $.
	f6_2reu5lem3 $f class B $.
	p_2reu5lem3 $p |- ( ( E! x e. A E! y e. B ph /\ A. x e. A E* y e. B ph ) <-> ( E. x e. A E. y e. B ph /\ E. z E. w A. x e. A A. y e. B ( ph -> ( x = z /\ y = w ) ) ) ) $= f0_2reu5lem3 f1_2reu5lem3 f2_2reu5lem3 f5_2reu5lem3 f6_2reu5lem3 p_2reu5lem1 f0_2reu5lem3 f1_2reu5lem3 f2_2reu5lem3 f5_2reu5lem3 f6_2reu5lem3 p_2reu5lem2 f0_2reu5lem3 f2_2reu5lem3 f6_2reu5lem3 a_wreu f1_2reu5lem3 f5_2reu5lem3 a_wreu f1_2reu5lem3 a_sup_set_class f5_2reu5lem3 a_wcel f2_2reu5lem3 a_sup_set_class f6_2reu5lem3 a_wcel f0_2reu5lem3 a_w3a f2_2reu5lem3 a_weu f1_2reu5lem3 a_weu f0_2reu5lem3 f2_2reu5lem3 f6_2reu5lem3 a_wrmo f1_2reu5lem3 f5_2reu5lem3 a_wral f1_2reu5lem3 a_sup_set_class f5_2reu5lem3 a_wcel f2_2reu5lem3 a_sup_set_class f6_2reu5lem3 a_wcel f0_2reu5lem3 a_w3a f2_2reu5lem3 a_wmo f1_2reu5lem3 a_wal p_anbi12i f1_2reu5lem3 a_sup_set_class f5_2reu5lem3 a_wcel f2_2reu5lem3 a_sup_set_class f6_2reu5lem3 a_wcel f0_2reu5lem3 a_w3a f1_2reu5lem3 f2_2reu5lem3 f3_2reu5lem3 f4_2reu5lem3 p_2eu5 f1_2reu5lem3 a_sup_set_class f5_2reu5lem3 a_wcel f2_2reu5lem3 a_sup_set_class f6_2reu5lem3 a_wcel f0_2reu5lem3 p_3anass f1_2reu5lem3 a_sup_set_class f5_2reu5lem3 a_wcel f2_2reu5lem3 a_sup_set_class f6_2reu5lem3 a_wcel f0_2reu5lem3 a_w3a f1_2reu5lem3 a_sup_set_class f5_2reu5lem3 a_wcel f2_2reu5lem3 a_sup_set_class f6_2reu5lem3 a_wcel f0_2reu5lem3 a_wa a_wa f2_2reu5lem3 p_exbii f1_2reu5lem3 a_sup_set_class f5_2reu5lem3 a_wcel f2_2reu5lem3 a_sup_set_class f6_2reu5lem3 a_wcel f0_2reu5lem3 a_wa f2_2reu5lem3 p_19.42v f0_2reu5lem3 f2_2reu5lem3 f6_2reu5lem3 a_df-rex f0_2reu5lem3 f2_2reu5lem3 f6_2reu5lem3 a_wrex f2_2reu5lem3 a_sup_set_class f6_2reu5lem3 a_wcel f0_2reu5lem3 a_wa f2_2reu5lem3 a_wex p_bicomi f2_2reu5lem3 a_sup_set_class f6_2reu5lem3 a_wcel f0_2reu5lem3 a_wa f2_2reu5lem3 a_wex f0_2reu5lem3 f2_2reu5lem3 f6_2reu5lem3 a_wrex f1_2reu5lem3 a_sup_set_class f5_2reu5lem3 a_wcel p_anbi2i f1_2reu5lem3 a_sup_set_class f5_2reu5lem3 a_wcel f2_2reu5lem3 a_sup_set_class f6_2reu5lem3 a_wcel f0_2reu5lem3 a_w3a f2_2reu5lem3 a_wex f1_2reu5lem3 a_sup_set_class f5_2reu5lem3 a_wcel f2_2reu5lem3 a_sup_set_class f6_2reu5lem3 a_wcel f0_2reu5lem3 a_wa a_wa f2_2reu5lem3 a_wex f1_2reu5lem3 a_sup_set_class f5_2reu5lem3 a_wcel f2_2reu5lem3 a_sup_set_class f6_2reu5lem3 a_wcel f0_2reu5lem3 a_wa f2_2reu5lem3 a_wex a_wa f1_2reu5lem3 a_sup_set_class f5_2reu5lem3 a_wcel f0_2reu5lem3 f2_2reu5lem3 f6_2reu5lem3 a_wrex a_wa p_3bitri f1_2reu5lem3 a_sup_set_class f5_2reu5lem3 a_wcel f2_2reu5lem3 a_sup_set_class f6_2reu5lem3 a_wcel f0_2reu5lem3 a_w3a f2_2reu5lem3 a_wex f1_2reu5lem3 a_sup_set_class f5_2reu5lem3 a_wcel f0_2reu5lem3 f2_2reu5lem3 f6_2reu5lem3 a_wrex a_wa f1_2reu5lem3 p_exbii f0_2reu5lem3 f2_2reu5lem3 f6_2reu5lem3 a_wrex f1_2reu5lem3 f5_2reu5lem3 a_df-rex f1_2reu5lem3 a_sup_set_class f5_2reu5lem3 a_wcel f2_2reu5lem3 a_sup_set_class f6_2reu5lem3 a_wcel f0_2reu5lem3 a_w3a f2_2reu5lem3 a_wex f1_2reu5lem3 a_wex f1_2reu5lem3 a_sup_set_class f5_2reu5lem3 a_wcel f0_2reu5lem3 f2_2reu5lem3 f6_2reu5lem3 a_wrex a_wa f1_2reu5lem3 a_wex f0_2reu5lem3 f2_2reu5lem3 f6_2reu5lem3 a_wrex f1_2reu5lem3 f5_2reu5lem3 a_wrex p_bitr4i f1_2reu5lem3 a_sup_set_class f5_2reu5lem3 a_wcel f2_2reu5lem3 a_sup_set_class f6_2reu5lem3 a_wcel f0_2reu5lem3 p_3anan12 f1_2reu5lem3 a_sup_set_class f5_2reu5lem3 a_wcel f2_2reu5lem3 a_sup_set_class f6_2reu5lem3 a_wcel f0_2reu5lem3 a_w3a f2_2reu5lem3 a_sup_set_class f6_2reu5lem3 a_wcel f1_2reu5lem3 a_sup_set_class f5_2reu5lem3 a_wcel f0_2reu5lem3 a_wa a_wa f1_2reu5lem3 a_sup_set_class f3_2reu5lem3 a_sup_set_class a_wceq f2_2reu5lem3 a_sup_set_class f4_2reu5lem3 a_sup_set_class a_wceq a_wa p_imbi1i f2_2reu5lem3 a_sup_set_class f6_2reu5lem3 a_wcel f1_2reu5lem3 a_sup_set_class f5_2reu5lem3 a_wcel f0_2reu5lem3 a_wa f1_2reu5lem3 a_sup_set_class f3_2reu5lem3 a_sup_set_class a_wceq f2_2reu5lem3 a_sup_set_class f4_2reu5lem3 a_sup_set_class a_wceq a_wa p_impexp f1_2reu5lem3 a_sup_set_class f5_2reu5lem3 a_wcel f0_2reu5lem3 f1_2reu5lem3 a_sup_set_class f3_2reu5lem3 a_sup_set_class a_wceq f2_2reu5lem3 a_sup_set_class f4_2reu5lem3 a_sup_set_class a_wceq a_wa p_impexp f1_2reu5lem3 a_sup_set_class f5_2reu5lem3 a_wcel f0_2reu5lem3 a_wa f1_2reu5lem3 a_sup_set_class f3_2reu5lem3 a_sup_set_class a_wceq f2_2reu5lem3 a_sup_set_class f4_2reu5lem3 a_sup_set_class a_wceq a_wa a_wi f1_2reu5lem3 a_sup_set_class f5_2reu5lem3 a_wcel f0_2reu5lem3 f1_2reu5lem3 a_sup_set_class f3_2reu5lem3 a_sup_set_class a_wceq f2_2reu5lem3 a_sup_set_class f4_2reu5lem3 a_sup_set_class a_wceq a_wa a_wi a_wi f2_2reu5lem3 a_sup_set_class f6_2reu5lem3 a_wcel p_imbi2i f1_2reu5lem3 a_sup_set_class f5_2reu5lem3 a_wcel f2_2reu5lem3 a_sup_set_class f6_2reu5lem3 a_wcel f0_2reu5lem3 a_w3a f1_2reu5lem3 a_sup_set_class f3_2reu5lem3 a_sup_set_class a_wceq f2_2reu5lem3 a_sup_set_class f4_2reu5lem3 a_sup_set_class a_wceq a_wa a_wi f2_2reu5lem3 a_sup_set_class f6_2reu5lem3 a_wcel f1_2reu5lem3 a_sup_set_class f5_2reu5lem3 a_wcel f0_2reu5lem3 a_wa a_wa f1_2reu5lem3 a_sup_set_class f3_2reu5lem3 a_sup_set_class a_wceq f2_2reu5lem3 a_sup_set_class f4_2reu5lem3 a_sup_set_class a_wceq a_wa a_wi f2_2reu5lem3 a_sup_set_class f6_2reu5lem3 a_wcel f1_2reu5lem3 a_sup_set_class f5_2reu5lem3 a_wcel f0_2reu5lem3 a_wa f1_2reu5lem3 a_sup_set_class f3_2reu5lem3 a_sup_set_class a_wceq f2_2reu5lem3 a_sup_set_class f4_2reu5lem3 a_sup_set_class a_wceq a_wa a_wi a_wi f2_2reu5lem3 a_sup_set_class f6_2reu5lem3 a_wcel f1_2reu5lem3 a_sup_set_class f5_2reu5lem3 a_wcel f0_2reu5lem3 f1_2reu5lem3 a_sup_set_class f3_2reu5lem3 a_sup_set_class a_wceq f2_2reu5lem3 a_sup_set_class f4_2reu5lem3 a_sup_set_class a_wceq a_wa a_wi a_wi a_wi p_3bitri f1_2reu5lem3 a_sup_set_class f5_2reu5lem3 a_wcel f2_2reu5lem3 a_sup_set_class f6_2reu5lem3 a_wcel f0_2reu5lem3 a_w3a f1_2reu5lem3 a_sup_set_class f3_2reu5lem3 a_sup_set_class a_wceq f2_2reu5lem3 a_sup_set_class f4_2reu5lem3 a_sup_set_class a_wceq a_wa a_wi f2_2reu5lem3 a_sup_set_class f6_2reu5lem3 a_wcel f1_2reu5lem3 a_sup_set_class f5_2reu5lem3 a_wcel f0_2reu5lem3 f1_2reu5lem3 a_sup_set_class f3_2reu5lem3 a_sup_set_class a_wceq f2_2reu5lem3 a_sup_set_class f4_2reu5lem3 a_sup_set_class a_wceq a_wa a_wi a_wi a_wi f2_2reu5lem3 p_albii f1_2reu5lem3 a_sup_set_class f5_2reu5lem3 a_wcel f0_2reu5lem3 f1_2reu5lem3 a_sup_set_class f3_2reu5lem3 a_sup_set_class a_wceq f2_2reu5lem3 a_sup_set_class f4_2reu5lem3 a_sup_set_class a_wceq a_wa a_wi a_wi f2_2reu5lem3 f6_2reu5lem3 a_df-ral f1_2reu5lem3 a_sup_set_class f5_2reu5lem3 a_wcel f0_2reu5lem3 f1_2reu5lem3 a_sup_set_class f3_2reu5lem3 a_sup_set_class a_wceq f2_2reu5lem3 a_sup_set_class f4_2reu5lem3 a_sup_set_class a_wceq a_wa a_wi f2_2reu5lem3 f6_2reu5lem3 p_r19.21v f1_2reu5lem3 a_sup_set_class f5_2reu5lem3 a_wcel f2_2reu5lem3 a_sup_set_class f6_2reu5lem3 a_wcel f0_2reu5lem3 a_w3a f1_2reu5lem3 a_sup_set_class f3_2reu5lem3 a_sup_set_class a_wceq f2_2reu5lem3 a_sup_set_class f4_2reu5lem3 a_sup_set_class a_wceq a_wa a_wi f2_2reu5lem3 a_wal f2_2reu5lem3 a_sup_set_class f6_2reu5lem3 a_wcel f1_2reu5lem3 a_sup_set_class f5_2reu5lem3 a_wcel f0_2reu5lem3 f1_2reu5lem3 a_sup_set_class f3_2reu5lem3 a_sup_set_class a_wceq f2_2reu5lem3 a_sup_set_class f4_2reu5lem3 a_sup_set_class a_wceq a_wa a_wi a_wi a_wi f2_2reu5lem3 a_wal f1_2reu5lem3 a_sup_set_class f5_2reu5lem3 a_wcel f0_2reu5lem3 f1_2reu5lem3 a_sup_set_class f3_2reu5lem3 a_sup_set_class a_wceq f2_2reu5lem3 a_sup_set_class f4_2reu5lem3 a_sup_set_class a_wceq a_wa a_wi a_wi f2_2reu5lem3 f6_2reu5lem3 a_wral f1_2reu5lem3 a_sup_set_class f5_2reu5lem3 a_wcel f0_2reu5lem3 f1_2reu5lem3 a_sup_set_class f3_2reu5lem3 a_sup_set_class a_wceq f2_2reu5lem3 a_sup_set_class f4_2reu5lem3 a_sup_set_class a_wceq a_wa a_wi f2_2reu5lem3 f6_2reu5lem3 a_wral a_wi p_3bitr2i f1_2reu5lem3 a_sup_set_class f5_2reu5lem3 a_wcel f2_2reu5lem3 a_sup_set_class f6_2reu5lem3 a_wcel f0_2reu5lem3 a_w3a f1_2reu5lem3 a_sup_set_class f3_2reu5lem3 a_sup_set_class a_wceq f2_2reu5lem3 a_sup_set_class f4_2reu5lem3 a_sup_set_class a_wceq a_wa a_wi f2_2reu5lem3 a_wal f1_2reu5lem3 a_sup_set_class f5_2reu5lem3 a_wcel f0_2reu5lem3 f1_2reu5lem3 a_sup_set_class f3_2reu5lem3 a_sup_set_class a_wceq f2_2reu5lem3 a_sup_set_class f4_2reu5lem3 a_sup_set_class a_wceq a_wa a_wi f2_2reu5lem3 f6_2reu5lem3 a_wral a_wi f1_2reu5lem3 p_albii f0_2reu5lem3 f1_2reu5lem3 a_sup_set_class f3_2reu5lem3 a_sup_set_class a_wceq f2_2reu5lem3 a_sup_set_class f4_2reu5lem3 a_sup_set_class a_wceq a_wa a_wi f2_2reu5lem3 f6_2reu5lem3 a_wral f1_2reu5lem3 f5_2reu5lem3 a_df-ral f1_2reu5lem3 a_sup_set_class f5_2reu5lem3 a_wcel f2_2reu5lem3 a_sup_set_class f6_2reu5lem3 a_wcel f0_2reu5lem3 a_w3a f1_2reu5lem3 a_sup_set_class f3_2reu5lem3 a_sup_set_class a_wceq f2_2reu5lem3 a_sup_set_class f4_2reu5lem3 a_sup_set_class a_wceq a_wa a_wi f2_2reu5lem3 a_wal f1_2reu5lem3 a_wal f1_2reu5lem3 a_sup_set_class f5_2reu5lem3 a_wcel f0_2reu5lem3 f1_2reu5lem3 a_sup_set_class f3_2reu5lem3 a_sup_set_class a_wceq f2_2reu5lem3 a_sup_set_class f4_2reu5lem3 a_sup_set_class a_wceq a_wa a_wi f2_2reu5lem3 f6_2reu5lem3 a_wral a_wi f1_2reu5lem3 a_wal f0_2reu5lem3 f1_2reu5lem3 a_sup_set_class f3_2reu5lem3 a_sup_set_class a_wceq f2_2reu5lem3 a_sup_set_class f4_2reu5lem3 a_sup_set_class a_wceq a_wa a_wi f2_2reu5lem3 f6_2reu5lem3 a_wral f1_2reu5lem3 f5_2reu5lem3 a_wral p_bitr4i f1_2reu5lem3 a_sup_set_class f5_2reu5lem3 a_wcel f2_2reu5lem3 a_sup_set_class f6_2reu5lem3 a_wcel f0_2reu5lem3 a_w3a f1_2reu5lem3 a_sup_set_class f3_2reu5lem3 a_sup_set_class a_wceq f2_2reu5lem3 a_sup_set_class f4_2reu5lem3 a_sup_set_class a_wceq a_wa a_wi f2_2reu5lem3 a_wal f1_2reu5lem3 a_wal f0_2reu5lem3 f1_2reu5lem3 a_sup_set_class f3_2reu5lem3 a_sup_set_class a_wceq f2_2reu5lem3 a_sup_set_class f4_2reu5lem3 a_sup_set_class a_wceq a_wa a_wi f2_2reu5lem3 f6_2reu5lem3 a_wral f1_2reu5lem3 f5_2reu5lem3 a_wral f4_2reu5lem3 p_exbii f1_2reu5lem3 a_sup_set_class f5_2reu5lem3 a_wcel f2_2reu5lem3 a_sup_set_class f6_2reu5lem3 a_wcel f0_2reu5lem3 a_w3a f1_2reu5lem3 a_sup_set_class f3_2reu5lem3 a_sup_set_class a_wceq f2_2reu5lem3 a_sup_set_class f4_2reu5lem3 a_sup_set_class a_wceq a_wa a_wi f2_2reu5lem3 a_wal f1_2reu5lem3 a_wal f4_2reu5lem3 a_wex f0_2reu5lem3 f1_2reu5lem3 a_sup_set_class f3_2reu5lem3 a_sup_set_class a_wceq f2_2reu5lem3 a_sup_set_class f4_2reu5lem3 a_sup_set_class a_wceq a_wa a_wi f2_2reu5lem3 f6_2reu5lem3 a_wral f1_2reu5lem3 f5_2reu5lem3 a_wral f4_2reu5lem3 a_wex f3_2reu5lem3 p_exbii f1_2reu5lem3 a_sup_set_class f5_2reu5lem3 a_wcel f2_2reu5lem3 a_sup_set_class f6_2reu5lem3 a_wcel f0_2reu5lem3 a_w3a f2_2reu5lem3 a_wex f1_2reu5lem3 a_wex f0_2reu5lem3 f2_2reu5lem3 f6_2reu5lem3 a_wrex f1_2reu5lem3 f5_2reu5lem3 a_wrex f1_2reu5lem3 a_sup_set_class f5_2reu5lem3 a_wcel f2_2reu5lem3 a_sup_set_class f6_2reu5lem3 a_wcel f0_2reu5lem3 a_w3a f1_2reu5lem3 a_sup_set_class f3_2reu5lem3 a_sup_set_class a_wceq f2_2reu5lem3 a_sup_set_class f4_2reu5lem3 a_sup_set_class a_wceq a_wa a_wi f2_2reu5lem3 a_wal f1_2reu5lem3 a_wal f4_2reu5lem3 a_wex f3_2reu5lem3 a_wex f0_2reu5lem3 f1_2reu5lem3 a_sup_set_class f3_2reu5lem3 a_sup_set_class a_wceq f2_2reu5lem3 a_sup_set_class f4_2reu5lem3 a_sup_set_class a_wceq a_wa a_wi f2_2reu5lem3 f6_2reu5lem3 a_wral f1_2reu5lem3 f5_2reu5lem3 a_wral f4_2reu5lem3 a_wex f3_2reu5lem3 a_wex p_anbi12i f0_2reu5lem3 f2_2reu5lem3 f6_2reu5lem3 a_wreu f1_2reu5lem3 f5_2reu5lem3 a_wreu f0_2reu5lem3 f2_2reu5lem3 f6_2reu5lem3 a_wrmo f1_2reu5lem3 f5_2reu5lem3 a_wral a_wa f1_2reu5lem3 a_sup_set_class f5_2reu5lem3 a_wcel f2_2reu5lem3 a_sup_set_class f6_2reu5lem3 a_wcel f0_2reu5lem3 a_w3a f2_2reu5lem3 a_weu f1_2reu5lem3 a_weu f1_2reu5lem3 a_sup_set_class f5_2reu5lem3 a_wcel f2_2reu5lem3 a_sup_set_class f6_2reu5lem3 a_wcel f0_2reu5lem3 a_w3a f2_2reu5lem3 a_wmo f1_2reu5lem3 a_wal a_wa f1_2reu5lem3 a_sup_set_class f5_2reu5lem3 a_wcel f2_2reu5lem3 a_sup_set_class f6_2reu5lem3 a_wcel f0_2reu5lem3 a_w3a f2_2reu5lem3 a_wex f1_2reu5lem3 a_wex f1_2reu5lem3 a_sup_set_class f5_2reu5lem3 a_wcel f2_2reu5lem3 a_sup_set_class f6_2reu5lem3 a_wcel f0_2reu5lem3 a_w3a f1_2reu5lem3 a_sup_set_class f3_2reu5lem3 a_sup_set_class a_wceq f2_2reu5lem3 a_sup_set_class f4_2reu5lem3 a_sup_set_class a_wceq a_wa a_wi f2_2reu5lem3 a_wal f1_2reu5lem3 a_wal f4_2reu5lem3 a_wex f3_2reu5lem3 a_wex a_wa f0_2reu5lem3 f2_2reu5lem3 f6_2reu5lem3 a_wrex f1_2reu5lem3 f5_2reu5lem3 a_wrex f0_2reu5lem3 f1_2reu5lem3 a_sup_set_class f3_2reu5lem3 a_sup_set_class a_wceq f2_2reu5lem3 a_sup_set_class f4_2reu5lem3 a_sup_set_class a_wceq a_wa a_wi f2_2reu5lem3 f6_2reu5lem3 a_wral f1_2reu5lem3 f5_2reu5lem3 a_wral f4_2reu5lem3 a_wex f3_2reu5lem3 a_wex a_wa p_3bitri $.
$}

$(Double restricted existential uniqueness in terms of restricted
       existential quantification and restricted universal quantification,
       analogous to ~ 2eu5 and ~ reu3 .  (Contributed by Alexander van der
       Vekens, 17-Jun-2017.) $)

${
	$v ph x y z w A B  $.
	$d w y z A  $.
	$d w x z B  $.
	$d x y  $.
	$d ph w  $.
	$d ph z  $.
	$d x A  $.
	$d y B  $.
	f0_2reu5 $f wff ph $.
	f1_2reu5 $f set x $.
	f2_2reu5 $f set y $.
	f3_2reu5 $f set z $.
	f4_2reu5 $f set w $.
	f5_2reu5 $f class A $.
	f6_2reu5 $f class B $.
	p_2reu5 $p |- ( ( E! x e. A E! y e. B ph /\ A. x e. A E* y e. B ph ) <-> ( E. x e. A E. y e. B ph /\ E. z e. A E. w e. B A. x e. A A. y e. B ( ph -> ( x = z /\ y = w ) ) ) ) $= f0_2reu5 f2_2reu5 f6_2reu5 a_wrex f0_2reu5 f1_2reu5 a_sup_set_class f3_2reu5 a_sup_set_class a_wceq f2_2reu5 a_sup_set_class f4_2reu5 a_sup_set_class a_wceq a_wa a_wi f2_2reu5 f6_2reu5 a_wral f1_2reu5 f5_2reu5 p_r19.29r f0_2reu5 f0_2reu5 f1_2reu5 a_sup_set_class f3_2reu5 a_sup_set_class a_wceq f2_2reu5 a_sup_set_class f4_2reu5 a_sup_set_class a_wceq a_wa a_wi f2_2reu5 f6_2reu5 p_r19.29r f0_2reu5 f2_2reu5 f6_2reu5 a_wrex f0_2reu5 f1_2reu5 a_sup_set_class f3_2reu5 a_sup_set_class a_wceq f2_2reu5 a_sup_set_class f4_2reu5 a_sup_set_class a_wceq a_wa a_wi f2_2reu5 f6_2reu5 a_wral a_wa f0_2reu5 f0_2reu5 f1_2reu5 a_sup_set_class f3_2reu5 a_sup_set_class a_wceq f2_2reu5 a_sup_set_class f4_2reu5 a_sup_set_class a_wceq a_wa a_wi a_wa f2_2reu5 f6_2reu5 a_wrex f1_2reu5 f5_2reu5 p_reximi f0_2reu5 f1_2reu5 a_sup_set_class f3_2reu5 a_sup_set_class a_wceq f2_2reu5 a_sup_set_class f4_2reu5 a_sup_set_class a_wceq a_wa p_pm3.35 f0_2reu5 f0_2reu5 f1_2reu5 a_sup_set_class f3_2reu5 a_sup_set_class a_wceq f2_2reu5 a_sup_set_class f4_2reu5 a_sup_set_class a_wceq a_wa a_wi a_wa f1_2reu5 a_sup_set_class f3_2reu5 a_sup_set_class a_wceq f2_2reu5 a_sup_set_class f4_2reu5 a_sup_set_class a_wceq a_wa f2_2reu5 f6_2reu5 p_reximi f0_2reu5 f0_2reu5 f1_2reu5 a_sup_set_class f3_2reu5 a_sup_set_class a_wceq f2_2reu5 a_sup_set_class f4_2reu5 a_sup_set_class a_wceq a_wa a_wi a_wa f2_2reu5 f6_2reu5 a_wrex f1_2reu5 a_sup_set_class f3_2reu5 a_sup_set_class a_wceq f2_2reu5 a_sup_set_class f4_2reu5 a_sup_set_class a_wceq a_wa f2_2reu5 f6_2reu5 a_wrex f1_2reu5 f5_2reu5 p_reximi f1_2reu5 a_sup_set_class f3_2reu5 a_sup_set_class f5_2reu5 p_eleq1 f2_2reu5 a_sup_set_class f4_2reu5 a_sup_set_class f6_2reu5 p_eleq1 f1_2reu5 a_sup_set_class f3_2reu5 a_sup_set_class a_wceq f1_2reu5 a_sup_set_class f5_2reu5 a_wcel f3_2reu5 a_sup_set_class f5_2reu5 a_wcel f2_2reu5 a_sup_set_class f4_2reu5 a_sup_set_class a_wceq f2_2reu5 a_sup_set_class f6_2reu5 a_wcel f4_2reu5 a_sup_set_class f6_2reu5 a_wcel p_bi2anan9 f1_2reu5 a_sup_set_class f3_2reu5 a_sup_set_class a_wceq f2_2reu5 a_sup_set_class f4_2reu5 a_sup_set_class a_wceq a_wa f1_2reu5 a_sup_set_class f5_2reu5 a_wcel f2_2reu5 a_sup_set_class f6_2reu5 a_wcel a_wa f3_2reu5 a_sup_set_class f5_2reu5 a_wcel f4_2reu5 a_sup_set_class f6_2reu5 a_wcel a_wa p_biimpac f1_2reu5 a_sup_set_class f5_2reu5 a_wcel f2_2reu5 a_sup_set_class f6_2reu5 a_wcel a_wa f1_2reu5 a_sup_set_class f3_2reu5 a_sup_set_class a_wceq f2_2reu5 a_sup_set_class f4_2reu5 a_sup_set_class a_wceq a_wa a_wa f3_2reu5 a_sup_set_class f5_2reu5 a_wcel f4_2reu5 a_sup_set_class f6_2reu5 a_wcel p_ancomd f1_2reu5 a_sup_set_class f5_2reu5 a_wcel f2_2reu5 a_sup_set_class f6_2reu5 a_wcel a_wa f1_2reu5 a_sup_set_class f3_2reu5 a_sup_set_class a_wceq f2_2reu5 a_sup_set_class f4_2reu5 a_sup_set_class a_wceq a_wa f4_2reu5 a_sup_set_class f6_2reu5 a_wcel f3_2reu5 a_sup_set_class f5_2reu5 a_wcel a_wa p_ex f1_2reu5 a_sup_set_class f3_2reu5 a_sup_set_class a_wceq f2_2reu5 a_sup_set_class f4_2reu5 a_sup_set_class a_wceq a_wa f4_2reu5 a_sup_set_class f6_2reu5 a_wcel f3_2reu5 a_sup_set_class f5_2reu5 a_wcel a_wa f1_2reu5 f2_2reu5 f5_2reu5 f6_2reu5 p_rexlimivv f0_2reu5 f0_2reu5 f1_2reu5 a_sup_set_class f3_2reu5 a_sup_set_class a_wceq f2_2reu5 a_sup_set_class f4_2reu5 a_sup_set_class a_wceq a_wa a_wi a_wa f2_2reu5 f6_2reu5 a_wrex f1_2reu5 f5_2reu5 a_wrex f1_2reu5 a_sup_set_class f3_2reu5 a_sup_set_class a_wceq f2_2reu5 a_sup_set_class f4_2reu5 a_sup_set_class a_wceq a_wa f2_2reu5 f6_2reu5 a_wrex f1_2reu5 f5_2reu5 a_wrex f4_2reu5 a_sup_set_class f6_2reu5 a_wcel f3_2reu5 a_sup_set_class f5_2reu5 a_wcel a_wa p_syl f0_2reu5 f2_2reu5 f6_2reu5 a_wrex f1_2reu5 f5_2reu5 a_wrex f0_2reu5 f1_2reu5 a_sup_set_class f3_2reu5 a_sup_set_class a_wceq f2_2reu5 a_sup_set_class f4_2reu5 a_sup_set_class a_wceq a_wa a_wi f2_2reu5 f6_2reu5 a_wral f1_2reu5 f5_2reu5 a_wral a_wa f0_2reu5 f2_2reu5 f6_2reu5 a_wrex f0_2reu5 f1_2reu5 a_sup_set_class f3_2reu5 a_sup_set_class a_wceq f2_2reu5 a_sup_set_class f4_2reu5 a_sup_set_class a_wceq a_wa a_wi f2_2reu5 f6_2reu5 a_wral a_wa f1_2reu5 f5_2reu5 a_wrex f0_2reu5 f0_2reu5 f1_2reu5 a_sup_set_class f3_2reu5 a_sup_set_class a_wceq f2_2reu5 a_sup_set_class f4_2reu5 a_sup_set_class a_wceq a_wa a_wi a_wa f2_2reu5 f6_2reu5 a_wrex f1_2reu5 f5_2reu5 a_wrex f4_2reu5 a_sup_set_class f6_2reu5 a_wcel f3_2reu5 a_sup_set_class f5_2reu5 a_wcel a_wa p_3syl f0_2reu5 f2_2reu5 f6_2reu5 a_wrex f1_2reu5 f5_2reu5 a_wrex f0_2reu5 f1_2reu5 a_sup_set_class f3_2reu5 a_sup_set_class a_wceq f2_2reu5 a_sup_set_class f4_2reu5 a_sup_set_class a_wceq a_wa a_wi f2_2reu5 f6_2reu5 a_wral f1_2reu5 f5_2reu5 a_wral f4_2reu5 a_sup_set_class f6_2reu5 a_wcel f3_2reu5 a_sup_set_class f5_2reu5 a_wcel a_wa p_ex f0_2reu5 f2_2reu5 f6_2reu5 a_wrex f1_2reu5 f5_2reu5 a_wrex f0_2reu5 f1_2reu5 a_sup_set_class f3_2reu5 a_sup_set_class a_wceq f2_2reu5 a_sup_set_class f4_2reu5 a_sup_set_class a_wceq a_wa a_wi f2_2reu5 f6_2reu5 a_wral f1_2reu5 f5_2reu5 a_wral f4_2reu5 a_sup_set_class f6_2reu5 a_wcel f3_2reu5 a_sup_set_class f5_2reu5 a_wcel a_wa p_pm4.71rd f4_2reu5 a_sup_set_class f6_2reu5 a_wcel f3_2reu5 a_sup_set_class f5_2reu5 a_wcel f0_2reu5 f1_2reu5 a_sup_set_class f3_2reu5 a_sup_set_class a_wceq f2_2reu5 a_sup_set_class f4_2reu5 a_sup_set_class a_wceq a_wa a_wi f2_2reu5 f6_2reu5 a_wral f1_2reu5 f5_2reu5 a_wral p_anass f0_2reu5 f2_2reu5 f6_2reu5 a_wrex f1_2reu5 f5_2reu5 a_wrex f0_2reu5 f1_2reu5 a_sup_set_class f3_2reu5 a_sup_set_class a_wceq f2_2reu5 a_sup_set_class f4_2reu5 a_sup_set_class a_wceq a_wa a_wi f2_2reu5 f6_2reu5 a_wral f1_2reu5 f5_2reu5 a_wral f4_2reu5 a_sup_set_class f6_2reu5 a_wcel f3_2reu5 a_sup_set_class f5_2reu5 a_wcel a_wa f0_2reu5 f1_2reu5 a_sup_set_class f3_2reu5 a_sup_set_class a_wceq f2_2reu5 a_sup_set_class f4_2reu5 a_sup_set_class a_wceq a_wa a_wi f2_2reu5 f6_2reu5 a_wral f1_2reu5 f5_2reu5 a_wral a_wa f4_2reu5 a_sup_set_class f6_2reu5 a_wcel f3_2reu5 a_sup_set_class f5_2reu5 a_wcel f0_2reu5 f1_2reu5 a_sup_set_class f3_2reu5 a_sup_set_class a_wceq f2_2reu5 a_sup_set_class f4_2reu5 a_sup_set_class a_wceq a_wa a_wi f2_2reu5 f6_2reu5 a_wral f1_2reu5 f5_2reu5 a_wral a_wa a_wa p_syl6bb f0_2reu5 f2_2reu5 f6_2reu5 a_wrex f1_2reu5 f5_2reu5 a_wrex f0_2reu5 f1_2reu5 a_sup_set_class f3_2reu5 a_sup_set_class a_wceq f2_2reu5 a_sup_set_class f4_2reu5 a_sup_set_class a_wceq a_wa a_wi f2_2reu5 f6_2reu5 a_wral f1_2reu5 f5_2reu5 a_wral f4_2reu5 a_sup_set_class f6_2reu5 a_wcel f3_2reu5 a_sup_set_class f5_2reu5 a_wcel f0_2reu5 f1_2reu5 a_sup_set_class f3_2reu5 a_sup_set_class a_wceq f2_2reu5 a_sup_set_class f4_2reu5 a_sup_set_class a_wceq a_wa a_wi f2_2reu5 f6_2reu5 a_wral f1_2reu5 f5_2reu5 a_wral a_wa a_wa f3_2reu5 f4_2reu5 p_2exbidv f0_2reu5 f2_2reu5 f6_2reu5 a_wrex f1_2reu5 f5_2reu5 a_wrex f0_2reu5 f1_2reu5 a_sup_set_class f3_2reu5 a_sup_set_class a_wceq f2_2reu5 a_sup_set_class f4_2reu5 a_sup_set_class a_wceq a_wa a_wi f2_2reu5 f6_2reu5 a_wral f1_2reu5 f5_2reu5 a_wral f4_2reu5 a_wex f3_2reu5 a_wex f4_2reu5 a_sup_set_class f6_2reu5 a_wcel f3_2reu5 a_sup_set_class f5_2reu5 a_wcel f0_2reu5 f1_2reu5 a_sup_set_class f3_2reu5 a_sup_set_class a_wceq f2_2reu5 a_sup_set_class f4_2reu5 a_sup_set_class a_wceq a_wa a_wi f2_2reu5 f6_2reu5 a_wral f1_2reu5 f5_2reu5 a_wral a_wa a_wa f4_2reu5 a_wex f3_2reu5 a_wex p_pm5.32i f0_2reu5 f1_2reu5 f2_2reu5 f3_2reu5 f4_2reu5 f5_2reu5 f6_2reu5 p_2reu5lem3 f0_2reu5 f1_2reu5 a_sup_set_class f3_2reu5 a_sup_set_class a_wceq f2_2reu5 a_sup_set_class f4_2reu5 a_sup_set_class a_wceq a_wa a_wi f2_2reu5 f6_2reu5 a_wral f1_2reu5 f5_2reu5 a_wral f4_2reu5 f6_2reu5 a_wrex f3_2reu5 f5_2reu5 a_df-rex f3_2reu5 a_sup_set_class f5_2reu5 a_wcel f0_2reu5 f1_2reu5 a_sup_set_class f3_2reu5 a_sup_set_class a_wceq f2_2reu5 a_sup_set_class f4_2reu5 a_sup_set_class a_wceq a_wa a_wi f2_2reu5 f6_2reu5 a_wral f1_2reu5 f5_2reu5 a_wral f4_2reu5 f6_2reu5 p_r19.42v f3_2reu5 a_sup_set_class f5_2reu5 a_wcel f0_2reu5 f1_2reu5 a_sup_set_class f3_2reu5 a_sup_set_class a_wceq f2_2reu5 a_sup_set_class f4_2reu5 a_sup_set_class a_wceq a_wa a_wi f2_2reu5 f6_2reu5 a_wral f1_2reu5 f5_2reu5 a_wral a_wa f4_2reu5 f6_2reu5 a_df-rex f3_2reu5 a_sup_set_class f5_2reu5 a_wcel f0_2reu5 f1_2reu5 a_sup_set_class f3_2reu5 a_sup_set_class a_wceq f2_2reu5 a_sup_set_class f4_2reu5 a_sup_set_class a_wceq a_wa a_wi f2_2reu5 f6_2reu5 a_wral f1_2reu5 f5_2reu5 a_wral f4_2reu5 f6_2reu5 a_wrex a_wa f3_2reu5 a_sup_set_class f5_2reu5 a_wcel f0_2reu5 f1_2reu5 a_sup_set_class f3_2reu5 a_sup_set_class a_wceq f2_2reu5 a_sup_set_class f4_2reu5 a_sup_set_class a_wceq a_wa a_wi f2_2reu5 f6_2reu5 a_wral f1_2reu5 f5_2reu5 a_wral a_wa f4_2reu5 f6_2reu5 a_wrex f4_2reu5 a_sup_set_class f6_2reu5 a_wcel f3_2reu5 a_sup_set_class f5_2reu5 a_wcel f0_2reu5 f1_2reu5 a_sup_set_class f3_2reu5 a_sup_set_class a_wceq f2_2reu5 a_sup_set_class f4_2reu5 a_sup_set_class a_wceq a_wa a_wi f2_2reu5 f6_2reu5 a_wral f1_2reu5 f5_2reu5 a_wral a_wa a_wa f4_2reu5 a_wex p_bitr3i f3_2reu5 a_sup_set_class f5_2reu5 a_wcel f0_2reu5 f1_2reu5 a_sup_set_class f3_2reu5 a_sup_set_class a_wceq f2_2reu5 a_sup_set_class f4_2reu5 a_sup_set_class a_wceq a_wa a_wi f2_2reu5 f6_2reu5 a_wral f1_2reu5 f5_2reu5 a_wral f4_2reu5 f6_2reu5 a_wrex a_wa f4_2reu5 a_sup_set_class f6_2reu5 a_wcel f3_2reu5 a_sup_set_class f5_2reu5 a_wcel f0_2reu5 f1_2reu5 a_sup_set_class f3_2reu5 a_sup_set_class a_wceq f2_2reu5 a_sup_set_class f4_2reu5 a_sup_set_class a_wceq a_wa a_wi f2_2reu5 f6_2reu5 a_wral f1_2reu5 f5_2reu5 a_wral a_wa a_wa f4_2reu5 a_wex f3_2reu5 p_exbii f0_2reu5 f1_2reu5 a_sup_set_class f3_2reu5 a_sup_set_class a_wceq f2_2reu5 a_sup_set_class f4_2reu5 a_sup_set_class a_wceq a_wa a_wi f2_2reu5 f6_2reu5 a_wral f1_2reu5 f5_2reu5 a_wral f4_2reu5 f6_2reu5 a_wrex f3_2reu5 f5_2reu5 a_wrex f3_2reu5 a_sup_set_class f5_2reu5 a_wcel f0_2reu5 f1_2reu5 a_sup_set_class f3_2reu5 a_sup_set_class a_wceq f2_2reu5 a_sup_set_class f4_2reu5 a_sup_set_class a_wceq a_wa a_wi f2_2reu5 f6_2reu5 a_wral f1_2reu5 f5_2reu5 a_wral f4_2reu5 f6_2reu5 a_wrex a_wa f3_2reu5 a_wex f4_2reu5 a_sup_set_class f6_2reu5 a_wcel f3_2reu5 a_sup_set_class f5_2reu5 a_wcel f0_2reu5 f1_2reu5 a_sup_set_class f3_2reu5 a_sup_set_class a_wceq f2_2reu5 a_sup_set_class f4_2reu5 a_sup_set_class a_wceq a_wa a_wi f2_2reu5 f6_2reu5 a_wral f1_2reu5 f5_2reu5 a_wral a_wa a_wa f4_2reu5 a_wex f3_2reu5 a_wex p_bitri f0_2reu5 f1_2reu5 a_sup_set_class f3_2reu5 a_sup_set_class a_wceq f2_2reu5 a_sup_set_class f4_2reu5 a_sup_set_class a_wceq a_wa a_wi f2_2reu5 f6_2reu5 a_wral f1_2reu5 f5_2reu5 a_wral f4_2reu5 f6_2reu5 a_wrex f3_2reu5 f5_2reu5 a_wrex f4_2reu5 a_sup_set_class f6_2reu5 a_wcel f3_2reu5 a_sup_set_class f5_2reu5 a_wcel f0_2reu5 f1_2reu5 a_sup_set_class f3_2reu5 a_sup_set_class a_wceq f2_2reu5 a_sup_set_class f4_2reu5 a_sup_set_class a_wceq a_wa a_wi f2_2reu5 f6_2reu5 a_wral f1_2reu5 f5_2reu5 a_wral a_wa a_wa f4_2reu5 a_wex f3_2reu5 a_wex f0_2reu5 f2_2reu5 f6_2reu5 a_wrex f1_2reu5 f5_2reu5 a_wrex p_anbi2i f0_2reu5 f2_2reu5 f6_2reu5 a_wrex f1_2reu5 f5_2reu5 a_wrex f0_2reu5 f1_2reu5 a_sup_set_class f3_2reu5 a_sup_set_class a_wceq f2_2reu5 a_sup_set_class f4_2reu5 a_sup_set_class a_wceq a_wa a_wi f2_2reu5 f6_2reu5 a_wral f1_2reu5 f5_2reu5 a_wral f4_2reu5 a_wex f3_2reu5 a_wex a_wa f0_2reu5 f2_2reu5 f6_2reu5 a_wrex f1_2reu5 f5_2reu5 a_wrex f4_2reu5 a_sup_set_class f6_2reu5 a_wcel f3_2reu5 a_sup_set_class f5_2reu5 a_wcel f0_2reu5 f1_2reu5 a_sup_set_class f3_2reu5 a_sup_set_class a_wceq f2_2reu5 a_sup_set_class f4_2reu5 a_sup_set_class a_wceq a_wa a_wi f2_2reu5 f6_2reu5 a_wral f1_2reu5 f5_2reu5 a_wral a_wa a_wa f4_2reu5 a_wex f3_2reu5 a_wex a_wa f0_2reu5 f2_2reu5 f6_2reu5 a_wreu f1_2reu5 f5_2reu5 a_wreu f0_2reu5 f2_2reu5 f6_2reu5 a_wrmo f1_2reu5 f5_2reu5 a_wral a_wa f0_2reu5 f2_2reu5 f6_2reu5 a_wrex f1_2reu5 f5_2reu5 a_wrex f0_2reu5 f1_2reu5 a_sup_set_class f3_2reu5 a_sup_set_class a_wceq f2_2reu5 a_sup_set_class f4_2reu5 a_sup_set_class a_wceq a_wa a_wi f2_2reu5 f6_2reu5 a_wral f1_2reu5 f5_2reu5 a_wral f4_2reu5 f6_2reu5 a_wrex f3_2reu5 f5_2reu5 a_wrex a_wa p_3bitr4i $.
$}


