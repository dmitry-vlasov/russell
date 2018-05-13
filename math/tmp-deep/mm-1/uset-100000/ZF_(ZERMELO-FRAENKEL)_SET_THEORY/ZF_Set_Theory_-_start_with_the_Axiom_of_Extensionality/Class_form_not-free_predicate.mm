$[ turnstile_special_source.mm $]

$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/Class_abstractions_(a_k_a__class_builders).mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Class form not-free predicate

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$c F/_ $.

$(Underlined not-free symbol. $)

$(Extend wff definition to include the not-free predicate for classes. $)

${
	$v x A  $.
	f0_wnfc $f set x $.
	f1_wnfc $f class A $.
	a_wnfc $a wff F/_ x A $.
$}

$(Justification theorem for ~ df-nfc .  (Contributed by Mario Carneiro,
       13-Oct-2016.) $)

${
	$v x y z A  $.
	$d x y z  $.
	$d y z A  $.
	f0_nfcjust $f set x $.
	f1_nfcjust $f set y $.
	f2_nfcjust $f set z $.
	f3_nfcjust $f class A $.
	p_nfcjust $p |- ( A. y F/ x y e. A <-> A. z F/ x z e. A ) $= f1_nfcjust a_sup_set_class f2_nfcjust a_sup_set_class a_wceq f0_nfcjust p_nfv f1_nfcjust a_sup_set_class f2_nfcjust a_sup_set_class f3_nfcjust p_eleq1 f1_nfcjust a_sup_set_class f2_nfcjust a_sup_set_class a_wceq f1_nfcjust a_sup_set_class f3_nfcjust a_wcel f2_nfcjust a_sup_set_class f3_nfcjust a_wcel f0_nfcjust p_nfbidf f1_nfcjust a_sup_set_class f3_nfcjust a_wcel f0_nfcjust a_wnf f2_nfcjust a_sup_set_class f3_nfcjust a_wcel f0_nfcjust a_wnf f1_nfcjust f2_nfcjust p_cbvalv $.
$}

$(Define the not-free predicate for classes.  This is read " ` x ` is not
       free in ` A ` ".  Not-free means that the value of ` x ` cannot affect
       the value of ` A ` , e.g., any occurrence of ` x ` in ` A ` is
       effectively bound by a "for all" or something that expands to one (such
       as "there exists").  It is defined in terms of the not-free predicate
       ~ df-nf for wffs; see that definition for more information.
       (Contributed by Mario Carneiro, 11-Aug-2016.) $)

${
	$v x y A  $.
	$d x y  $.
	$d y A  $.
	f0_df-nfc $f set x $.
	f1_df-nfc $f set y $.
	f2_df-nfc $f class A $.
	a_df-nfc $a |- ( F/_ x A <-> A. y F/ x y e. A ) $.
$}

$(Deduce that a class ` A ` does not have ` x ` free in it.
         (Contributed by Mario Carneiro, 11-Aug-2016.) $)

${
	$v x y A  $.
	$d x y  $.
	$d y A  $.
	f0_nfci $f set x $.
	f1_nfci $f set y $.
	f2_nfci $f class A $.
	e0_nfci $e |- F/ x y e. A $.
	p_nfci $p |- F/_ x A $= f0_nfci f1_nfci f2_nfci a_df-nfc e0_nfci f0_nfci f2_nfci a_wnfc f1_nfci a_sup_set_class f2_nfci a_wcel f0_nfci a_wnf f1_nfci p_mpgbir $.
$}

$(Deduce that a class ` A ` does not have ` x ` free in it.
         (Contributed by Mario Carneiro, 11-Aug-2016.) $)

${
	$v x y A  $.
	$d x y  $.
	$d y A  $.
	f0_nfcii $f set x $.
	f1_nfcii $f set y $.
	f2_nfcii $f class A $.
	e0_nfcii $e |- ( y e. A -> A. x y e. A ) $.
	p_nfcii $p |- F/_ x A $= e0_nfcii f1_nfcii a_sup_set_class f2_nfcii a_wcel f0_nfcii p_nfi f0_nfcii f1_nfcii f2_nfcii p_nfci $.
$}

$(Consequence of the not-free predicate.  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)

${
	$v x y A  $.
	$d x y  $.
	$d y A  $.
	f0_nfcr $f set x $.
	f1_nfcr $f set y $.
	f2_nfcr $f class A $.
	p_nfcr $p |- ( F/_ x A -> F/ x y e. A ) $= f0_nfcr f1_nfcr f2_nfcr a_df-nfc f1_nfcr a_sup_set_class f2_nfcr a_wcel f0_nfcr a_wnf f1_nfcr p_sp f0_nfcr f2_nfcr a_wnfc f1_nfcr a_sup_set_class f2_nfcr a_wcel f0_nfcr a_wnf f1_nfcr a_wal f1_nfcr a_sup_set_class f2_nfcr a_wcel f0_nfcr a_wnf p_sylbi $.
$}

$(Consequence of the not-free predicate.  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)

${
	$v x y A  $.
	$d x y z  $.
	$d z A  $.
	f0_nfcrii $f set x $.
	f1_nfcrii $f set y $.
	f2_nfcrii $f class A $.
	i0_nfcrii $f set z $.
	e0_nfcrii $e |- F/_ x A $.
	p_nfcrii $p |- ( y e. A -> A. x y e. A ) $= e0_nfcrii f0_nfcrii i0_nfcrii f2_nfcrii p_nfcr f0_nfcrii f2_nfcrii a_wnfc i0_nfcrii a_sup_set_class f2_nfcrii a_wcel f0_nfcrii a_wnf a_ax-mp i0_nfcrii a_sup_set_class f2_nfcrii a_wcel f0_nfcrii p_nfri f0_nfcrii i0_nfcrii f1_nfcrii f2_nfcrii p_hblem $.
$}

$(Consequence of the not-free predicate.  (Note that unlike ~ nfcr , this
       does not require ` y ` and ` A ` to be disjoint.)  (Contributed by Mario
       Carneiro, 11-Aug-2016.) $)

${
	$v x y A  $.
	$d x y  $.
	$d A  $.
	f0_nfcri $f set x $.
	f1_nfcri $f set y $.
	f2_nfcri $f class A $.
	e0_nfcri $e |- F/_ x A $.
	p_nfcri $p |- F/ x y e. A $= e0_nfcri f0_nfcri f1_nfcri f2_nfcri p_nfcrii f1_nfcri a_sup_set_class f2_nfcri a_wcel f0_nfcri p_nfi $.
$}

$(Deduce that a class ` A ` does not have ` x ` free in it.  (Contributed
       by Mario Carneiro, 11-Aug-2016.) $)

${
	$v ph x y A  $.
	$d x y  $.
	$d y A  $.
	f0_nfcd $f wff ph $.
	f1_nfcd $f set x $.
	f2_nfcd $f set y $.
	f3_nfcd $f class A $.
	e0_nfcd $e |- F/ y ph $.
	e1_nfcd $e |- ( ph -> F/ x y e. A ) $.
	p_nfcd $p |- ( ph -> F/_ x A ) $= e0_nfcd e1_nfcd f0_nfcd f2_nfcd a_sup_set_class f3_nfcd a_wcel f1_nfcd a_wnf f2_nfcd p_alrimi f1_nfcd f2_nfcd f3_nfcd a_df-nfc f0_nfcd f2_nfcd a_sup_set_class f3_nfcd a_wcel f1_nfcd a_wnf f2_nfcd a_wal f1_nfcd f3_nfcd a_wnfc p_sylibr $.
$}

$(Equality theorem for class not-free.  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)

${
	$v x A B  $.
	$d x y  $.
	$d y A  $.
	$d y B  $.
	f0_nfceqi $f set x $.
	f1_nfceqi $f class A $.
	f2_nfceqi $f class B $.
	i0_nfceqi $f set y $.
	e0_nfceqi $e |- A = B $.
	p_nfceqi $p |- ( F/_ x A <-> F/_ x B ) $= e0_nfceqi f1_nfceqi f2_nfceqi i0_nfceqi a_sup_set_class p_eleq2i i0_nfceqi a_sup_set_class f1_nfceqi a_wcel i0_nfceqi a_sup_set_class f2_nfceqi a_wcel f0_nfceqi p_nfbii i0_nfceqi a_sup_set_class f1_nfceqi a_wcel f0_nfceqi a_wnf i0_nfceqi a_sup_set_class f2_nfceqi a_wcel f0_nfceqi a_wnf i0_nfceqi p_albii f0_nfceqi i0_nfceqi f1_nfceqi a_df-nfc f0_nfceqi i0_nfceqi f2_nfceqi a_df-nfc i0_nfceqi a_sup_set_class f1_nfceqi a_wcel f0_nfceqi a_wnf i0_nfceqi a_wal i0_nfceqi a_sup_set_class f2_nfceqi a_wcel f0_nfceqi a_wnf i0_nfceqi a_wal f0_nfceqi f1_nfceqi a_wnfc f0_nfceqi f2_nfceqi a_wnfc p_3bitr4i $.
$}

$(A utility lemma to transfer a bound-variable hypothesis builder into a
         definition.  (Contributed by Mario Carneiro, 11-Aug-2016.) $)

${
	$v x A B  $.
	$d x  $.
	$d A  $.
	$d B  $.
	f0_nfcxfr $f set x $.
	f1_nfcxfr $f class A $.
	f2_nfcxfr $f class B $.
	e0_nfcxfr $e |- A = B $.
	e1_nfcxfr $e |- F/_ x B $.
	p_nfcxfr $p |- F/_ x A $= e1_nfcxfr e0_nfcxfr f0_nfcxfr f1_nfcxfr f2_nfcxfr p_nfceqi f0_nfcxfr f1_nfcxfr a_wnfc f0_nfcxfr f2_nfcxfr a_wnfc p_mpbir $.
$}

$(A utility lemma to transfer a bound-variable hypothesis builder into a
         definition.  (Contributed by Mario Carneiro, 11-Aug-2016.) $)

${
	$v ph x A B  $.
	$d x  $.
	$d A  $.
	$d B  $.
	f0_nfcxfrd $f wff ph $.
	f1_nfcxfrd $f set x $.
	f2_nfcxfrd $f class A $.
	f3_nfcxfrd $f class B $.
	e0_nfcxfrd $e |- A = B $.
	e1_nfcxfrd $e |- ( ph -> F/_ x B ) $.
	p_nfcxfrd $p |- ( ph -> F/_ x A ) $= e1_nfcxfrd e0_nfcxfrd f1_nfcxfrd f2_nfcxfrd f3_nfcxfrd p_nfceqi f0_nfcxfrd f1_nfcxfrd f3_nfcxfrd a_wnfc f1_nfcxfrd f2_nfcxfrd a_wnfc p_sylibr $.
$}

$(An equality theorem for effectively not free.  (Contributed by Mario
       Carneiro, 14-Oct-2016.) $)

${
	$v ph x A B  $.
	$d x y  $.
	$d A y  $.
	$d B y  $.
	$d ph y  $.
	f0_nfceqdf $f wff ph $.
	f1_nfceqdf $f set x $.
	f2_nfceqdf $f class A $.
	f3_nfceqdf $f class B $.
	i0_nfceqdf $f set y $.
	e0_nfceqdf $e |- F/ x ph $.
	e1_nfceqdf $e |- ( ph -> A = B ) $.
	p_nfceqdf $p |- ( ph -> ( F/_ x A <-> F/_ x B ) ) $= e0_nfceqdf e1_nfceqdf f0_nfceqdf f2_nfceqdf f3_nfceqdf i0_nfceqdf a_sup_set_class p_eleq2d f0_nfceqdf i0_nfceqdf a_sup_set_class f2_nfceqdf a_wcel i0_nfceqdf a_sup_set_class f3_nfceqdf a_wcel f1_nfceqdf p_nfbidf f0_nfceqdf i0_nfceqdf a_sup_set_class f2_nfceqdf a_wcel f1_nfceqdf a_wnf i0_nfceqdf a_sup_set_class f3_nfceqdf a_wcel f1_nfceqdf a_wnf i0_nfceqdf p_albidv f1_nfceqdf i0_nfceqdf f2_nfceqdf a_df-nfc f1_nfceqdf i0_nfceqdf f3_nfceqdf a_df-nfc f0_nfceqdf i0_nfceqdf a_sup_set_class f2_nfceqdf a_wcel f1_nfceqdf a_wnf i0_nfceqdf a_wal i0_nfceqdf a_sup_set_class f3_nfceqdf a_wcel f1_nfceqdf a_wnf i0_nfceqdf a_wal f1_nfceqdf f2_nfceqdf a_wnfc f1_nfceqdf f3_nfceqdf a_wnfc p_3bitr4g $.
$}

$(If ` x ` is disjoint from ` A ` , then ` x ` is not free in ` A ` .
       (Contributed by Mario Carneiro, 11-Aug-2016.) $)

${
	$v x A  $.
	$d x y A  $.
	f0_nfcv $f set x $.
	f1_nfcv $f class A $.
	i0_nfcv $f set y $.
	p_nfcv $p |- F/_ x A $= i0_nfcv a_sup_set_class f1_nfcv a_wcel f0_nfcv p_nfv f0_nfcv i0_nfcv f1_nfcv p_nfci $.
$}

$(If ` x ` is disjoint from ` A ` , then ` x ` is not free in ` A ` .
       (Contributed by Mario Carneiro, 7-Oct-2016.) $)

${
	$v ph x A  $.
	$d x A  $.
	f0_nfcvd $f wff ph $.
	f1_nfcvd $f set x $.
	f2_nfcvd $f class A $.
	p_nfcvd $p |- ( ph -> F/_ x A ) $= f1_nfcvd f2_nfcvd p_nfcv f1_nfcvd f2_nfcvd a_wnfc f0_nfcvd p_a1i $.
$}

$(Bound-variable hypothesis builder for a class abstraction.  (Contributed
       by Mario Carneiro, 11-Aug-2016.) $)

${
	$v ph x  $.
	$d x y  $.
	$d y  $.
	$d y ph  $.
	f0_nfab1 $f wff ph $.
	f1_nfab1 $f set x $.
	i0_nfab1 $f set y $.
	p_nfab1 $p |- F/_ x { x | ph } $= f0_nfab1 f1_nfab1 i0_nfab1 p_nfsab1 f1_nfab1 i0_nfab1 f0_nfab1 f1_nfab1 a_cab p_nfci $.
$}

$(` x ` is bound in ` F/_ x A ` .  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)

${
	$v x A  $.
	$d x y  $.
	$d y A  $.
	$d y  $.
	f0_nfnfc1 $f set x $.
	f1_nfnfc1 $f class A $.
	i0_nfnfc1 $f set y $.
	p_nfnfc1 $p |- F/ x F/_ x A $= f0_nfnfc1 i0_nfnfc1 f1_nfnfc1 a_df-nfc i0_nfnfc1 a_sup_set_class f1_nfnfc1 a_wcel f0_nfnfc1 p_nfnf1 i0_nfnfc1 a_sup_set_class f1_nfnfc1 a_wcel f0_nfnfc1 a_wnf f0_nfnfc1 i0_nfnfc1 p_nfal f0_nfnfc1 f1_nfnfc1 a_wnfc i0_nfnfc1 a_sup_set_class f1_nfnfc1 a_wcel f0_nfnfc1 a_wnf i0_nfnfc1 a_wal f0_nfnfc1 p_nfxfr $.
$}

$(Bound-variable hypothesis builder for a class abstraction.  (Contributed
       by Mario Carneiro, 11-Aug-2016.) $)

${
	$v ph x y  $.
	$d x z  $.
	$d y z  $.
	$d z ph  $.
	f0_nfab $f wff ph $.
	f1_nfab $f set x $.
	f2_nfab $f set y $.
	i0_nfab $f set z $.
	e0_nfab $e |- F/ x ph $.
	p_nfab $p |- F/_ x { y | ph } $= e0_nfab f0_nfab f1_nfab f2_nfab i0_nfab p_nfsab f1_nfab i0_nfab f0_nfab f2_nfab a_cab p_nfci $.
$}

$(Bound-variable hypothesis builder for a class abstraction.  (Contributed
       by Mario Carneiro, 14-Oct-2016.) $)

${
	$v ph x y  $.
	f0_nfaba1 $f wff ph $.
	f1_nfaba1 $f set x $.
	f2_nfaba1 $f set y $.
	p_nfaba1 $p |- F/_ x { y | A. x ph } $= f0_nfaba1 f1_nfaba1 p_nfa1 f0_nfaba1 f1_nfaba1 a_wal f1_nfaba1 f2_nfaba1 p_nfab $.
$}

$(Hypothesis builder for ` F/_ y A ` .  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)

${
	$v x y A  $.
	$d x z  $.
	$d y z  $.
	$d z A  $.
	$d z  $.
	f0_nfnfc $f set x $.
	f1_nfnfc $f set y $.
	f2_nfnfc $f class A $.
	i0_nfnfc $f set z $.
	e0_nfnfc $e |- F/_ x A $.
	p_nfnfc $p |- F/ x F/_ y A $= f1_nfnfc i0_nfnfc f2_nfnfc a_df-nfc e0_nfnfc f0_nfnfc i0_nfnfc f2_nfnfc p_nfcri i0_nfnfc a_sup_set_class f2_nfnfc a_wcel f0_nfnfc f1_nfnfc p_nfnf i0_nfnfc a_sup_set_class f2_nfnfc a_wcel f1_nfnfc a_wnf f0_nfnfc i0_nfnfc p_nfal f1_nfnfc f2_nfnfc a_wnfc i0_nfnfc a_sup_set_class f2_nfnfc a_wcel f1_nfnfc a_wnf i0_nfnfc a_wal f0_nfnfc p_nfxfr $.
$}

$(Hypothesis builder for equality.  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)

${
	$v x A B  $.
	$d x z  $.
	$d z  $.
	$d z A  $.
	$d z B  $.
	f0_nfeq $f set x $.
	f1_nfeq $f class A $.
	f2_nfeq $f class B $.
	i0_nfeq $f set z $.
	e0_nfeq $e |- F/_ x A $.
	e1_nfeq $e |- F/_ x B $.
	p_nfeq $p |- F/ x A = B $= i0_nfeq f1_nfeq f2_nfeq p_dfcleq e0_nfeq f0_nfeq i0_nfeq f1_nfeq p_nfcri e1_nfeq f0_nfeq i0_nfeq f2_nfeq p_nfcri i0_nfeq a_sup_set_class f1_nfeq a_wcel i0_nfeq a_sup_set_class f2_nfeq a_wcel f0_nfeq p_nfbi i0_nfeq a_sup_set_class f1_nfeq a_wcel i0_nfeq a_sup_set_class f2_nfeq a_wcel a_wb f0_nfeq i0_nfeq p_nfal f1_nfeq f2_nfeq a_wceq i0_nfeq a_sup_set_class f1_nfeq a_wcel i0_nfeq a_sup_set_class f2_nfeq a_wcel a_wb i0_nfeq a_wal f0_nfeq p_nfxfr $.
$}

$(Hypothesis builder for elementhood.  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)

${
	$v x A B  $.
	$d x z  $.
	$d z  $.
	$d z A  $.
	$d z B  $.
	f0_nfel $f set x $.
	f1_nfel $f class A $.
	f2_nfel $f class B $.
	i0_nfel $f set z $.
	e0_nfel $e |- F/_ x A $.
	e1_nfel $e |- F/_ x B $.
	p_nfel $p |- F/ x A e. B $= i0_nfel f1_nfel f2_nfel a_df-clel f0_nfel i0_nfel a_sup_set_class p_nfcv e0_nfel f0_nfel i0_nfel a_sup_set_class f1_nfel p_nfeq e1_nfel f0_nfel i0_nfel f2_nfel p_nfcri i0_nfel a_sup_set_class f1_nfel a_wceq i0_nfel a_sup_set_class f2_nfel a_wcel f0_nfel p_nfan i0_nfel a_sup_set_class f1_nfel a_wceq i0_nfel a_sup_set_class f2_nfel a_wcel a_wa f0_nfel i0_nfel p_nfex f1_nfel f2_nfel a_wcel i0_nfel a_sup_set_class f1_nfel a_wceq i0_nfel a_sup_set_class f2_nfel a_wcel a_wa i0_nfel a_wex f0_nfel p_nfxfr $.
$}

$(Hypothesis builder for equality, special case.  (Contributed by Mario
       Carneiro, 10-Oct-2016.) $)

${
	$v x A B  $.
	$d x B  $.
	f0_nfeq1 $f set x $.
	f1_nfeq1 $f class A $.
	f2_nfeq1 $f class B $.
	e0_nfeq1 $e |- F/_ x A $.
	p_nfeq1 $p |- F/ x A = B $= e0_nfeq1 f0_nfeq1 f2_nfeq1 p_nfcv f0_nfeq1 f1_nfeq1 f2_nfeq1 p_nfeq $.
$}

$(Hypothesis builder for elementhood, special case.  (Contributed by Mario
       Carneiro, 10-Oct-2016.) $)

${
	$v x A B  $.
	$d x B  $.
	f0_nfel1 $f set x $.
	f1_nfel1 $f class A $.
	f2_nfel1 $f class B $.
	e0_nfel1 $e |- F/_ x A $.
	p_nfel1 $p |- F/ x A e. B $= e0_nfel1 f0_nfel1 f2_nfel1 p_nfcv f0_nfel1 f1_nfel1 f2_nfel1 p_nfel $.
$}

$(Hypothesis builder for equality, special case.  (Contributed by Mario
       Carneiro, 10-Oct-2016.) $)

${
	$v x A B  $.
	$d x A  $.
	f0_nfeq2 $f set x $.
	f1_nfeq2 $f class A $.
	f2_nfeq2 $f class B $.
	e0_nfeq2 $e |- F/_ x B $.
	p_nfeq2 $p |- F/ x A = B $= f0_nfeq2 f1_nfeq2 p_nfcv e0_nfeq2 f0_nfeq2 f1_nfeq2 f2_nfeq2 p_nfeq $.
$}

$(Hypothesis builder for elementhood, special case.  (Contributed by Mario
       Carneiro, 10-Oct-2016.) $)

${
	$v x A B  $.
	$d x A  $.
	f0_nfel2 $f set x $.
	f1_nfel2 $f class A $.
	f2_nfel2 $f class B $.
	e0_nfel2 $e |- F/_ x B $.
	p_nfel2 $p |- F/ x A e. B $= f0_nfel2 f1_nfel2 p_nfcv e0_nfel2 f0_nfel2 f1_nfel2 f2_nfel2 p_nfel $.
$}

$(Consequence of the not-free predicate.  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)

${
	$v ph x y A  $.
	$d x y  $.
	$d y A  $.
	$d y  $.
	f0_nfcrd $f wff ph $.
	f1_nfcrd $f set x $.
	f2_nfcrd $f set y $.
	f3_nfcrd $f class A $.
	e0_nfcrd $e |- ( ph -> F/_ x A ) $.
	p_nfcrd $p |- ( ph -> F/ x y e. A ) $= e0_nfcrd f1_nfcrd f2_nfcrd f3_nfcrd p_nfcr f0_nfcrd f1_nfcrd f3_nfcrd a_wnfc f2_nfcrd a_sup_set_class f3_nfcrd a_wcel f1_nfcrd a_wnf p_syl $.
$}

$(Hypothesis builder for equality.  (Contributed by Mario Carneiro,
       7-Oct-2016.) $)

${
	$v ph x A B  $.
	$d x y  $.
	$d y A  $.
	$d y B  $.
	$d y ph  $.
	f0_nfeqd $f wff ph $.
	f1_nfeqd $f set x $.
	f2_nfeqd $f class A $.
	f3_nfeqd $f class B $.
	i0_nfeqd $f set y $.
	e0_nfeqd $e |- ( ph -> F/_ x A ) $.
	e1_nfeqd $e |- ( ph -> F/_ x B ) $.
	p_nfeqd $p |- ( ph -> F/ x A = B ) $= i0_nfeqd f2_nfeqd f3_nfeqd p_dfcleq f0_nfeqd i0_nfeqd p_nfv e0_nfeqd f0_nfeqd f1_nfeqd i0_nfeqd f2_nfeqd p_nfcrd e1_nfeqd f0_nfeqd f1_nfeqd i0_nfeqd f3_nfeqd p_nfcrd f0_nfeqd i0_nfeqd a_sup_set_class f2_nfeqd a_wcel i0_nfeqd a_sup_set_class f3_nfeqd a_wcel f1_nfeqd p_nfbid f0_nfeqd i0_nfeqd a_sup_set_class f2_nfeqd a_wcel i0_nfeqd a_sup_set_class f3_nfeqd a_wcel a_wb f1_nfeqd i0_nfeqd p_nfald f2_nfeqd f3_nfeqd a_wceq i0_nfeqd a_sup_set_class f2_nfeqd a_wcel i0_nfeqd a_sup_set_class f3_nfeqd a_wcel a_wb i0_nfeqd a_wal f0_nfeqd f1_nfeqd p_nfxfrd $.
$}

$(Hypothesis builder for elementhood.  (Contributed by Mario Carneiro,
       7-Oct-2016.) $)

${
	$v ph x A B  $.
	$d x y  $.
	$d y A  $.
	$d y B  $.
	$d y ph  $.
	f0_nfeld $f wff ph $.
	f1_nfeld $f set x $.
	f2_nfeld $f class A $.
	f3_nfeld $f class B $.
	i0_nfeld $f set y $.
	e0_nfeld $e |- ( ph -> F/_ x A ) $.
	e1_nfeld $e |- ( ph -> F/_ x B ) $.
	p_nfeld $p |- ( ph -> F/ x A e. B ) $= i0_nfeld f2_nfeld f3_nfeld a_df-clel f0_nfeld i0_nfeld p_nfv f0_nfeld f1_nfeld i0_nfeld a_sup_set_class p_nfcvd e0_nfeld f0_nfeld f1_nfeld i0_nfeld a_sup_set_class f2_nfeld p_nfeqd e1_nfeld f0_nfeld f1_nfeld i0_nfeld f3_nfeld p_nfcrd f0_nfeld i0_nfeld a_sup_set_class f2_nfeld a_wceq i0_nfeld a_sup_set_class f3_nfeld a_wcel f1_nfeld p_nfand f0_nfeld i0_nfeld a_sup_set_class f2_nfeld a_wceq i0_nfeld a_sup_set_class f3_nfeld a_wcel a_wa f1_nfeld i0_nfeld p_nfexd f2_nfeld f3_nfeld a_wcel i0_nfeld a_sup_set_class f2_nfeld a_wceq i0_nfeld a_sup_set_class f3_nfeld a_wcel a_wa i0_nfeld a_wex f0_nfeld f1_nfeld p_nfxfrd $.
$}

$(Formula-building lemma for use with the Distinctor Reduction Theorem.
       (Contributed by Mario Carneiro, 8-Oct-2016.) $)

${
	$v x y A B  $.
	$d w x  $.
	$d w y  $.
	$d w  $.
	$d w A  $.
	$d w B  $.
	f0_drnfc1 $f set x $.
	f1_drnfc1 $f set y $.
	f2_drnfc1 $f class A $.
	f3_drnfc1 $f class B $.
	i0_drnfc1 $f set w $.
	e0_drnfc1 $e |- ( A. x x = y -> A = B ) $.
	p_drnfc1 $p |- ( A. x x = y -> ( F/_ x A <-> F/_ y B ) ) $= e0_drnfc1 f0_drnfc1 a_sup_set_class f1_drnfc1 a_sup_set_class a_wceq f0_drnfc1 a_wal f2_drnfc1 f3_drnfc1 i0_drnfc1 a_sup_set_class p_eleq2d i0_drnfc1 a_sup_set_class f2_drnfc1 a_wcel i0_drnfc1 a_sup_set_class f3_drnfc1 a_wcel f0_drnfc1 f1_drnfc1 p_drnf1 i0_drnfc1 a_sup_set_class f2_drnfc1 a_wcel f0_drnfc1 a_wnf i0_drnfc1 a_sup_set_class f3_drnfc1 a_wcel f1_drnfc1 a_wnf f0_drnfc1 f1_drnfc1 i0_drnfc1 p_dral2 f0_drnfc1 i0_drnfc1 f2_drnfc1 a_df-nfc f1_drnfc1 i0_drnfc1 f3_drnfc1 a_df-nfc f0_drnfc1 a_sup_set_class f1_drnfc1 a_sup_set_class a_wceq f0_drnfc1 a_wal i0_drnfc1 a_sup_set_class f2_drnfc1 a_wcel f0_drnfc1 a_wnf i0_drnfc1 a_wal i0_drnfc1 a_sup_set_class f3_drnfc1 a_wcel f1_drnfc1 a_wnf i0_drnfc1 a_wal f0_drnfc1 f2_drnfc1 a_wnfc f1_drnfc1 f3_drnfc1 a_wnfc p_3bitr4g $.
$}

$(Formula-building lemma for use with the Distinctor Reduction Theorem.
       (Contributed by Mario Carneiro, 8-Oct-2016.) $)

${
	$v x y z A B  $.
	$d w x  $.
	$d w y  $.
	$d w z  $.
	$d w A  $.
	$d w B  $.
	f0_drnfc2 $f set x $.
	f1_drnfc2 $f set y $.
	f2_drnfc2 $f set z $.
	f3_drnfc2 $f class A $.
	f4_drnfc2 $f class B $.
	i0_drnfc2 $f set w $.
	e0_drnfc2 $e |- ( A. x x = y -> A = B ) $.
	p_drnfc2 $p |- ( A. x x = y -> ( F/_ z A <-> F/_ z B ) ) $= e0_drnfc2 f0_drnfc2 a_sup_set_class f1_drnfc2 a_sup_set_class a_wceq f0_drnfc2 a_wal f3_drnfc2 f4_drnfc2 i0_drnfc2 a_sup_set_class p_eleq2d i0_drnfc2 a_sup_set_class f3_drnfc2 a_wcel i0_drnfc2 a_sup_set_class f4_drnfc2 a_wcel f0_drnfc2 f1_drnfc2 f2_drnfc2 p_drnf2 i0_drnfc2 a_sup_set_class f3_drnfc2 a_wcel f2_drnfc2 a_wnf i0_drnfc2 a_sup_set_class f4_drnfc2 a_wcel f2_drnfc2 a_wnf f0_drnfc2 f1_drnfc2 i0_drnfc2 p_dral2 f2_drnfc2 i0_drnfc2 f3_drnfc2 a_df-nfc f2_drnfc2 i0_drnfc2 f4_drnfc2 a_df-nfc f0_drnfc2 a_sup_set_class f1_drnfc2 a_sup_set_class a_wceq f0_drnfc2 a_wal i0_drnfc2 a_sup_set_class f3_drnfc2 a_wcel f2_drnfc2 a_wnf i0_drnfc2 a_wal i0_drnfc2 a_sup_set_class f4_drnfc2 a_wcel f2_drnfc2 a_wnf i0_drnfc2 a_wal f2_drnfc2 f3_drnfc2 a_wnfc f2_drnfc2 f4_drnfc2 a_wnfc p_3bitr4g $.
$}

$(Bound-variable hypothesis builder for a class abstraction.  (Contributed
       by Mario Carneiro, 8-Oct-2016.) $)

${
	$v ph ps x y  $.
	$d x z  $.
	$d y z  $.
	$d z ph  $.
	$d z ps  $.
	f0_nfabd2 $f wff ph $.
	f1_nfabd2 $f wff ps $.
	f2_nfabd2 $f set x $.
	f3_nfabd2 $f set y $.
	i0_nfabd2 $f set z $.
	e0_nfabd2 $e |- F/ y ph $.
	e1_nfabd2 $e |- ( ( ph /\ -. A. x x = y ) -> F/ x ps ) $.
	p_nfabd2 $p |- ( ph -> F/_ x { y | ps } ) $= f0_nfabd2 f2_nfabd2 a_sup_set_class f3_nfabd2 a_sup_set_class a_wceq f2_nfabd2 a_wal a_wn a_wa i0_nfabd2 p_nfv f1_nfabd2 i0_nfabd2 f3_nfabd2 a_df-clab e0_nfabd2 f2_nfabd2 f3_nfabd2 f3_nfabd2 p_nfnae f0_nfabd2 f2_nfabd2 a_sup_set_class f3_nfabd2 a_sup_set_class a_wceq f2_nfabd2 a_wal a_wn f3_nfabd2 p_nfan e1_nfabd2 f0_nfabd2 f2_nfabd2 a_sup_set_class f3_nfabd2 a_sup_set_class a_wceq f2_nfabd2 a_wal a_wn a_wa f1_nfabd2 f3_nfabd2 i0_nfabd2 f2_nfabd2 p_nfsbd i0_nfabd2 a_sup_set_class f1_nfabd2 f3_nfabd2 a_cab a_wcel f1_nfabd2 f3_nfabd2 i0_nfabd2 a_wsb f0_nfabd2 f2_nfabd2 a_sup_set_class f3_nfabd2 a_sup_set_class a_wceq f2_nfabd2 a_wal a_wn a_wa f2_nfabd2 p_nfxfrd f0_nfabd2 f2_nfabd2 a_sup_set_class f3_nfabd2 a_sup_set_class a_wceq f2_nfabd2 a_wal a_wn a_wa f2_nfabd2 i0_nfabd2 f1_nfabd2 f3_nfabd2 a_cab p_nfcd f0_nfabd2 f2_nfabd2 a_sup_set_class f3_nfabd2 a_sup_set_class a_wceq f2_nfabd2 a_wal a_wn f2_nfabd2 f1_nfabd2 f3_nfabd2 a_cab a_wnfc p_ex f1_nfabd2 f3_nfabd2 p_nfab1 f2_nfabd2 a_sup_set_class f3_nfabd2 a_sup_set_class a_wceq f2_nfabd2 a_wal f1_nfabd2 f3_nfabd2 a_cab p_eqidd f2_nfabd2 f3_nfabd2 f1_nfabd2 f3_nfabd2 a_cab f1_nfabd2 f3_nfabd2 a_cab p_drnfc1 f2_nfabd2 a_sup_set_class f3_nfabd2 a_sup_set_class a_wceq f2_nfabd2 a_wal f2_nfabd2 f1_nfabd2 f3_nfabd2 a_cab a_wnfc f3_nfabd2 f1_nfabd2 f3_nfabd2 a_cab a_wnfc p_mpbiri f0_nfabd2 f2_nfabd2 a_sup_set_class f3_nfabd2 a_sup_set_class a_wceq f2_nfabd2 a_wal f2_nfabd2 f1_nfabd2 f3_nfabd2 a_cab a_wnfc p_pm2.61d2 $.
$}

$(Bound-variable hypothesis builder for a class abstraction.  (Contributed
       by Mario Carneiro, 8-Oct-2016.) $)

${
	$v ph ps x y  $.
	f0_nfabd $f wff ph $.
	f1_nfabd $f wff ps $.
	f2_nfabd $f set x $.
	f3_nfabd $f set y $.
	e0_nfabd $e |- F/ y ph $.
	e1_nfabd $e |- ( ph -> F/ x ps ) $.
	p_nfabd $p |- ( ph -> F/_ x { y | ps } ) $= e0_nfabd e1_nfabd f0_nfabd f1_nfabd f2_nfabd a_wnf f2_nfabd a_sup_set_class f3_nfabd a_sup_set_class a_wceq f2_nfabd a_wal a_wn p_adantr f0_nfabd f1_nfabd f2_nfabd f3_nfabd p_nfabd2 $.
$}

$(Deduction form of ~ dvelimc .  (Contributed by Mario Carneiro,
       8-Oct-2016.) $)

${
	$v ph x y z A B  $.
	$d w x  $.
	$d w y  $.
	$d w z  $.
	$d w A  $.
	$d w B  $.
	$d w ph  $.
	f0_dvelimdc $f wff ph $.
	f1_dvelimdc $f set x $.
	f2_dvelimdc $f set y $.
	f3_dvelimdc $f set z $.
	f4_dvelimdc $f class A $.
	f5_dvelimdc $f class B $.
	i0_dvelimdc $f set w $.
	e0_dvelimdc $e |- F/ x ph $.
	e1_dvelimdc $e |- F/ z ph $.
	e2_dvelimdc $e |- ( ph -> F/_ x A ) $.
	e3_dvelimdc $e |- ( ph -> F/_ z B ) $.
	e4_dvelimdc $e |- ( ph -> ( z = y -> A = B ) ) $.
	p_dvelimdc $p |- ( ph -> ( -. A. x x = y -> F/_ x B ) ) $= f0_dvelimdc f1_dvelimdc a_sup_set_class f2_dvelimdc a_sup_set_class a_wceq f1_dvelimdc a_wal a_wn a_wa i0_dvelimdc p_nfv e0_dvelimdc e1_dvelimdc e2_dvelimdc f0_dvelimdc f1_dvelimdc i0_dvelimdc f4_dvelimdc p_nfcrd e3_dvelimdc f0_dvelimdc f3_dvelimdc i0_dvelimdc f5_dvelimdc p_nfcrd e4_dvelimdc f4_dvelimdc f5_dvelimdc i0_dvelimdc a_sup_set_class p_eleq2 f0_dvelimdc f3_dvelimdc a_sup_set_class f2_dvelimdc a_sup_set_class a_wceq f4_dvelimdc f5_dvelimdc a_wceq i0_dvelimdc a_sup_set_class f4_dvelimdc a_wcel i0_dvelimdc a_sup_set_class f5_dvelimdc a_wcel a_wb p_syl6 f0_dvelimdc i0_dvelimdc a_sup_set_class f4_dvelimdc a_wcel i0_dvelimdc a_sup_set_class f5_dvelimdc a_wcel f1_dvelimdc f2_dvelimdc f3_dvelimdc p_dvelimdf f0_dvelimdc f1_dvelimdc a_sup_set_class f2_dvelimdc a_sup_set_class a_wceq f1_dvelimdc a_wal a_wn i0_dvelimdc a_sup_set_class f5_dvelimdc a_wcel f1_dvelimdc a_wnf p_imp f0_dvelimdc f1_dvelimdc a_sup_set_class f2_dvelimdc a_sup_set_class a_wceq f1_dvelimdc a_wal a_wn a_wa f1_dvelimdc i0_dvelimdc f5_dvelimdc p_nfcd f0_dvelimdc f1_dvelimdc a_sup_set_class f2_dvelimdc a_sup_set_class a_wceq f1_dvelimdc a_wal a_wn f1_dvelimdc f5_dvelimdc a_wnfc p_ex $.
$}

$(Version of ~ dvelim for classes.  (Contributed by Mario Carneiro,
       8-Oct-2016.) $)

${
	$v x y z A B  $.
	f0_dvelimc $f set x $.
	f1_dvelimc $f set y $.
	f2_dvelimc $f set z $.
	f3_dvelimc $f class A $.
	f4_dvelimc $f class B $.
	e0_dvelimc $e |- F/_ x A $.
	e1_dvelimc $e |- F/_ z B $.
	e2_dvelimc $e |- ( z = y -> A = B ) $.
	p_dvelimc $p |- ( -. A. x x = y -> F/_ x B ) $= f0_dvelimc p_nftru f2_dvelimc p_nftru e0_dvelimc f0_dvelimc f3_dvelimc a_wnfc a_wtru p_a1i e1_dvelimc f2_dvelimc f4_dvelimc a_wnfc a_wtru p_a1i e2_dvelimc f2_dvelimc a_sup_set_class f1_dvelimc a_sup_set_class a_wceq f3_dvelimc f4_dvelimc a_wceq a_wi a_wtru p_a1i a_wtru f0_dvelimc f1_dvelimc f2_dvelimc f3_dvelimc f4_dvelimc p_dvelimdc f0_dvelimc a_sup_set_class f1_dvelimc a_sup_set_class a_wceq f0_dvelimc a_wal a_wn f0_dvelimc f4_dvelimc a_wnfc a_wi p_trud $.
$}

$(If ` x ` and ` y ` are distinct, then ` x ` is not free in ` y ` .
       (Contributed by Mario Carneiro, 8-Oct-2016.) $)

${
	$v x y  $.
	$d x z  $.
	$d y z  $.
	f0_nfcvf $f set x $.
	f1_nfcvf $f set y $.
	i0_nfcvf $f set z $.
	p_nfcvf $p |- ( -. A. x x = y -> F/_ x y ) $= f0_nfcvf i0_nfcvf a_sup_set_class p_nfcv i0_nfcvf f1_nfcvf a_sup_set_class p_nfcv i0_nfcvf a_sup_set_class f1_nfcvf a_sup_set_class a_wceq p_id f0_nfcvf f1_nfcvf i0_nfcvf i0_nfcvf a_sup_set_class f1_nfcvf a_sup_set_class p_dvelimc $.
$}

$(If ` x ` and ` y ` are distinct, then ` y ` is not free in ` x ` .
       (Contributed by Mario Carneiro, 5-Dec-2016.) $)

${
	$v x y  $.
	$d x  $.
	$d y  $.
	f0_nfcvf2 $f set x $.
	f1_nfcvf2 $f set y $.
	p_nfcvf2 $p |- ( -. A. x x = y -> F/_ y x ) $= f1_nfcvf2 f0_nfcvf2 p_nfcvf f1_nfcvf2 f0_nfcvf2 a_sup_set_class a_wnfc f1_nfcvf2 f0_nfcvf2 p_naecoms $.
$}

$(Establish equality between classes, using bound-variable hypotheses
       instead of distinct variable conditions.  (Contributed by NM,
       5-Aug-1993.)  (Revised by Mario Carneiro, 7-Oct-2016.) $)

${
	$v x A B  $.
	$d y A  $.
	$d y B  $.
	$d x y  $.
	f0_cleqf $f set x $.
	f1_cleqf $f class A $.
	f2_cleqf $f class B $.
	i0_cleqf $f set y $.
	e0_cleqf $e |- F/_ x A $.
	e1_cleqf $e |- F/_ x B $.
	p_cleqf $p |- ( A = B <-> A. x ( x e. A <-> x e. B ) ) $= i0_cleqf f1_cleqf f2_cleqf p_dfcleq f0_cleqf a_sup_set_class f1_cleqf a_wcel f0_cleqf a_sup_set_class f2_cleqf a_wcel a_wb i0_cleqf p_nfv e0_cleqf f0_cleqf i0_cleqf f1_cleqf p_nfcri e1_cleqf f0_cleqf i0_cleqf f2_cleqf p_nfcri i0_cleqf a_sup_set_class f1_cleqf a_wcel i0_cleqf a_sup_set_class f2_cleqf a_wcel f0_cleqf p_nfbi f0_cleqf a_sup_set_class i0_cleqf a_sup_set_class f1_cleqf p_eleq1 f0_cleqf a_sup_set_class i0_cleqf a_sup_set_class f2_cleqf p_eleq1 f0_cleqf a_sup_set_class i0_cleqf a_sup_set_class a_wceq f0_cleqf a_sup_set_class f1_cleqf a_wcel i0_cleqf a_sup_set_class f1_cleqf a_wcel f0_cleqf a_sup_set_class f2_cleqf a_wcel i0_cleqf a_sup_set_class f2_cleqf a_wcel p_bibi12d f0_cleqf a_sup_set_class f1_cleqf a_wcel f0_cleqf a_sup_set_class f2_cleqf a_wcel a_wb i0_cleqf a_sup_set_class f1_cleqf a_wcel i0_cleqf a_sup_set_class f2_cleqf a_wcel a_wb f0_cleqf i0_cleqf p_cbval f1_cleqf f2_cleqf a_wceq i0_cleqf a_sup_set_class f1_cleqf a_wcel i0_cleqf a_sup_set_class f2_cleqf a_wcel a_wb i0_cleqf a_wal f0_cleqf a_sup_set_class f1_cleqf a_wcel f0_cleqf a_sup_set_class f2_cleqf a_wcel a_wb f0_cleqf a_wal p_bitr4i $.
$}

$(A simplification of class abstraction.  Theorem 5.2 of [Quine] p. 35.
       (Contributed by NM, 5-Sep-2011.)  (Revised by Mario Carneiro,
       7-Oct-2016.) $)

${
	$v x A  $.
	$d A  $.
	$d x  $.
	f0_abid2f $f set x $.
	f1_abid2f $f class A $.
	e0_abid2f $e |- F/_ x A $.
	p_abid2f $p |- { x | x e. A } = A $= e0_abid2f f0_abid2f a_sup_set_class f1_abid2f a_wcel f0_abid2f p_nfab1 f0_abid2f f1_abid2f f0_abid2f a_sup_set_class f1_abid2f a_wcel f0_abid2f a_cab p_cleqf f0_abid2f a_sup_set_class f1_abid2f a_wcel f0_abid2f p_abid f0_abid2f a_sup_set_class f0_abid2f a_sup_set_class f1_abid2f a_wcel f0_abid2f a_cab a_wcel f0_abid2f a_sup_set_class f1_abid2f a_wcel f0_abid2f a_sup_set_class f1_abid2f a_wcel p_bibi2i f0_abid2f a_sup_set_class f1_abid2f a_wcel f0_abid2f a_sup_set_class f0_abid2f a_sup_set_class f1_abid2f a_wcel f0_abid2f a_cab a_wcel a_wb f0_abid2f a_sup_set_class f1_abid2f a_wcel f0_abid2f a_sup_set_class f1_abid2f a_wcel a_wb f0_abid2f p_albii f1_abid2f f0_abid2f a_sup_set_class f1_abid2f a_wcel f0_abid2f a_cab a_wceq f0_abid2f a_sup_set_class f1_abid2f a_wcel f0_abid2f a_sup_set_class f0_abid2f a_sup_set_class f1_abid2f a_wcel f0_abid2f a_cab a_wcel a_wb f0_abid2f a_wal f0_abid2f a_sup_set_class f1_abid2f a_wcel f0_abid2f a_sup_set_class f1_abid2f a_wcel a_wb f0_abid2f a_wal p_bitri f0_abid2f a_sup_set_class f1_abid2f a_wcel p_biid f1_abid2f f0_abid2f a_sup_set_class f1_abid2f a_wcel f0_abid2f a_cab a_wceq f0_abid2f a_sup_set_class f1_abid2f a_wcel f0_abid2f a_sup_set_class f1_abid2f a_wcel a_wb f0_abid2f p_mpgbir f1_abid2f f0_abid2f a_sup_set_class f1_abid2f a_wcel f0_abid2f a_cab p_eqcomi $.
$}

$(Theorem to move a substitution in and out of a class abstraction.
       (Contributed by NM, 27-Sep-2003.)  (Revised by Mario Carneiro,
       7-Oct-2016.) $)

${
	$v ph x y z A  $.
	$d v A  $.
	$d x z v  $.
	$d y z v  $.
	$d v ph  $.
	f0_sbabel $f wff ph $.
	f1_sbabel $f set x $.
	f2_sbabel $f set y $.
	f3_sbabel $f set z $.
	f4_sbabel $f class A $.
	i0_sbabel $f set v $.
	e0_sbabel $e |- F/_ x A $.
	p_sbabel $p |- ( [ y / x ] { z | ph } e. A <-> { z | [ y / x ] ph } e. A ) $= i0_sbabel a_sup_set_class f0_sbabel f3_sbabel a_cab a_wceq i0_sbabel a_sup_set_class f4_sbabel a_wcel a_wa i0_sbabel f1_sbabel f2_sbabel p_sbex i0_sbabel a_sup_set_class f0_sbabel f3_sbabel a_cab a_wceq i0_sbabel a_sup_set_class f4_sbabel a_wcel f1_sbabel f2_sbabel p_sban f3_sbabel a_sup_set_class i0_sbabel a_sup_set_class a_wcel f1_sbabel p_nfv f3_sbabel a_sup_set_class i0_sbabel a_sup_set_class a_wcel f1_sbabel f2_sbabel p_sbf f3_sbabel a_sup_set_class i0_sbabel a_sup_set_class a_wcel f3_sbabel a_sup_set_class i0_sbabel a_sup_set_class a_wcel f0_sbabel f1_sbabel f2_sbabel p_sbrbis f3_sbabel a_sup_set_class i0_sbabel a_sup_set_class a_wcel f0_sbabel a_wb f3_sbabel a_sup_set_class i0_sbabel a_sup_set_class a_wcel f0_sbabel f1_sbabel f2_sbabel a_wsb a_wb f1_sbabel f2_sbabel f3_sbabel p_sbalv f0_sbabel f3_sbabel i0_sbabel a_sup_set_class p_abeq2 i0_sbabel a_sup_set_class f0_sbabel f3_sbabel a_cab a_wceq f3_sbabel a_sup_set_class i0_sbabel a_sup_set_class a_wcel f0_sbabel a_wb f3_sbabel a_wal f1_sbabel f2_sbabel p_sbbii f0_sbabel f1_sbabel f2_sbabel a_wsb f3_sbabel i0_sbabel a_sup_set_class p_abeq2 f3_sbabel a_sup_set_class i0_sbabel a_sup_set_class a_wcel f0_sbabel a_wb f3_sbabel a_wal f1_sbabel f2_sbabel a_wsb f3_sbabel a_sup_set_class i0_sbabel a_sup_set_class a_wcel f0_sbabel f1_sbabel f2_sbabel a_wsb a_wb f3_sbabel a_wal i0_sbabel a_sup_set_class f0_sbabel f3_sbabel a_cab a_wceq f1_sbabel f2_sbabel a_wsb i0_sbabel a_sup_set_class f0_sbabel f1_sbabel f2_sbabel a_wsb f3_sbabel a_cab a_wceq p_3bitr4i e0_sbabel f1_sbabel i0_sbabel f4_sbabel p_nfcri i0_sbabel a_sup_set_class f4_sbabel a_wcel f1_sbabel f2_sbabel p_sbf i0_sbabel a_sup_set_class f0_sbabel f3_sbabel a_cab a_wceq f1_sbabel f2_sbabel a_wsb i0_sbabel a_sup_set_class f0_sbabel f1_sbabel f2_sbabel a_wsb f3_sbabel a_cab a_wceq i0_sbabel a_sup_set_class f4_sbabel a_wcel f1_sbabel f2_sbabel a_wsb i0_sbabel a_sup_set_class f4_sbabel a_wcel p_anbi12i i0_sbabel a_sup_set_class f0_sbabel f3_sbabel a_cab a_wceq i0_sbabel a_sup_set_class f4_sbabel a_wcel a_wa f1_sbabel f2_sbabel a_wsb i0_sbabel a_sup_set_class f0_sbabel f3_sbabel a_cab a_wceq f1_sbabel f2_sbabel a_wsb i0_sbabel a_sup_set_class f4_sbabel a_wcel f1_sbabel f2_sbabel a_wsb a_wa i0_sbabel a_sup_set_class f0_sbabel f1_sbabel f2_sbabel a_wsb f3_sbabel a_cab a_wceq i0_sbabel a_sup_set_class f4_sbabel a_wcel a_wa p_bitri i0_sbabel a_sup_set_class f0_sbabel f3_sbabel a_cab a_wceq i0_sbabel a_sup_set_class f4_sbabel a_wcel a_wa f1_sbabel f2_sbabel a_wsb i0_sbabel a_sup_set_class f0_sbabel f1_sbabel f2_sbabel a_wsb f3_sbabel a_cab a_wceq i0_sbabel a_sup_set_class f4_sbabel a_wcel a_wa i0_sbabel p_exbii i0_sbabel a_sup_set_class f0_sbabel f3_sbabel a_cab a_wceq i0_sbabel a_sup_set_class f4_sbabel a_wcel a_wa i0_sbabel a_wex f1_sbabel f2_sbabel a_wsb i0_sbabel a_sup_set_class f0_sbabel f3_sbabel a_cab a_wceq i0_sbabel a_sup_set_class f4_sbabel a_wcel a_wa f1_sbabel f2_sbabel a_wsb i0_sbabel a_wex i0_sbabel a_sup_set_class f0_sbabel f1_sbabel f2_sbabel a_wsb f3_sbabel a_cab a_wceq i0_sbabel a_sup_set_class f4_sbabel a_wcel a_wa i0_sbabel a_wex p_bitri i0_sbabel f0_sbabel f3_sbabel a_cab f4_sbabel a_df-clel f0_sbabel f3_sbabel a_cab f4_sbabel a_wcel i0_sbabel a_sup_set_class f0_sbabel f3_sbabel a_cab a_wceq i0_sbabel a_sup_set_class f4_sbabel a_wcel a_wa i0_sbabel a_wex f1_sbabel f2_sbabel p_sbbii i0_sbabel f0_sbabel f1_sbabel f2_sbabel a_wsb f3_sbabel a_cab f4_sbabel a_df-clel i0_sbabel a_sup_set_class f0_sbabel f3_sbabel a_cab a_wceq i0_sbabel a_sup_set_class f4_sbabel a_wcel a_wa i0_sbabel a_wex f1_sbabel f2_sbabel a_wsb i0_sbabel a_sup_set_class f0_sbabel f1_sbabel f2_sbabel a_wsb f3_sbabel a_cab a_wceq i0_sbabel a_sup_set_class f4_sbabel a_wcel a_wa i0_sbabel a_wex f0_sbabel f3_sbabel a_cab f4_sbabel a_wcel f1_sbabel f2_sbabel a_wsb f0_sbabel f1_sbabel f2_sbabel a_wsb f3_sbabel a_cab f4_sbabel a_wcel p_3bitr4i $.
$}


