$[ turnstile_special_source.mm $]

$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Older_axiomatization_(1_rule,_14_schemes)/Obsolete_schemes_ax-5o_ax-4_ax-6o_ax-9o_ax-10o_ax-10_ax-11o_ax-12o_ax-15_ax-16.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Rederive new axioms from old: theorems ax5 , ax6 , ax9from9o , ax11 , ax12

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Theorems ~ ax11 and ~ ax12 require some intermediate theorems that are
  included in this section.

$)

$(This theorem repeats ~ sp under the name ~ ax4 , so that the metamath
     program's "verify markup" command will check that it matches axiom scheme
     ~ ax-4 .  It is preferred that references to this theorem use the name
     ~ sp .  (Contributed by NM, 18-Aug-2017.)  (New usage is discouraged.)
     (Proof modification is discouraged.) $)

${
	$v ph x  $.
	f0_ax4 $f wff ph $.
	f1_ax4 $f set x $.
	p_ax4 $p |- ( A. x ph -> ph ) $= f0_ax4 f1_ax4 p_sp $.
$}

$(Rederivation of axiom ~ ax-5 from ~ ax-5o and other older axioms.  See
     ~ ax5o for the derivation of ~ ax-5o from ~ ax-5 .  (Contributed by NM,
     23-May-2008.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)

${
	$v ph ps x  $.
	f0_ax5 $f wff ph $.
	f1_ax5 $f wff ps $.
	f2_ax5 $f set x $.
	p_ax5 $p |- ( A. x ( ph -> ps ) -> ( A. x ph -> A. x ps ) ) $= f0_ax5 f1_ax5 a_wi f0_ax5 f2_ax5 a_wal f1_ax5 a_wi f2_ax5 a_ax-5o f0_ax5 f2_ax5 a_ax-4 f0_ax5 f1_ax5 a_wi f2_ax5 a_ax-4 f0_ax5 f2_ax5 a_wal f0_ax5 f0_ax5 f1_ax5 a_wi f2_ax5 a_wal f1_ax5 p_syl5 f0_ax5 f1_ax5 a_wi f2_ax5 a_wal f0_ax5 f2_ax5 a_wal f1_ax5 a_wi a_wi f0_ax5 f1_ax5 a_wi f2_ax5 a_wal f0_ax5 f2_ax5 a_wal f1_ax5 a_wi f2_ax5 a_wal a_wi f2_ax5 p_mpg f0_ax5 f1_ax5 f2_ax5 a_ax-5o f0_ax5 f1_ax5 a_wi f2_ax5 a_wal f0_ax5 f2_ax5 a_wal f1_ax5 a_wi f2_ax5 a_wal f0_ax5 f2_ax5 a_wal f1_ax5 f2_ax5 a_wal a_wi p_syl $.
$}

$(Rederivation of axiom ~ ax-6 from ~ ax-6o and other older axioms.  See
     ~ ax6o for the derivation of ~ ax-6o from ~ ax-6 .  (Contributed by NM,
     23-May-2008.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)

${
	$v ph x  $.
	f0_ax6 $f wff ph $.
	f1_ax6 $f set x $.
	p_ax6 $p |- ( -. A. x ph -> A. x -. A. x ph ) $= f0_ax6 f1_ax6 a_wal f1_ax6 a_wal a_wn f0_ax6 f1_ax6 a_wal a_wn f1_ax6 a_ax-5o f0_ax6 f1_ax6 a_wal f1_ax6 a_wal a_wn f1_ax6 a_ax-4 f0_ax6 f0_ax6 f1_ax6 a_wal f1_ax6 a_ax-5o f0_ax6 f1_ax6 a_wal p_id f0_ax6 f1_ax6 a_wal f0_ax6 f1_ax6 a_wal a_wi f0_ax6 f1_ax6 a_wal f0_ax6 f1_ax6 a_wal f1_ax6 a_wal a_wi f1_ax6 p_mpg f0_ax6 f1_ax6 a_wal f1_ax6 a_wal a_wn f1_ax6 a_wal f0_ax6 f1_ax6 a_wal f1_ax6 a_wal f0_ax6 f1_ax6 a_wal p_nsyl f0_ax6 f1_ax6 a_wal f1_ax6 a_wal a_wn f1_ax6 a_wal f0_ax6 f1_ax6 a_wal a_wn a_wi f0_ax6 f1_ax6 a_wal f1_ax6 a_wal a_wn f1_ax6 a_wal f0_ax6 f1_ax6 a_wal a_wn f1_ax6 a_wal a_wi f1_ax6 p_mpg f0_ax6 f1_ax6 a_wal f1_ax6 a_ax-6o f0_ax6 f1_ax6 a_wal f1_ax6 a_wal a_wn f1_ax6 a_wal f0_ax6 f1_ax6 a_wal a_wn f1_ax6 a_wal f0_ax6 f1_ax6 a_wal p_nsyl4 $.
$}

$(Rederivation of axiom ~ ax-9 from ~ ax-9o and other older axioms.  See
     ~ ax9o for the derivation of ~ ax-9o from ~ ax-9 .  Lemma L18 in [Megill]
     p. 446 (p. 14 of the preprint).  (Contributed by NM, 5-Aug-1993.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)

${
	$v x y  $.
	f0_ax9from9o $f set x $.
	f1_ax9from9o $f set y $.
	p_ax9from9o $p |- -. A. x -. x = y $= f0_ax9from9o a_sup_set_class f1_ax9from9o a_sup_set_class a_wceq a_wn f0_ax9from9o a_wal a_wn f0_ax9from9o f1_ax9from9o a_ax-9o f0_ax9from9o a_sup_set_class f1_ax9from9o a_sup_set_class a_wceq a_wn f0_ax9from9o a_ax-6o f0_ax9from9o a_sup_set_class f1_ax9from9o a_sup_set_class a_wceq a_wn f0_ax9from9o a_wal a_wn f0_ax9from9o a_wal f0_ax9from9o a_sup_set_class f1_ax9from9o a_sup_set_class a_wceq p_con4i f0_ax9from9o a_sup_set_class f1_ax9from9o a_sup_set_class a_wceq f0_ax9from9o a_sup_set_class f1_ax9from9o a_sup_set_class a_wceq a_wn f0_ax9from9o a_wal a_wn f0_ax9from9o a_wal a_wi f0_ax9from9o a_sup_set_class f1_ax9from9o a_sup_set_class a_wceq a_wn f0_ax9from9o a_wal a_wn f0_ax9from9o p_mpg $.
$}

$(` x ` is not free in ` A. x ph ` .  Example in Appendix in [Megill] p. 450
     (p. 19 of the preprint).  Also Lemma 22 of [Monk2] p. 114.  (Contributed
     by NM, 5-Aug-1993.)  (New usage is discouraged.) $)

${
	$v ph x  $.
	f0_hba1-o $f wff ph $.
	f1_hba1-o $f set x $.
	p_hba1-o $p |- ( A. x ph -> A. x A. x ph ) $= f0_hba1-o f1_hba1-o a_wal a_wn f1_hba1-o a_ax-4 f0_hba1-o f1_hba1-o a_wal a_wn f1_hba1-o a_wal f0_hba1-o f1_hba1-o a_wal p_con2i f0_hba1-o f1_hba1-o a_wal a_wn f1_hba1-o p_ax6 f0_hba1-o f1_hba1-o p_ax6 f0_hba1-o f1_hba1-o a_wal f0_hba1-o f1_hba1-o a_wal a_wn f1_hba1-o a_wal p_con1i f0_hba1-o f1_hba1-o a_wal a_wn f1_hba1-o a_wal a_wn f0_hba1-o f1_hba1-o a_wal f1_hba1-o p_alimi f0_hba1-o f1_hba1-o a_wal f0_hba1-o f1_hba1-o a_wal a_wn f1_hba1-o a_wal a_wn f0_hba1-o f1_hba1-o a_wal a_wn f1_hba1-o a_wal a_wn f1_hba1-o a_wal f0_hba1-o f1_hba1-o a_wal f1_hba1-o a_wal p_3syl $.
$}

$(Inference version of ~ ax-5o .  (Contributed by NM, 5-Aug-1993.)
       (New usage is discouraged.) $)

${
	$v ph ps x  $.
	f0_a5i-o $f wff ph $.
	f1_a5i-o $f wff ps $.
	f2_a5i-o $f set x $.
	e0_a5i-o $e |- ( A. x ph -> ps ) $.
	p_a5i-o $p |- ( A. x ph -> A. x ps ) $= f0_a5i-o f2_a5i-o p_hba1-o e0_a5i-o f0_a5i-o f2_a5i-o a_wal f1_a5i-o f2_a5i-o p_alrimih $.
$}

$(Commutation law for identical variable specifiers.  The antecedent and
     consequent are true when ` x ` and ` y ` are substituted with the same
     variable.  Lemma L12 in [Megill] p. 445 (p. 12 of the preprint).  Version
     of ~ aecom using ~ ax-10o .  Unlike ~ ax10from10o , this version does not
     require ~ ax-17 .  (Contributed by NM, 5-Aug-1993.)
     (New usage is discouraged.) $)

${
	$v x y  $.
	f0_aecom-o $f set x $.
	f1_aecom-o $f set y $.
	p_aecom-o $p |- ( A. x x = y -> A. y y = x ) $= f0_aecom-o a_sup_set_class f1_aecom-o a_sup_set_class a_wceq f0_aecom-o f1_aecom-o a_ax-10o f0_aecom-o a_sup_set_class f1_aecom-o a_sup_set_class a_wceq f0_aecom-o a_wal f0_aecom-o a_sup_set_class f1_aecom-o a_sup_set_class a_wceq f1_aecom-o a_wal p_pm2.43i f0_aecom-o f1_aecom-o p_equcomi f0_aecom-o a_sup_set_class f1_aecom-o a_sup_set_class a_wceq f1_aecom-o a_sup_set_class f0_aecom-o a_sup_set_class a_wceq f1_aecom-o p_alimi f0_aecom-o a_sup_set_class f1_aecom-o a_sup_set_class a_wceq f0_aecom-o a_wal f0_aecom-o a_sup_set_class f1_aecom-o a_sup_set_class a_wceq f1_aecom-o a_wal f1_aecom-o a_sup_set_class f0_aecom-o a_sup_set_class a_wceq f1_aecom-o a_wal p_syl $.
$}

$(A commutation rule for identical variable specifiers.  Version of
       ~ aecoms using ax-10o .  (Contributed by NM, 5-Aug-1993.)
       (New usage is discouraged.) $)

${
	$v ph x y  $.
	f0_aecoms-o $f wff ph $.
	f1_aecoms-o $f set x $.
	f2_aecoms-o $f set y $.
	e0_aecoms-o $e |- ( A. x x = y -> ph ) $.
	p_aecoms-o $p |- ( A. y y = x -> ph ) $= f2_aecoms-o f1_aecoms-o p_aecom-o e0_aecoms-o f2_aecoms-o a_sup_set_class f1_aecoms-o a_sup_set_class a_wceq f2_aecoms-o a_wal f1_aecoms-o a_sup_set_class f2_aecoms-o a_sup_set_class a_wceq f1_aecoms-o a_wal f0_aecoms-o p_syl $.
$}

$(All variables are effectively bound in an identical variable specifier.
     Version of ~ hbae using ~ ax-10o .  (Contributed by NM, 5-Aug-1993.)
     (Proof modification is disccouraged.)  (New usage is discouraged.) $)

${
	$v x y z  $.
	f0_hbae-o $f set x $.
	f1_hbae-o $f set y $.
	f2_hbae-o $f set z $.
	p_hbae-o $p |- ( A. x x = y -> A. z A. x x = y ) $= f0_hbae-o a_sup_set_class f1_hbae-o a_sup_set_class a_wceq f0_hbae-o a_ax-4 f0_hbae-o f1_hbae-o f2_hbae-o a_ax-12o f0_hbae-o a_sup_set_class f1_hbae-o a_sup_set_class a_wceq f0_hbae-o a_wal f0_hbae-o a_sup_set_class f1_hbae-o a_sup_set_class a_wceq f2_hbae-o a_sup_set_class f0_hbae-o a_sup_set_class a_wceq f2_hbae-o a_wal a_wn f2_hbae-o a_sup_set_class f1_hbae-o a_sup_set_class a_wceq f2_hbae-o a_wal a_wn f0_hbae-o a_sup_set_class f1_hbae-o a_sup_set_class a_wceq f2_hbae-o a_wal p_syl7 f0_hbae-o a_sup_set_class f1_hbae-o a_sup_set_class a_wceq f0_hbae-o f2_hbae-o a_ax-10o f0_hbae-o a_sup_set_class f1_hbae-o a_sup_set_class a_wceq f0_hbae-o a_wal f0_hbae-o a_sup_set_class f1_hbae-o a_sup_set_class a_wceq f2_hbae-o a_wal a_wi f0_hbae-o f2_hbae-o p_aecoms-o f0_hbae-o a_sup_set_class f1_hbae-o a_sup_set_class a_wceq f0_hbae-o f1_hbae-o a_ax-10o f0_hbae-o a_sup_set_class f1_hbae-o a_sup_set_class a_wceq f0_hbae-o a_wal f0_hbae-o a_sup_set_class f1_hbae-o a_sup_set_class a_wceq f1_hbae-o a_wal p_pm2.43i f0_hbae-o a_sup_set_class f1_hbae-o a_sup_set_class a_wceq f1_hbae-o f2_hbae-o a_ax-10o f0_hbae-o a_sup_set_class f1_hbae-o a_sup_set_class a_wceq f0_hbae-o a_wal f0_hbae-o a_sup_set_class f1_hbae-o a_sup_set_class a_wceq f1_hbae-o a_wal f1_hbae-o a_sup_set_class f2_hbae-o a_sup_set_class a_wceq f1_hbae-o a_wal f0_hbae-o a_sup_set_class f1_hbae-o a_sup_set_class a_wceq f2_hbae-o a_wal p_syl5 f0_hbae-o a_sup_set_class f1_hbae-o a_sup_set_class a_wceq f0_hbae-o a_wal f0_hbae-o a_sup_set_class f1_hbae-o a_sup_set_class a_wceq f2_hbae-o a_wal a_wi f1_hbae-o f2_hbae-o p_aecoms-o f2_hbae-o a_sup_set_class f0_hbae-o a_sup_set_class a_wceq f2_hbae-o a_wal f2_hbae-o a_sup_set_class f1_hbae-o a_sup_set_class a_wceq f2_hbae-o a_wal f0_hbae-o a_sup_set_class f1_hbae-o a_sup_set_class a_wceq f0_hbae-o a_wal f0_hbae-o a_sup_set_class f1_hbae-o a_sup_set_class a_wceq f2_hbae-o a_wal a_wi p_pm2.61ii f0_hbae-o a_sup_set_class f1_hbae-o a_sup_set_class a_wceq f0_hbae-o a_sup_set_class f1_hbae-o a_sup_set_class a_wceq f2_hbae-o a_wal f0_hbae-o p_a5i-o f0_hbae-o a_sup_set_class f1_hbae-o a_sup_set_class a_wceq f0_hbae-o f2_hbae-o a_ax-7 f0_hbae-o a_sup_set_class f1_hbae-o a_sup_set_class a_wceq f0_hbae-o a_wal f0_hbae-o a_sup_set_class f1_hbae-o a_sup_set_class a_wceq f2_hbae-o a_wal f0_hbae-o a_wal f0_hbae-o a_sup_set_class f1_hbae-o a_sup_set_class a_wceq f0_hbae-o a_wal f2_hbae-o a_wal p_syl $.
$}

$(Formula-building lemma for use with the Distinctor Reduction Theorem.
       Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).  Version of
       ~ dral1 using ~ ax-10o .  (Contributed by NM, 24-Nov-1994.)
       (New usage is discouraged.) $)

${
	$v ph ps x y  $.
	f0_dral1-o $f wff ph $.
	f1_dral1-o $f wff ps $.
	f2_dral1-o $f set x $.
	f3_dral1-o $f set y $.
	e0_dral1-o $e |- ( A. x x = y -> ( ph <-> ps ) ) $.
	p_dral1-o $p |- ( A. x x = y -> ( A. x ph <-> A. y ps ) ) $= f2_dral1-o f3_dral1-o f2_dral1-o p_hbae-o e0_dral1-o f2_dral1-o a_sup_set_class f3_dral1-o a_sup_set_class a_wceq f2_dral1-o a_wal f0_dral1-o f1_dral1-o p_biimpd f2_dral1-o a_sup_set_class f3_dral1-o a_sup_set_class a_wceq f2_dral1-o a_wal f0_dral1-o f1_dral1-o f2_dral1-o p_alimdh f1_dral1-o f2_dral1-o f3_dral1-o a_ax-10o f2_dral1-o a_sup_set_class f3_dral1-o a_sup_set_class a_wceq f2_dral1-o a_wal f0_dral1-o f2_dral1-o a_wal f1_dral1-o f2_dral1-o a_wal f1_dral1-o f3_dral1-o a_wal p_syld f2_dral1-o f3_dral1-o f3_dral1-o p_hbae-o e0_dral1-o f2_dral1-o a_sup_set_class f3_dral1-o a_sup_set_class a_wceq f2_dral1-o a_wal f0_dral1-o f1_dral1-o p_biimprd f2_dral1-o a_sup_set_class f3_dral1-o a_sup_set_class a_wceq f2_dral1-o a_wal f1_dral1-o f0_dral1-o f3_dral1-o p_alimdh f0_dral1-o f3_dral1-o f2_dral1-o a_ax-10o f0_dral1-o f3_dral1-o a_wal f0_dral1-o f2_dral1-o a_wal a_wi f3_dral1-o f2_dral1-o p_aecoms-o f2_dral1-o a_sup_set_class f3_dral1-o a_sup_set_class a_wceq f2_dral1-o a_wal f1_dral1-o f3_dral1-o a_wal f0_dral1-o f3_dral1-o a_wal f0_dral1-o f2_dral1-o a_wal p_syld f2_dral1-o a_sup_set_class f3_dral1-o a_sup_set_class a_wceq f2_dral1-o a_wal f0_dral1-o f2_dral1-o a_wal f1_dral1-o f3_dral1-o a_wal p_impbid $.
$}

$(Rederivation of axiom ~ ax-11 from ~ ax-11o , ~ ax-10o , and other older
     axioms.  The proof does not require ~ ax-16 or ~ ax-17 .  See theorem
     ~ ax11o for the derivation of ~ ax-11o from ~ ax-11 .

     An open problem is whether we can prove this using ~ ax-10 instead of
     ~ ax-10o .

     This proof uses newer axioms ~ ax-5 and ~ ax-9 , but since these are
     proved from the older axioms above, this is acceptable and lets us avoid
     having to reprove several earlier theorems to use ~ ax-5o and ~ ax-9o .
     (Contributed by NM, 22-Jan-2007.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)

${
	$v ph x y  $.
	f0_ax11 $f wff ph $.
	f1_ax11 $f set x $.
	f2_ax11 $f set y $.
	p_ax11 $p |- ( x = y -> ( A. y ph -> A. x ( x = y -> ph ) ) ) $= f1_ax11 a_sup_set_class f2_ax11 a_sup_set_class a_wceq f1_ax11 a_wal f0_ax11 p_biidd f0_ax11 f0_ax11 f1_ax11 f2_ax11 p_dral1-o f0_ax11 f1_ax11 a_sup_set_class f2_ax11 a_sup_set_class a_wceq a_ax-1 f0_ax11 f1_ax11 a_sup_set_class f2_ax11 a_sup_set_class a_wceq f0_ax11 a_wi f1_ax11 p_alimi f1_ax11 a_sup_set_class f2_ax11 a_sup_set_class a_wceq f1_ax11 a_wal f0_ax11 f2_ax11 a_wal f0_ax11 f1_ax11 a_wal f1_ax11 a_sup_set_class f2_ax11 a_sup_set_class a_wceq f0_ax11 a_wi f1_ax11 a_wal p_syl6bir f1_ax11 a_sup_set_class f2_ax11 a_sup_set_class a_wceq f1_ax11 a_wal f0_ax11 f2_ax11 a_wal f1_ax11 a_sup_set_class f2_ax11 a_sup_set_class a_wceq f0_ax11 a_wi f1_ax11 a_wal a_wi f1_ax11 a_sup_set_class f2_ax11 a_sup_set_class a_wceq p_a1d f0_ax11 f2_ax11 a_ax-4 f0_ax11 f1_ax11 f2_ax11 a_ax-11o f0_ax11 f2_ax11 a_wal f0_ax11 f1_ax11 a_sup_set_class f2_ax11 a_sup_set_class a_wceq f1_ax11 a_wal a_wn f1_ax11 a_sup_set_class f2_ax11 a_sup_set_class a_wceq f1_ax11 a_sup_set_class f2_ax11 a_sup_set_class a_wceq f0_ax11 a_wi f1_ax11 a_wal p_syl7 f1_ax11 a_sup_set_class f2_ax11 a_sup_set_class a_wceq f1_ax11 a_wal f1_ax11 a_sup_set_class f2_ax11 a_sup_set_class a_wceq f0_ax11 f2_ax11 a_wal f1_ax11 a_sup_set_class f2_ax11 a_sup_set_class a_wceq f0_ax11 a_wi f1_ax11 a_wal a_wi a_wi p_pm2.61i $.
$}

$(Derive ~ ax-12 from ~ ax-12o and other older axioms.

     This proof uses newer axioms ~ ax-5 and ~ ax-9 , but since these are
     proved from the older axioms above, this is acceptable and lets us avoid
     having to reprove several earlier theorems to use ~ ax-5o and ~ ax-9o .
     (Contributed by NM, 21-Dec-2015.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)

${
	$v x y z  $.
	f0_ax12 $f set x $.
	f1_ax12 $f set y $.
	f2_ax12 $f set z $.
	p_ax12 $p |- ( -. x = y -> ( y = z -> A. x y = z ) ) $= f0_ax12 a_sup_set_class f1_ax12 a_sup_set_class a_wceq f0_ax12 a_ax-4 f0_ax12 a_sup_set_class f1_ax12 a_sup_set_class a_wceq f0_ax12 a_wal f0_ax12 a_sup_set_class f1_ax12 a_sup_set_class a_wceq p_con3i f0_ax12 a_sup_set_class f1_ax12 a_sup_set_class a_wceq a_wn f0_ax12 a_sup_set_class f1_ax12 a_sup_set_class a_wceq f0_ax12 a_wal a_wn f1_ax12 a_sup_set_class f2_ax12 a_sup_set_class a_wceq p_adantr f2_ax12 f1_ax12 f0_ax12 p_equtrr f0_ax12 a_sup_set_class f2_ax12 a_sup_set_class a_wceq f0_ax12 a_sup_set_class f1_ax12 a_sup_set_class a_wceq a_wi f2_ax12 f1_ax12 p_equcoms f1_ax12 a_sup_set_class f2_ax12 a_sup_set_class a_wceq f0_ax12 a_sup_set_class f2_ax12 a_sup_set_class a_wceq f0_ax12 a_sup_set_class f1_ax12 a_sup_set_class a_wceq p_con3rr3 f0_ax12 a_sup_set_class f1_ax12 a_sup_set_class a_wceq a_wn f1_ax12 a_sup_set_class f2_ax12 a_sup_set_class a_wceq f0_ax12 a_sup_set_class f2_ax12 a_sup_set_class a_wceq a_wn p_imp f0_ax12 a_sup_set_class f2_ax12 a_sup_set_class a_wceq f0_ax12 a_ax-4 f0_ax12 a_sup_set_class f1_ax12 a_sup_set_class a_wceq a_wn f1_ax12 a_sup_set_class f2_ax12 a_sup_set_class a_wceq a_wa f0_ax12 a_sup_set_class f2_ax12 a_sup_set_class a_wceq f0_ax12 a_sup_set_class f2_ax12 a_sup_set_class a_wceq f0_ax12 a_wal p_nsyl f1_ax12 f2_ax12 f0_ax12 a_ax-12o f0_ax12 a_sup_set_class f1_ax12 a_sup_set_class a_wceq a_wn f1_ax12 a_sup_set_class f2_ax12 a_sup_set_class a_wceq a_wa f0_ax12 a_sup_set_class f1_ax12 a_sup_set_class a_wceq f0_ax12 a_wal a_wn f0_ax12 a_sup_set_class f2_ax12 a_sup_set_class a_wceq f0_ax12 a_wal a_wn f1_ax12 a_sup_set_class f2_ax12 a_sup_set_class a_wceq f1_ax12 a_sup_set_class f2_ax12 a_sup_set_class a_wceq f0_ax12 a_wal a_wi p_sylc f0_ax12 a_sup_set_class f1_ax12 a_sup_set_class a_wceq a_wn f1_ax12 a_sup_set_class f2_ax12 a_sup_set_class a_wceq f1_ax12 a_sup_set_class f2_ax12 a_sup_set_class a_wceq f1_ax12 a_sup_set_class f2_ax12 a_sup_set_class a_wceq f0_ax12 a_wal a_wi p_ex f0_ax12 a_sup_set_class f1_ax12 a_sup_set_class a_wceq a_wn f1_ax12 a_sup_set_class f2_ax12 a_sup_set_class a_wceq f1_ax12 a_sup_set_class f2_ax12 a_sup_set_class a_wceq f0_ax12 a_wal p_pm2.43d $.
$}


