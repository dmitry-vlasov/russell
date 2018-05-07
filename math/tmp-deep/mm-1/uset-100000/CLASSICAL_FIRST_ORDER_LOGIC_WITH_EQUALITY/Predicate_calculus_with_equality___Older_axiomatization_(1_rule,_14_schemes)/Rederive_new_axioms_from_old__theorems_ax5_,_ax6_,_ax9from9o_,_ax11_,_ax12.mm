$[ turnstile_special_source.mm $]
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Older_axiomatization_(1_rule,_14_schemes)/Obsolete_schemes_ax-5o_ax-4_ax-6o_ax-9o_ax-10o_ax-10_ax-11o_ax-12o_ax-15_ax-16.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Rederive new axioms from old: theorems ax5 , ax6 , ax9from9o , ax11 , ax12

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Theorems ~ ax11 and ~ ax12 require some intermediate theorems that are
  included in this section.

$)
$( This theorem repeats ~ sp under the name ~ ax4 , so that the metamath
     program's "verify markup" command will check that it matches axiom scheme
     ~ ax-4 .  It is preferred that references to this theorem use the name
     ~ sp .  (Contributed by NM, 18-Aug-2017.)  (New usage is discouraged.)
     (Proof modification is discouraged.) $)
${
	$v ph $.
	$v x $.
	fax4_0 $f wff ph $.
	fax4_1 $f set x $.
	ax4 $p |- ( A. x ph -> ph ) $= fax4_0 fax4_1 sp $.
$}
$( Rederivation of axiom ~ ax-5 from ~ ax-5o and other older axioms.  See
     ~ ax5o for the derivation of ~ ax-5o from ~ ax-5 .  (Contributed by NM,
     23-May-2008.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	fax5_0 $f wff ph $.
	fax5_1 $f wff ps $.
	fax5_2 $f set x $.
	ax5 $p |- ( A. x ( ph -> ps ) -> ( A. x ph -> A. x ps ) ) $= fax5_0 fax5_1 wi fax5_2 wal fax5_0 fax5_2 wal fax5_1 wi fax5_2 wal fax5_0 fax5_2 wal fax5_1 fax5_2 wal wi fax5_0 fax5_1 wi fax5_2 wal fax5_0 fax5_2 wal fax5_1 wi wi fax5_0 fax5_1 wi fax5_2 wal fax5_0 fax5_2 wal fax5_1 wi fax5_2 wal wi fax5_2 fax5_0 fax5_1 wi fax5_0 fax5_2 wal fax5_1 wi fax5_2 ax-5o fax5_0 fax5_2 wal fax5_0 fax5_0 fax5_1 wi fax5_2 wal fax5_1 fax5_0 fax5_2 ax-4 fax5_0 fax5_1 wi fax5_2 ax-4 syl5 mpg fax5_0 fax5_1 fax5_2 ax-5o syl $.
$}
$( Rederivation of axiom ~ ax-6 from ~ ax-6o and other older axioms.  See
     ~ ax6o for the derivation of ~ ax-6o from ~ ax-6 .  (Contributed by NM,
     23-May-2008.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
${
	$v ph $.
	$v x $.
	fax6_0 $f wff ph $.
	fax6_1 $f set x $.
	ax6 $p |- ( -. A. x ph -> A. x -. A. x ph ) $= fax6_0 fax6_1 wal fax6_1 wal wn fax6_1 wal fax6_0 fax6_1 wal wn fax6_1 wal fax6_0 fax6_1 wal fax6_0 fax6_1 wal fax6_1 wal wn fax6_1 wal fax6_0 fax6_1 wal wn wi fax6_0 fax6_1 wal fax6_1 wal wn fax6_1 wal fax6_0 fax6_1 wal wn fax6_1 wal wi fax6_1 fax6_0 fax6_1 wal fax6_1 wal wn fax6_0 fax6_1 wal wn fax6_1 ax-5o fax6_0 fax6_1 wal fax6_1 wal wn fax6_1 wal fax6_0 fax6_1 wal fax6_1 wal fax6_0 fax6_1 wal fax6_0 fax6_1 wal fax6_1 wal wn fax6_1 ax-4 fax6_0 fax6_1 wal fax6_0 fax6_1 wal wi fax6_0 fax6_1 wal fax6_0 fax6_1 wal fax6_1 wal wi fax6_1 fax6_0 fax6_0 fax6_1 wal fax6_1 ax-5o fax6_0 fax6_1 wal id mpg nsyl mpg fax6_0 fax6_1 wal fax6_1 ax-6o nsyl4 $.
$}
$( Rederivation of axiom ~ ax-9 from ~ ax-9o and other older axioms.  See
     ~ ax9o for the derivation of ~ ax-9o from ~ ax-9 .  Lemma L18 in [Megill]
     p. 446 (p. 14 of the preprint).  (Contributed by NM, 5-Aug-1993.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	$v x $.
	$v y $.
	fax9from9o_0 $f set x $.
	fax9from9o_1 $f set y $.
	ax9from9o $p |- -. A. x -. x = y $= fax9from9o_0 sup_set_class fax9from9o_1 sup_set_class wceq fax9from9o_0 sup_set_class fax9from9o_1 sup_set_class wceq wn fax9from9o_0 wal wn fax9from9o_0 wal wi fax9from9o_0 sup_set_class fax9from9o_1 sup_set_class wceq wn fax9from9o_0 wal wn fax9from9o_0 fax9from9o_0 sup_set_class fax9from9o_1 sup_set_class wceq wn fax9from9o_0 wal wn fax9from9o_0 fax9from9o_1 ax-9o fax9from9o_0 sup_set_class fax9from9o_1 sup_set_class wceq wn fax9from9o_0 wal wn fax9from9o_0 wal fax9from9o_0 sup_set_class fax9from9o_1 sup_set_class wceq fax9from9o_0 sup_set_class fax9from9o_1 sup_set_class wceq wn fax9from9o_0 ax-6o con4i mpg $.
$}
$( ` x ` is not free in ` A. x ph ` .  Example in Appendix in [Megill] p. 450
     (p. 19 of the preprint).  Also Lemma 22 of [Monk2] p. 114.  (Contributed
     by NM, 5-Aug-1993.)  (New usage is discouraged.) $)
${
	$v ph $.
	$v x $.
	fhba1-o_0 $f wff ph $.
	fhba1-o_1 $f set x $.
	hba1-o $p |- ( A. x ph -> A. x A. x ph ) $= fhba1-o_0 fhba1-o_1 wal fhba1-o_0 fhba1-o_1 wal wn fhba1-o_1 wal wn fhba1-o_0 fhba1-o_1 wal wn fhba1-o_1 wal wn fhba1-o_1 wal fhba1-o_0 fhba1-o_1 wal fhba1-o_1 wal fhba1-o_0 fhba1-o_1 wal wn fhba1-o_1 wal fhba1-o_0 fhba1-o_1 wal fhba1-o_0 fhba1-o_1 wal wn fhba1-o_1 ax-4 con2i fhba1-o_0 fhba1-o_1 wal wn fhba1-o_1 ax6 fhba1-o_0 fhba1-o_1 wal wn fhba1-o_1 wal wn fhba1-o_0 fhba1-o_1 wal fhba1-o_1 fhba1-o_0 fhba1-o_1 wal fhba1-o_0 fhba1-o_1 wal wn fhba1-o_1 wal fhba1-o_0 fhba1-o_1 ax6 con1i alimi 3syl $.
$}
$( Inference version of ~ ax-5o .  (Contributed by NM, 5-Aug-1993.)
       (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	fa5i-o_0 $f wff ph $.
	fa5i-o_1 $f wff ps $.
	fa5i-o_2 $f set x $.
	ea5i-o_0 $e |- ( A. x ph -> ps ) $.
	a5i-o $p |- ( A. x ph -> A. x ps ) $= fa5i-o_0 fa5i-o_2 wal fa5i-o_1 fa5i-o_2 fa5i-o_0 fa5i-o_2 hba1-o ea5i-o_0 alrimih $.
$}
$( Commutation law for identical variable specifiers.  The antecedent and
     consequent are true when ` x ` and ` y ` are substituted with the same
     variable.  Lemma L12 in [Megill] p. 445 (p. 12 of the preprint).  Version
     of ~ aecom using ~ ax-10o .  Unlike ~ ax10from10o , this version does not
     require ~ ax-17 .  (Contributed by NM, 5-Aug-1993.)
     (New usage is discouraged.) $)
${
	$v x $.
	$v y $.
	faecom-o_0 $f set x $.
	faecom-o_1 $f set y $.
	aecom-o $p |- ( A. x x = y -> A. y y = x ) $= faecom-o_0 sup_set_class faecom-o_1 sup_set_class wceq faecom-o_0 wal faecom-o_0 sup_set_class faecom-o_1 sup_set_class wceq faecom-o_1 wal faecom-o_1 sup_set_class faecom-o_0 sup_set_class wceq faecom-o_1 wal faecom-o_0 sup_set_class faecom-o_1 sup_set_class wceq faecom-o_0 wal faecom-o_0 sup_set_class faecom-o_1 sup_set_class wceq faecom-o_1 wal faecom-o_0 sup_set_class faecom-o_1 sup_set_class wceq faecom-o_0 faecom-o_1 ax-10o pm2.43i faecom-o_0 sup_set_class faecom-o_1 sup_set_class wceq faecom-o_1 sup_set_class faecom-o_0 sup_set_class wceq faecom-o_1 faecom-o_0 faecom-o_1 equcomi alimi syl $.
$}
$( A commutation rule for identical variable specifiers.  Version of
       ~ aecoms using ax-10o .  (Contributed by NM, 5-Aug-1993.)
       (New usage is discouraged.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	faecoms-o_0 $f wff ph $.
	faecoms-o_1 $f set x $.
	faecoms-o_2 $f set y $.
	eaecoms-o_0 $e |- ( A. x x = y -> ph ) $.
	aecoms-o $p |- ( A. y y = x -> ph ) $= faecoms-o_2 sup_set_class faecoms-o_1 sup_set_class wceq faecoms-o_2 wal faecoms-o_1 sup_set_class faecoms-o_2 sup_set_class wceq faecoms-o_1 wal faecoms-o_0 faecoms-o_2 faecoms-o_1 aecom-o eaecoms-o_0 syl $.
$}
$( All variables are effectively bound in an identical variable specifier.
     Version of ~ hbae using ~ ax-10o .  (Contributed by NM, 5-Aug-1993.)
     (Proof modification is disccouraged.)  (New usage is discouraged.) $)
${
	$v x $.
	$v y $.
	$v z $.
	fhbae-o_0 $f set x $.
	fhbae-o_1 $f set y $.
	fhbae-o_2 $f set z $.
	hbae-o $p |- ( A. x x = y -> A. z A. x x = y ) $= fhbae-o_0 sup_set_class fhbae-o_1 sup_set_class wceq fhbae-o_0 wal fhbae-o_0 sup_set_class fhbae-o_1 sup_set_class wceq fhbae-o_2 wal fhbae-o_0 wal fhbae-o_0 sup_set_class fhbae-o_1 sup_set_class wceq fhbae-o_0 wal fhbae-o_2 wal fhbae-o_0 sup_set_class fhbae-o_1 sup_set_class wceq fhbae-o_0 sup_set_class fhbae-o_1 sup_set_class wceq fhbae-o_2 wal fhbae-o_0 fhbae-o_2 sup_set_class fhbae-o_0 sup_set_class wceq fhbae-o_2 wal fhbae-o_2 sup_set_class fhbae-o_1 sup_set_class wceq fhbae-o_2 wal fhbae-o_0 sup_set_class fhbae-o_1 sup_set_class wceq fhbae-o_0 wal fhbae-o_0 sup_set_class fhbae-o_1 sup_set_class wceq fhbae-o_2 wal wi fhbae-o_0 sup_set_class fhbae-o_1 sup_set_class wceq fhbae-o_0 wal fhbae-o_0 sup_set_class fhbae-o_1 sup_set_class wceq fhbae-o_2 sup_set_class fhbae-o_0 sup_set_class wceq fhbae-o_2 wal wn fhbae-o_2 sup_set_class fhbae-o_1 sup_set_class wceq fhbae-o_2 wal wn fhbae-o_0 sup_set_class fhbae-o_1 sup_set_class wceq fhbae-o_2 wal fhbae-o_0 sup_set_class fhbae-o_1 sup_set_class wceq fhbae-o_0 ax-4 fhbae-o_0 fhbae-o_1 fhbae-o_2 ax-12o syl7 fhbae-o_0 sup_set_class fhbae-o_1 sup_set_class wceq fhbae-o_0 wal fhbae-o_0 sup_set_class fhbae-o_1 sup_set_class wceq fhbae-o_2 wal wi fhbae-o_0 fhbae-o_2 fhbae-o_0 sup_set_class fhbae-o_1 sup_set_class wceq fhbae-o_0 fhbae-o_2 ax-10o aecoms-o fhbae-o_0 sup_set_class fhbae-o_1 sup_set_class wceq fhbae-o_0 wal fhbae-o_0 sup_set_class fhbae-o_1 sup_set_class wceq fhbae-o_2 wal wi fhbae-o_1 fhbae-o_2 fhbae-o_0 sup_set_class fhbae-o_1 sup_set_class wceq fhbae-o_0 wal fhbae-o_0 sup_set_class fhbae-o_1 sup_set_class wceq fhbae-o_1 wal fhbae-o_1 sup_set_class fhbae-o_2 sup_set_class wceq fhbae-o_1 wal fhbae-o_0 sup_set_class fhbae-o_1 sup_set_class wceq fhbae-o_2 wal fhbae-o_0 sup_set_class fhbae-o_1 sup_set_class wceq fhbae-o_0 wal fhbae-o_0 sup_set_class fhbae-o_1 sup_set_class wceq fhbae-o_1 wal fhbae-o_0 sup_set_class fhbae-o_1 sup_set_class wceq fhbae-o_0 fhbae-o_1 ax-10o pm2.43i fhbae-o_0 sup_set_class fhbae-o_1 sup_set_class wceq fhbae-o_1 fhbae-o_2 ax-10o syl5 aecoms-o pm2.61ii a5i-o fhbae-o_0 sup_set_class fhbae-o_1 sup_set_class wceq fhbae-o_0 fhbae-o_2 ax-7 syl $.
$}
$( Formula-building lemma for use with the Distinctor Reduction Theorem.
       Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).  Version of
       ~ dral1 using ~ ax-10o .  (Contributed by NM, 24-Nov-1994.)
       (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	fdral1-o_0 $f wff ph $.
	fdral1-o_1 $f wff ps $.
	fdral1-o_2 $f set x $.
	fdral1-o_3 $f set y $.
	edral1-o_0 $e |- ( A. x x = y -> ( ph <-> ps ) ) $.
	dral1-o $p |- ( A. x x = y -> ( A. x ph <-> A. y ps ) ) $= fdral1-o_2 sup_set_class fdral1-o_3 sup_set_class wceq fdral1-o_2 wal fdral1-o_0 fdral1-o_2 wal fdral1-o_1 fdral1-o_3 wal fdral1-o_2 sup_set_class fdral1-o_3 sup_set_class wceq fdral1-o_2 wal fdral1-o_0 fdral1-o_2 wal fdral1-o_1 fdral1-o_2 wal fdral1-o_1 fdral1-o_3 wal fdral1-o_2 sup_set_class fdral1-o_3 sup_set_class wceq fdral1-o_2 wal fdral1-o_0 fdral1-o_1 fdral1-o_2 fdral1-o_2 fdral1-o_3 fdral1-o_2 hbae-o fdral1-o_2 sup_set_class fdral1-o_3 sup_set_class wceq fdral1-o_2 wal fdral1-o_0 fdral1-o_1 edral1-o_0 biimpd alimdh fdral1-o_1 fdral1-o_2 fdral1-o_3 ax-10o syld fdral1-o_2 sup_set_class fdral1-o_3 sup_set_class wceq fdral1-o_2 wal fdral1-o_1 fdral1-o_3 wal fdral1-o_0 fdral1-o_3 wal fdral1-o_0 fdral1-o_2 wal fdral1-o_2 sup_set_class fdral1-o_3 sup_set_class wceq fdral1-o_2 wal fdral1-o_1 fdral1-o_0 fdral1-o_3 fdral1-o_2 fdral1-o_3 fdral1-o_3 hbae-o fdral1-o_2 sup_set_class fdral1-o_3 sup_set_class wceq fdral1-o_2 wal fdral1-o_0 fdral1-o_1 edral1-o_0 biimprd alimdh fdral1-o_0 fdral1-o_3 wal fdral1-o_0 fdral1-o_2 wal wi fdral1-o_3 fdral1-o_2 fdral1-o_0 fdral1-o_3 fdral1-o_2 ax-10o aecoms-o syld impbid $.
$}
$( Rederivation of axiom ~ ax-11 from ~ ax-11o , ~ ax-10o , and other older
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
	$v ph $.
	$v x $.
	$v y $.
	fax11_0 $f wff ph $.
	fax11_1 $f set x $.
	fax11_2 $f set y $.
	ax11 $p |- ( x = y -> ( A. y ph -> A. x ( x = y -> ph ) ) ) $= fax11_1 sup_set_class fax11_2 sup_set_class wceq fax11_1 wal fax11_1 sup_set_class fax11_2 sup_set_class wceq fax11_0 fax11_2 wal fax11_1 sup_set_class fax11_2 sup_set_class wceq fax11_0 wi fax11_1 wal wi wi fax11_1 sup_set_class fax11_2 sup_set_class wceq fax11_1 wal fax11_0 fax11_2 wal fax11_1 sup_set_class fax11_2 sup_set_class wceq fax11_0 wi fax11_1 wal wi fax11_1 sup_set_class fax11_2 sup_set_class wceq fax11_1 sup_set_class fax11_2 sup_set_class wceq fax11_1 wal fax11_0 fax11_2 wal fax11_0 fax11_1 wal fax11_1 sup_set_class fax11_2 sup_set_class wceq fax11_0 wi fax11_1 wal fax11_0 fax11_0 fax11_1 fax11_2 fax11_1 sup_set_class fax11_2 sup_set_class wceq fax11_1 wal fax11_0 biidd dral1-o fax11_0 fax11_1 sup_set_class fax11_2 sup_set_class wceq fax11_0 wi fax11_1 fax11_0 fax11_1 sup_set_class fax11_2 sup_set_class wceq ax-1 alimi syl6bir a1d fax11_0 fax11_2 wal fax11_0 fax11_1 sup_set_class fax11_2 sup_set_class wceq fax11_1 wal wn fax11_1 sup_set_class fax11_2 sup_set_class wceq fax11_1 sup_set_class fax11_2 sup_set_class wceq fax11_0 wi fax11_1 wal fax11_0 fax11_2 ax-4 fax11_0 fax11_1 fax11_2 ax-11o syl7 pm2.61i $.
$}
$( Derive ~ ax-12 from ~ ax-12o and other older axioms.

     This proof uses newer axioms ~ ax-5 and ~ ax-9 , but since these are
     proved from the older axioms above, this is acceptable and lets us avoid
     having to reprove several earlier theorems to use ~ ax-5o and ~ ax-9o .
     (Contributed by NM, 21-Dec-2015.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
${
	$v x $.
	$v y $.
	$v z $.
	fax12_0 $f set x $.
	fax12_1 $f set y $.
	fax12_2 $f set z $.
	ax12 $p |- ( -. x = y -> ( y = z -> A. x y = z ) ) $= fax12_0 sup_set_class fax12_1 sup_set_class wceq wn fax12_1 sup_set_class fax12_2 sup_set_class wceq fax12_1 sup_set_class fax12_2 sup_set_class wceq fax12_0 wal fax12_0 sup_set_class fax12_1 sup_set_class wceq wn fax12_1 sup_set_class fax12_2 sup_set_class wceq fax12_1 sup_set_class fax12_2 sup_set_class wceq fax12_1 sup_set_class fax12_2 sup_set_class wceq fax12_0 wal wi fax12_0 sup_set_class fax12_1 sup_set_class wceq wn fax12_1 sup_set_class fax12_2 sup_set_class wceq wa fax12_0 sup_set_class fax12_1 sup_set_class wceq fax12_0 wal wn fax12_0 sup_set_class fax12_2 sup_set_class wceq fax12_0 wal wn fax12_1 sup_set_class fax12_2 sup_set_class wceq fax12_1 sup_set_class fax12_2 sup_set_class wceq fax12_0 wal wi fax12_0 sup_set_class fax12_1 sup_set_class wceq wn fax12_0 sup_set_class fax12_1 sup_set_class wceq fax12_0 wal wn fax12_1 sup_set_class fax12_2 sup_set_class wceq fax12_0 sup_set_class fax12_1 sup_set_class wceq fax12_0 wal fax12_0 sup_set_class fax12_1 sup_set_class wceq fax12_0 sup_set_class fax12_1 sup_set_class wceq fax12_0 ax-4 con3i adantr fax12_0 sup_set_class fax12_1 sup_set_class wceq wn fax12_1 sup_set_class fax12_2 sup_set_class wceq wa fax12_0 sup_set_class fax12_2 sup_set_class wceq fax12_0 sup_set_class fax12_2 sup_set_class wceq fax12_0 wal fax12_0 sup_set_class fax12_1 sup_set_class wceq wn fax12_1 sup_set_class fax12_2 sup_set_class wceq fax12_0 sup_set_class fax12_2 sup_set_class wceq wn fax12_1 sup_set_class fax12_2 sup_set_class wceq fax12_0 sup_set_class fax12_2 sup_set_class wceq fax12_0 sup_set_class fax12_1 sup_set_class wceq fax12_0 sup_set_class fax12_2 sup_set_class wceq fax12_0 sup_set_class fax12_1 sup_set_class wceq wi fax12_2 fax12_1 fax12_2 fax12_1 fax12_0 equtrr equcoms con3rr3 imp fax12_0 sup_set_class fax12_2 sup_set_class wceq fax12_0 ax-4 nsyl fax12_1 fax12_2 fax12_0 ax-12o sylc ex pm2.43d $.
$}

