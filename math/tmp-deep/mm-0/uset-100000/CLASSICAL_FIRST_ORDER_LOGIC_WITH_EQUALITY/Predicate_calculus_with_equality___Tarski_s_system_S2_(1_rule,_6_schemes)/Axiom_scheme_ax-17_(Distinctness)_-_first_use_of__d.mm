$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Tarski_s_system_S2_(1_rule,_6_schemes)/Axiom_scheme_ax-5_(Quantified_Implication).mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Axiom scheme ax-17 (Distinctness) - first use of $d

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( Axiom of Distinctness.  This axiom quantifies a variable over a formula
       in which it does not occur.  Axiom C5 in [Megill] p. 444 (p. 11 of the
       preprint).  Also appears as Axiom B6 (p. 75) of system S2 of [Tarski]
       p. 77 and Axiom C5-1 of [Monk2] p. 113.

       (See comments in ~ ax17o about the logical redundancy of ~ ax-17 in the
       presence of our obsolete axioms.)

       This axiom essentially says that if ` x ` does not occur in ` ph ` ,
       i.e. ` ph ` does not depend on ` x ` in any way, then we can add the
       quantifier ` A. x ` to ` ph ` with no further assumptions.  By ~ sp , we
       can also remove the quantifier (unconditionally).  (Contributed by NM,
       5-Aug-1993.) $)
${
	$d x ph $.
	fax-17_0 $f wff ph $.
	fax-17_1 $f set x $.
	ax-17 $a |- ( ph -> A. x ph ) $.
$}
$( ~ ax-17 with antecedent.  Useful in proofs of deduction versions of
       bound-variable hypothesis builders.  (Contributed by NM, 1-Mar-2013.) $)
${
	$d x ps $.
	fa17d_0 $f wff ph $.
	fa17d_1 $f wff ps $.
	fa17d_2 $f set x $.
	a17d $p |- ( ph -> ( ps -> A. x ps ) ) $= fa17d_1 fa17d_1 fa17d_2 wal wi fa17d_0 fa17d_1 fa17d_2 ax-17 a1i $.
$}
$( If ` x ` is not present in ` ph ` , then ` x ` is not free in ` ph ` .
       (Contributed by Mario Carneiro, 11-Aug-2016.) $)
${
	$d x ph $.
	fnfv_0 $f wff ph $.
	fnfv_1 $f set x $.
	nfv $p |- F/ x ph $= fnfv_0 fnfv_1 fnfv_0 fnfv_1 ax-17 nfi $.
$}
$( ~ nfv with antecedent.  Useful in proofs of deduction versions of
       bound-variable hypothesis builders such as ~ nfimd .  (Contributed by
       Mario Carneiro, 6-Oct-2016.) $)
${
	$d x ps $.
	fnfvd_0 $f wff ph $.
	fnfvd_1 $f wff ps $.
	fnfvd_2 $f set x $.
	nfvd $p |- ( ph -> F/ x ps ) $= fnfvd_1 fnfvd_2 wnf fnfvd_0 fnfvd_1 fnfvd_2 nfv a1i $.
$}
$( Deduction from Theorem 19.20 of [Margaris] p. 90.  (Contributed by NM,
       3-Apr-1994.) $)
${
	$d x ph $.
	falimdv_0 $f wff ph $.
	falimdv_1 $f wff ps $.
	falimdv_2 $f wff ch $.
	falimdv_3 $f set x $.
	ealimdv_0 $e |- ( ph -> ( ps -> ch ) ) $.
	alimdv $p |- ( ph -> ( A. x ps -> A. x ch ) ) $= falimdv_0 falimdv_1 falimdv_2 falimdv_3 falimdv_0 falimdv_3 ax-17 ealimdv_0 alimdh $.
$}
$( Deduction from Theorem 19.22 of [Margaris] p. 90.  (Contributed by NM,
       27-Apr-1994.) $)
${
	$d x ph $.
	feximdv_0 $f wff ph $.
	feximdv_1 $f wff ps $.
	feximdv_2 $f wff ch $.
	feximdv_3 $f set x $.
	eeximdv_0 $e |- ( ph -> ( ps -> ch ) ) $.
	eximdv $p |- ( ph -> ( E. x ps -> E. x ch ) ) $= feximdv_0 feximdv_1 feximdv_2 feximdv_3 feximdv_0 feximdv_3 ax-17 eeximdv_0 eximdh $.
$}
$( Deduction from Theorem 19.22 of [Margaris] p. 90.  (Contributed by NM,
       27-Apr-2004.) $)
${
	$d x ph $.
	$d y ph $.
	f2alimdv_0 $f wff ph $.
	f2alimdv_1 $f wff ps $.
	f2alimdv_2 $f wff ch $.
	f2alimdv_3 $f set x $.
	f2alimdv_4 $f set y $.
	e2alimdv_0 $e |- ( ph -> ( ps -> ch ) ) $.
	2alimdv $p |- ( ph -> ( A. x A. y ps -> A. x A. y ch ) ) $= f2alimdv_0 f2alimdv_1 f2alimdv_4 wal f2alimdv_2 f2alimdv_4 wal f2alimdv_3 f2alimdv_0 f2alimdv_1 f2alimdv_2 f2alimdv_4 e2alimdv_0 alimdv alimdv $.
$}
$( Deduction from Theorem 19.22 of [Margaris] p. 90.  (Contributed by NM,
       3-Aug-1995.) $)
${
	$d x ph $.
	$d y ph $.
	f2eximdv_0 $f wff ph $.
	f2eximdv_1 $f wff ps $.
	f2eximdv_2 $f wff ch $.
	f2eximdv_3 $f set x $.
	f2eximdv_4 $f set y $.
	e2eximdv_0 $e |- ( ph -> ( ps -> ch ) ) $.
	2eximdv $p |- ( ph -> ( E. x E. y ps -> E. x E. y ch ) ) $= f2eximdv_0 f2eximdv_1 f2eximdv_4 wex f2eximdv_2 f2eximdv_4 wex f2eximdv_3 f2eximdv_0 f2eximdv_1 f2eximdv_2 f2eximdv_4 e2eximdv_0 eximdv eximdv $.
$}
$( Formula-building rule for universal quantifier (deduction rule).
       (Contributed by NM, 5-Aug-1993.) $)
${
	$d x ph $.
	falbidv_0 $f wff ph $.
	falbidv_1 $f wff ps $.
	falbidv_2 $f wff ch $.
	falbidv_3 $f set x $.
	ealbidv_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	albidv $p |- ( ph -> ( A. x ps <-> A. x ch ) ) $= falbidv_0 falbidv_1 falbidv_2 falbidv_3 falbidv_0 falbidv_3 ax-17 ealbidv_0 albidh $.
$}
$( Formula-building rule for existential quantifier (deduction rule).
       (Contributed by NM, 5-Aug-1993.) $)
${
	$d x ph $.
	fexbidv_0 $f wff ph $.
	fexbidv_1 $f wff ps $.
	fexbidv_2 $f wff ch $.
	fexbidv_3 $f set x $.
	eexbidv_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	exbidv $p |- ( ph -> ( E. x ps <-> E. x ch ) ) $= fexbidv_0 fexbidv_1 fexbidv_2 fexbidv_3 fexbidv_0 fexbidv_3 ax-17 eexbidv_0 exbidh $.
$}
$( Formula-building rule for 2 universal quantifiers (deduction rule).
       (Contributed by NM, 4-Mar-1997.) $)
${
	$d x ph $.
	$d y ph $.
	f2albidv_0 $f wff ph $.
	f2albidv_1 $f wff ps $.
	f2albidv_2 $f wff ch $.
	f2albidv_3 $f set x $.
	f2albidv_4 $f set y $.
	e2albidv_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	2albidv $p |- ( ph -> ( A. x A. y ps <-> A. x A. y ch ) ) $= f2albidv_0 f2albidv_1 f2albidv_4 wal f2albidv_2 f2albidv_4 wal f2albidv_3 f2albidv_0 f2albidv_1 f2albidv_2 f2albidv_4 e2albidv_0 albidv albidv $.
$}
$( Formula-building rule for 2 existential quantifiers (deduction rule).
       (Contributed by NM, 1-May-1995.) $)
${
	$d x ph $.
	$d y ph $.
	f2exbidv_0 $f wff ph $.
	f2exbidv_1 $f wff ps $.
	f2exbidv_2 $f wff ch $.
	f2exbidv_3 $f set x $.
	f2exbidv_4 $f set y $.
	e2exbidv_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	2exbidv $p |- ( ph -> ( E. x E. y ps <-> E. x E. y ch ) ) $= f2exbidv_0 f2exbidv_1 f2exbidv_4 wex f2exbidv_2 f2exbidv_4 wex f2exbidv_3 f2exbidv_0 f2exbidv_1 f2exbidv_2 f2exbidv_4 e2exbidv_0 exbidv exbidv $.
$}
$( Formula-building rule for 3 existential quantifiers (deduction rule).
       (Contributed by NM, 1-May-1995.) $)
${
	$d x ph $.
	$d y ph $.
	$d z ph $.
	f3exbidv_0 $f wff ph $.
	f3exbidv_1 $f wff ps $.
	f3exbidv_2 $f wff ch $.
	f3exbidv_3 $f set x $.
	f3exbidv_4 $f set y $.
	f3exbidv_5 $f set z $.
	e3exbidv_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	3exbidv $p |- ( ph -> ( E. x E. y E. z ps <-> E. x E. y E. z ch ) ) $= f3exbidv_0 f3exbidv_1 f3exbidv_5 wex f3exbidv_2 f3exbidv_5 wex f3exbidv_3 f3exbidv_4 f3exbidv_0 f3exbidv_1 f3exbidv_2 f3exbidv_5 e3exbidv_0 exbidv 2exbidv $.
$}
$( Formula-building rule for 4 existential quantifiers (deduction rule).
       (Contributed by NM, 3-Aug-1995.) $)
$v w $.
${
	$d x ph $.
	$d y ph $.
	$d z ph $.
	$d w ph $.
	f4exbidv_0 $f wff ph $.
	f4exbidv_1 $f wff ps $.
	f4exbidv_2 $f wff ch $.
	f4exbidv_3 $f set x $.
	f4exbidv_4 $f set y $.
	f4exbidv_5 $f set z $.
	f4exbidv_6 $f set w $.
	e4exbidv_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	4exbidv $p |- ( ph -> ( E. x E. y E. z E. w ps <-> E. x E. y E. z E. w ch ) ) $= f4exbidv_0 f4exbidv_1 f4exbidv_6 wex f4exbidv_5 wex f4exbidv_2 f4exbidv_6 wex f4exbidv_5 wex f4exbidv_3 f4exbidv_4 f4exbidv_0 f4exbidv_1 f4exbidv_2 f4exbidv_5 f4exbidv_6 e4exbidv_0 2exbidv 2exbidv $.
$}
$( Inference from Theorem 19.21 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)
${
	$d x ph $.
	falrimiv_0 $f wff ph $.
	falrimiv_1 $f wff ps $.
	falrimiv_2 $f set x $.
	ealrimiv_0 $e |- ( ph -> ps ) $.
	alrimiv $p |- ( ph -> A. x ps ) $= falrimiv_0 falrimiv_1 falrimiv_2 falrimiv_0 falrimiv_2 ax-17 ealrimiv_0 alrimih $.
$}
$( Inference from Theorem 19.21 of [Margaris] p. 90.  (Contributed by NM,
       31-Jul-1995.) $)
${
	$d x ph $.
	$d y ph $.
	falrimivv_0 $f wff ph $.
	falrimivv_1 $f wff ps $.
	falrimivv_2 $f set x $.
	falrimivv_3 $f set y $.
	ealrimivv_0 $e |- ( ph -> ps ) $.
	alrimivv $p |- ( ph -> A. x A. y ps ) $= falrimivv_0 falrimivv_1 falrimivv_3 wal falrimivv_2 falrimivv_0 falrimivv_1 falrimivv_3 ealrimivv_0 alrimiv alrimiv $.
$}
$( Deduction from Theorem 19.21 of [Margaris] p. 90.  (Contributed by NM,
       10-Feb-1997.) $)
${
	$d x ph $.
	$d x ps $.
	falrimdv_0 $f wff ph $.
	falrimdv_1 $f wff ps $.
	falrimdv_2 $f wff ch $.
	falrimdv_3 $f set x $.
	ealrimdv_0 $e |- ( ph -> ( ps -> ch ) ) $.
	alrimdv $p |- ( ph -> ( ps -> A. x ch ) ) $= falrimdv_0 falrimdv_1 falrimdv_2 falrimdv_3 falrimdv_0 falrimdv_3 ax-17 falrimdv_1 falrimdv_3 ax-17 ealrimdv_0 alrimdh $.
$}
$( Apply the definition of not-free in a context.  (Contributed by Mario
       Carneiro, 11-Aug-2016.) $)
${
	$d x ph $.
	fnfdv_0 $f wff ph $.
	fnfdv_1 $f wff ps $.
	fnfdv_2 $f set x $.
	enfdv_0 $e |- ( ph -> ( ps -> A. x ps ) ) $.
	nfdv $p |- ( ph -> F/ x ps ) $= fnfdv_0 fnfdv_1 fnfdv_1 fnfdv_2 wal wi fnfdv_2 wal fnfdv_1 fnfdv_2 wnf fnfdv_0 fnfdv_1 fnfdv_1 fnfdv_2 wal wi fnfdv_2 enfdv_0 alrimiv fnfdv_1 fnfdv_2 df-nf sylibr $.
$}
$( Quantification of two variables over a formula in which they do not
       occur.  (Contributed by Alan Sare, 12-Apr-2011.) $)
${
	$d x ph $.
	$d y ph $.
	f2ax17_0 $f wff ph $.
	f2ax17_1 $f set x $.
	f2ax17_2 $f set y $.
	2ax17 $p |- ( ph -> A. x A. y ph ) $= f2ax17_0 f2ax17_0 f2ax17_1 f2ax17_2 f2ax17_0 id alrimivv $.
$}

