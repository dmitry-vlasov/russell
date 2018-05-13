$[ turnstile_special_source.mm $]

$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Tarski_s_system_S2_(1_rule,_6_schemes)/Axiom_scheme_ax-5_(Quantified_Implication).mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Axiom scheme ax-17 (Distinctness) - first use of $d

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(Axiom of Distinctness.  This axiom quantifies a variable over a formula
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
	$v ph x  $.
	$d x ph  $.
	f0_ax-17 $f wff ph $.
	f1_ax-17 $f set x $.
	a_ax-17 $a |- ( ph -> A. x ph ) $.
$}

$(~ ax-17 with antecedent.  Useful in proofs of deduction versions of
       bound-variable hypothesis builders.  (Contributed by NM, 1-Mar-2013.) $)

${
	$v ph ps x  $.
	$d x ps  $.
	f0_a17d $f wff ph $.
	f1_a17d $f wff ps $.
	f2_a17d $f set x $.
	p_a17d $p |- ( ph -> ( ps -> A. x ps ) ) $= f1_a17d f2_a17d a_ax-17 f1_a17d f1_a17d f2_a17d a_wal a_wi f0_a17d p_a1i $.
$}

$(If ` x ` is not present in ` ph ` , then ` x ` is not free in ` ph ` .
       (Contributed by Mario Carneiro, 11-Aug-2016.) $)

${
	$v ph x  $.
	$d x ph  $.
	f0_nfv $f wff ph $.
	f1_nfv $f set x $.
	p_nfv $p |- F/ x ph $= f0_nfv f1_nfv a_ax-17 f0_nfv f1_nfv p_nfi $.
$}

$(~ nfv with antecedent.  Useful in proofs of deduction versions of
       bound-variable hypothesis builders such as ~ nfimd .  (Contributed by
       Mario Carneiro, 6-Oct-2016.) $)

${
	$v ph ps x  $.
	$d x ps  $.
	f0_nfvd $f wff ph $.
	f1_nfvd $f wff ps $.
	f2_nfvd $f set x $.
	p_nfvd $p |- ( ph -> F/ x ps ) $= f1_nfvd f2_nfvd p_nfv f1_nfvd f2_nfvd a_wnf f0_nfvd p_a1i $.
$}

$(Deduction from Theorem 19.20 of [Margaris] p. 90.  (Contributed by NM,
       3-Apr-1994.) $)

${
	$v ph ps ch x  $.
	$d x ph  $.
	f0_alimdv $f wff ph $.
	f1_alimdv $f wff ps $.
	f2_alimdv $f wff ch $.
	f3_alimdv $f set x $.
	e0_alimdv $e |- ( ph -> ( ps -> ch ) ) $.
	p_alimdv $p |- ( ph -> ( A. x ps -> A. x ch ) ) $= f0_alimdv f3_alimdv a_ax-17 e0_alimdv f0_alimdv f1_alimdv f2_alimdv f3_alimdv p_alimdh $.
$}

$(Deduction from Theorem 19.22 of [Margaris] p. 90.  (Contributed by NM,
       27-Apr-1994.) $)

${
	$v ph ps ch x  $.
	$d x ph  $.
	f0_eximdv $f wff ph $.
	f1_eximdv $f wff ps $.
	f2_eximdv $f wff ch $.
	f3_eximdv $f set x $.
	e0_eximdv $e |- ( ph -> ( ps -> ch ) ) $.
	p_eximdv $p |- ( ph -> ( E. x ps -> E. x ch ) ) $= f0_eximdv f3_eximdv a_ax-17 e0_eximdv f0_eximdv f1_eximdv f2_eximdv f3_eximdv p_eximdh $.
$}

$(Deduction from Theorem 19.22 of [Margaris] p. 90.  (Contributed by NM,
       27-Apr-2004.) $)

${
	$v ph ps ch x y  $.
	$d x ph  $.
	$d y ph  $.
	f0_2alimdv $f wff ph $.
	f1_2alimdv $f wff ps $.
	f2_2alimdv $f wff ch $.
	f3_2alimdv $f set x $.
	f4_2alimdv $f set y $.
	e0_2alimdv $e |- ( ph -> ( ps -> ch ) ) $.
	p_2alimdv $p |- ( ph -> ( A. x A. y ps -> A. x A. y ch ) ) $= e0_2alimdv f0_2alimdv f1_2alimdv f2_2alimdv f4_2alimdv p_alimdv f0_2alimdv f1_2alimdv f4_2alimdv a_wal f2_2alimdv f4_2alimdv a_wal f3_2alimdv p_alimdv $.
$}

$(Deduction from Theorem 19.22 of [Margaris] p. 90.  (Contributed by NM,
       3-Aug-1995.) $)

${
	$v ph ps ch x y  $.
	$d x ph  $.
	$d y ph  $.
	f0_2eximdv $f wff ph $.
	f1_2eximdv $f wff ps $.
	f2_2eximdv $f wff ch $.
	f3_2eximdv $f set x $.
	f4_2eximdv $f set y $.
	e0_2eximdv $e |- ( ph -> ( ps -> ch ) ) $.
	p_2eximdv $p |- ( ph -> ( E. x E. y ps -> E. x E. y ch ) ) $= e0_2eximdv f0_2eximdv f1_2eximdv f2_2eximdv f4_2eximdv p_eximdv f0_2eximdv f1_2eximdv f4_2eximdv a_wex f2_2eximdv f4_2eximdv a_wex f3_2eximdv p_eximdv $.
$}

$(Formula-building rule for universal quantifier (deduction rule).
       (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps ch x  $.
	$d x ph  $.
	f0_albidv $f wff ph $.
	f1_albidv $f wff ps $.
	f2_albidv $f wff ch $.
	f3_albidv $f set x $.
	e0_albidv $e |- ( ph -> ( ps <-> ch ) ) $.
	p_albidv $p |- ( ph -> ( A. x ps <-> A. x ch ) ) $= f0_albidv f3_albidv a_ax-17 e0_albidv f0_albidv f1_albidv f2_albidv f3_albidv p_albidh $.
$}

$(Formula-building rule for existential quantifier (deduction rule).
       (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps ch x  $.
	$d x ph  $.
	f0_exbidv $f wff ph $.
	f1_exbidv $f wff ps $.
	f2_exbidv $f wff ch $.
	f3_exbidv $f set x $.
	e0_exbidv $e |- ( ph -> ( ps <-> ch ) ) $.
	p_exbidv $p |- ( ph -> ( E. x ps <-> E. x ch ) ) $= f0_exbidv f3_exbidv a_ax-17 e0_exbidv f0_exbidv f1_exbidv f2_exbidv f3_exbidv p_exbidh $.
$}

$(Formula-building rule for 2 universal quantifiers (deduction rule).
       (Contributed by NM, 4-Mar-1997.) $)

${
	$v ph ps ch x y  $.
	$d x ph  $.
	$d y ph  $.
	f0_2albidv $f wff ph $.
	f1_2albidv $f wff ps $.
	f2_2albidv $f wff ch $.
	f3_2albidv $f set x $.
	f4_2albidv $f set y $.
	e0_2albidv $e |- ( ph -> ( ps <-> ch ) ) $.
	p_2albidv $p |- ( ph -> ( A. x A. y ps <-> A. x A. y ch ) ) $= e0_2albidv f0_2albidv f1_2albidv f2_2albidv f4_2albidv p_albidv f0_2albidv f1_2albidv f4_2albidv a_wal f2_2albidv f4_2albidv a_wal f3_2albidv p_albidv $.
$}

$(Formula-building rule for 2 existential quantifiers (deduction rule).
       (Contributed by NM, 1-May-1995.) $)

${
	$v ph ps ch x y  $.
	$d x ph  $.
	$d y ph  $.
	f0_2exbidv $f wff ph $.
	f1_2exbidv $f wff ps $.
	f2_2exbidv $f wff ch $.
	f3_2exbidv $f set x $.
	f4_2exbidv $f set y $.
	e0_2exbidv $e |- ( ph -> ( ps <-> ch ) ) $.
	p_2exbidv $p |- ( ph -> ( E. x E. y ps <-> E. x E. y ch ) ) $= e0_2exbidv f0_2exbidv f1_2exbidv f2_2exbidv f4_2exbidv p_exbidv f0_2exbidv f1_2exbidv f4_2exbidv a_wex f2_2exbidv f4_2exbidv a_wex f3_2exbidv p_exbidv $.
$}

$(Formula-building rule for 3 existential quantifiers (deduction rule).
       (Contributed by NM, 1-May-1995.) $)

${
	$v ph ps ch x y z  $.
	$d x ph  $.
	$d y ph  $.
	$d z ph  $.
	f0_3exbidv $f wff ph $.
	f1_3exbidv $f wff ps $.
	f2_3exbidv $f wff ch $.
	f3_3exbidv $f set x $.
	f4_3exbidv $f set y $.
	f5_3exbidv $f set z $.
	e0_3exbidv $e |- ( ph -> ( ps <-> ch ) ) $.
	p_3exbidv $p |- ( ph -> ( E. x E. y E. z ps <-> E. x E. y E. z ch ) ) $= e0_3exbidv f0_3exbidv f1_3exbidv f2_3exbidv f5_3exbidv p_exbidv f0_3exbidv f1_3exbidv f5_3exbidv a_wex f2_3exbidv f5_3exbidv a_wex f3_3exbidv f4_3exbidv p_2exbidv $.
$}

$(Formula-building rule for 4 existential quantifiers (deduction rule).
       (Contributed by NM, 3-Aug-1995.) $)

${
	$v ph ps ch x y z w  $.
	$d x ph  $.
	$d y ph  $.
	$d z ph  $.
	$d w ph  $.
	f0_4exbidv $f wff ph $.
	f1_4exbidv $f wff ps $.
	f2_4exbidv $f wff ch $.
	f3_4exbidv $f set x $.
	f4_4exbidv $f set y $.
	f5_4exbidv $f set z $.
	f6_4exbidv $f set w $.
	e0_4exbidv $e |- ( ph -> ( ps <-> ch ) ) $.
	p_4exbidv $p |- ( ph -> ( E. x E. y E. z E. w ps <-> E. x E. y E. z E. w ch ) ) $= e0_4exbidv f0_4exbidv f1_4exbidv f2_4exbidv f5_4exbidv f6_4exbidv p_2exbidv f0_4exbidv f1_4exbidv f6_4exbidv a_wex f5_4exbidv a_wex f2_4exbidv f6_4exbidv a_wex f5_4exbidv a_wex f3_4exbidv f4_4exbidv p_2exbidv $.
$}

$(Inference from Theorem 19.21 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v ph ps x  $.
	$d x ph  $.
	f0_alrimiv $f wff ph $.
	f1_alrimiv $f wff ps $.
	f2_alrimiv $f set x $.
	e0_alrimiv $e |- ( ph -> ps ) $.
	p_alrimiv $p |- ( ph -> A. x ps ) $= f0_alrimiv f2_alrimiv a_ax-17 e0_alrimiv f0_alrimiv f1_alrimiv f2_alrimiv p_alrimih $.
$}

$(Inference from Theorem 19.21 of [Margaris] p. 90.  (Contributed by NM,
       31-Jul-1995.) $)

${
	$v ph ps x y  $.
	$d x ph  $.
	$d y ph  $.
	f0_alrimivv $f wff ph $.
	f1_alrimivv $f wff ps $.
	f2_alrimivv $f set x $.
	f3_alrimivv $f set y $.
	e0_alrimivv $e |- ( ph -> ps ) $.
	p_alrimivv $p |- ( ph -> A. x A. y ps ) $= e0_alrimivv f0_alrimivv f1_alrimivv f3_alrimivv p_alrimiv f0_alrimivv f1_alrimivv f3_alrimivv a_wal f2_alrimivv p_alrimiv $.
$}

$(Deduction from Theorem 19.21 of [Margaris] p. 90.  (Contributed by NM,
       10-Feb-1997.) $)

${
	$v ph ps ch x  $.
	$d x ph  $.
	$d x ps  $.
	f0_alrimdv $f wff ph $.
	f1_alrimdv $f wff ps $.
	f2_alrimdv $f wff ch $.
	f3_alrimdv $f set x $.
	e0_alrimdv $e |- ( ph -> ( ps -> ch ) ) $.
	p_alrimdv $p |- ( ph -> ( ps -> A. x ch ) ) $= f0_alrimdv f3_alrimdv a_ax-17 f1_alrimdv f3_alrimdv a_ax-17 e0_alrimdv f0_alrimdv f1_alrimdv f2_alrimdv f3_alrimdv p_alrimdh $.
$}

$(Apply the definition of not-free in a context.  (Contributed by Mario
       Carneiro, 11-Aug-2016.) $)

${
	$v ph ps x  $.
	$d x ph  $.
	f0_nfdv $f wff ph $.
	f1_nfdv $f wff ps $.
	f2_nfdv $f set x $.
	e0_nfdv $e |- ( ph -> ( ps -> A. x ps ) ) $.
	p_nfdv $p |- ( ph -> F/ x ps ) $= e0_nfdv f0_nfdv f1_nfdv f1_nfdv f2_nfdv a_wal a_wi f2_nfdv p_alrimiv f1_nfdv f2_nfdv a_df-nf f0_nfdv f1_nfdv f1_nfdv f2_nfdv a_wal a_wi f2_nfdv a_wal f1_nfdv f2_nfdv a_wnf p_sylibr $.
$}

$(Quantification of two variables over a formula in which they do not
       occur.  (Contributed by Alan Sare, 12-Apr-2011.) $)

${
	$v ph x y  $.
	$d x ph  $.
	$d y ph  $.
	f0_2ax17 $f wff ph $.
	f1_2ax17 $f set x $.
	f2_2ax17 $f set y $.
	p_2ax17 $p |- ( ph -> A. x A. y ph ) $= f0_2ax17 p_id f0_2ax17 f0_2ax17 f1_2ax17 f2_2ax17 p_alrimivv $.
$}


