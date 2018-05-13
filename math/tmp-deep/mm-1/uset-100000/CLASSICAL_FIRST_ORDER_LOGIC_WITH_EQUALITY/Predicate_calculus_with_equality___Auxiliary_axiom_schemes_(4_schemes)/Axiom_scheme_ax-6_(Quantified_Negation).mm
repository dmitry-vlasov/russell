$[ turnstile_special_source.mm $]

$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Tarski_s_system_S2_(1_rule,_6_schemes).mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
              Axiom scheme ax-6 (Quantified Negation)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(Axiom of Quantified Negation.  Axiom C5-2 of [Monk2] p. 113.  This axiom
     scheme is logically redundant (see ~ ax6w ) but is used as an auxiliary
     axiom to achieve metalogical completeness.  (Contributed by NM,
     5-Aug-1993.) $)

${
	$v ph x  $.
	f0_ax-6 $f wff ph $.
	f1_ax-6 $f set x $.
	a_ax-6 $a |- ( -. A. x ph -> A. x -. A. x ph ) $.
$}

$(` x ` is not free in ` -. A. x ph ` .  (Contributed by NM, 5-Aug-1993.)
     (Proof shortened by Wolf Lammen, 18-Aug-2014.) $)

${
	$v ph x  $.
	f0_hbn1 $f wff ph $.
	f1_hbn1 $f set x $.
	p_hbn1 $p |- ( -. A. x ph -> A. x -. A. x ph ) $= f0_hbn1 f1_hbn1 a_ax-6 $.
$}

$(` x ` is not free in ` E. x ph ` .  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph x  $.
	f0_hbe1 $f wff ph $.
	f1_hbe1 $f set x $.
	p_hbe1 $p |- ( E. x ph -> A. x E. x ph ) $= f0_hbe1 f1_hbe1 a_df-ex f0_hbe1 a_wn f1_hbe1 p_hbn1 f0_hbe1 f1_hbe1 a_wex f0_hbe1 a_wn f1_hbe1 a_wal a_wn f1_hbe1 p_hbxfrbi $.
$}

$(` x ` is not free in ` E. x ph ` .  (Contributed by Mario Carneiro,
     11-Aug-2016.) $)

${
	$v ph x  $.
	f0_nfe1 $f wff ph $.
	f1_nfe1 $f set x $.
	p_nfe1 $p |- F/ x E. x ph $= f0_nfe1 f1_nfe1 p_hbe1 f0_nfe1 f1_nfe1 a_wex f1_nfe1 p_nfi $.
$}

$(The analog in our "pure" predicate calculus of axiom 5 of modal logic S5.
     (Contributed by NM, 5-Oct-2005.) $)

${
	$v ph x  $.
	f0_modal-5 $f wff ph $.
	f1_modal-5 $f set x $.
	p_modal-5 $p |- ( -. A. x -. ph -> A. x -. A. x -. ph ) $= f0_modal-5 a_wn f1_modal-5 p_hbn1 $.
$}


