$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Tarski_s_system_S2_(1_rule,_6_schemes).mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
              Axiom scheme ax-6 (Quantified Negation)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( Axiom of Quantified Negation.  Axiom C5-2 of [Monk2] p. 113.  This axiom
     scheme is logically redundant (see ~ ax6w ) but is used as an auxiliary
     axiom to achieve metalogical completeness.  (Contributed by NM,
     5-Aug-1993.) $)
${
	$v ph $.
	$v x $.
	fax-6_0 $f wff ph $.
	fax-6_1 $f set x $.
	ax-6 $a |- ( -. A. x ph -> A. x -. A. x ph ) $.
$}
$( ` x ` is not free in ` -. A. x ph ` .  (Contributed by NM, 5-Aug-1993.)
     (Proof shortened by Wolf Lammen, 18-Aug-2014.) $)
${
	$v ph $.
	$v x $.
	fhbn1_0 $f wff ph $.
	fhbn1_1 $f set x $.
	hbn1 $p |- ( -. A. x ph -> A. x -. A. x ph ) $= fhbn1_0 fhbn1_1 ax-6 $.
$}
$( ` x ` is not free in ` E. x ph ` .  (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v x $.
	fhbe1_0 $f wff ph $.
	fhbe1_1 $f set x $.
	hbe1 $p |- ( E. x ph -> A. x E. x ph ) $= fhbe1_0 fhbe1_1 wex fhbe1_0 wn fhbe1_1 wal wn fhbe1_1 fhbe1_0 fhbe1_1 df-ex fhbe1_0 wn fhbe1_1 hbn1 hbxfrbi $.
$}
$( ` x ` is not free in ` E. x ph ` .  (Contributed by Mario Carneiro,
     11-Aug-2016.) $)
${
	$v ph $.
	$v x $.
	fnfe1_0 $f wff ph $.
	fnfe1_1 $f set x $.
	nfe1 $p |- F/ x E. x ph $= fnfe1_0 fnfe1_1 wex fnfe1_1 fnfe1_0 fnfe1_1 hbe1 nfi $.
$}
$( The analog in our "pure" predicate calculus of axiom 5 of modal logic S5.
     (Contributed by NM, 5-Oct-2005.) $)
${
	$v ph $.
	$v x $.
	fmodal-5_0 $f wff ph $.
	fmodal-5_1 $f set x $.
	modal-5 $p |- ( -. A. x -. ph -> A. x -. A. x -. ph ) $= fmodal-5_0 wn fmodal-5_1 hbn1 $.
$}

