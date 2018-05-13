$[ turnstile_special_source.mm $]

$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Tarski_s_system_S2_(1_rule,_6_schemes)/Axiom_schemes_ax-13_(Left_Membership_Equality).mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Axiom schemes ax-14 (Right Membership Equality)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(Axiom of Right Membership Equality.  One of the equality and substitution
     axioms for a non-logical predicate in our predicate calculus with
     equality.  It substitutes equal variables into the right-hand side of the
     ` e. ` binary predicate.  This axiom scheme is a sub-scheme of Axiom
     Scheme B8 of system S2 of [Tarski], p. 75, whose general form cannot be
     represented with our notation.  Also appears as Axiom scheme C13' in
     [Megill] p. 448 (p. 16 of the preprint).  (Contributed by NM,
     5-Aug-1993.) $)

${
	$v x y z  $.
	f0_ax-14 $f set x $.
	f1_ax-14 $f set y $.
	f2_ax-14 $f set z $.
	a_ax-14 $a |- ( x = y -> ( z e. x -> z e. y ) ) $.
$}

$(An identity law for the non-logical predicate.  (Contributed by NM,
     5-Aug-1993.) $)

${
	$v x y z  $.
	f0_elequ2 $f set x $.
	f1_elequ2 $f set y $.
	f2_elequ2 $f set z $.
	p_elequ2 $p |- ( x = y -> ( z e. x <-> z e. y ) ) $= f0_elequ2 f1_elequ2 f2_elequ2 a_ax-14 f1_elequ2 f0_elequ2 f2_elequ2 a_ax-14 f2_elequ2 a_sup_set_class f1_elequ2 a_sup_set_class a_wcel f2_elequ2 a_sup_set_class f0_elequ2 a_sup_set_class a_wcel a_wi f1_elequ2 f0_elequ2 p_equcoms f0_elequ2 a_sup_set_class f1_elequ2 a_sup_set_class a_wceq f2_elequ2 a_sup_set_class f0_elequ2 a_sup_set_class a_wcel f2_elequ2 a_sup_set_class f1_elequ2 a_sup_set_class a_wcel p_impbid $.
$}


