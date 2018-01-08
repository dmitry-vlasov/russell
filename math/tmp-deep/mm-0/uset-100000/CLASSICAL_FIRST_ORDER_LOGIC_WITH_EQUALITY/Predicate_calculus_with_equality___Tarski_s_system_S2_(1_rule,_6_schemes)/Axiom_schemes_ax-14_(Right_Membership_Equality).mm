$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Tarski_s_system_S2_(1_rule,_6_schemes)/Axiom_schemes_ax-13_(Left_Membership_Equality).mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Axiom schemes ax-14 (Right Membership Equality)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( Axiom of Right Membership Equality.  One of the equality and substitution
     axioms for a non-logical predicate in our predicate calculus with
     equality.  It substitutes equal variables into the right-hand side of the
     ` e. ` binary predicate.  This axiom scheme is a sub-scheme of Axiom
     Scheme B8 of system S2 of [Tarski], p. 75, whose general form cannot be
     represented with our notation.  Also appears as Axiom scheme C13' in
     [Megill] p. 448 (p. 16 of the preprint).  (Contributed by NM,
     5-Aug-1993.) $)
${
	fax-14_0 $f set x $.
	fax-14_1 $f set y $.
	fax-14_2 $f set z $.
	ax-14 $a |- ( x = y -> ( z e. x -> z e. y ) ) $.
$}
$( An identity law for the non-logical predicate.  (Contributed by NM,
     5-Aug-1993.) $)
${
	felequ2_0 $f set x $.
	felequ2_1 $f set y $.
	felequ2_2 $f set z $.
	elequ2 $p |- ( x = y -> ( z e. x <-> z e. y ) ) $= felequ2_0 felequ2_1 weq felequ2_2 felequ2_0 wel felequ2_2 felequ2_1 wel felequ2_0 felequ2_1 felequ2_2 ax-14 felequ2_2 felequ2_1 wel felequ2_2 felequ2_0 wel wi felequ2_1 felequ2_0 felequ2_1 felequ2_0 felequ2_2 ax-14 equcoms impbid $.
$}

