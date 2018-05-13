$[ turnstile_special_source.mm $]

$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Auxiliary_axiom_schemes_(4_schemes)/Axiom_scheme_ax-11_(Substitution).mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
          Axiom scheme ax-12 (Quantified Equality)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(Axiom of Quantified Equality.  One of the equality and substitution axioms
     of predicate calculus with equality.

     An equivalent way to express this axiom that may be easier to understand
     is ` ( -. x = y -> ( -. x = z -> ( y = z -> A. x y = z ) ) ) ` (see
     ~ ax12b ).  Recall that in the intended interpretation, our variables are
     metavariables ranging over the variables of predicate calculus (the object
     language).  In order for the first antecedent ` -. x = y ` to hold, ` x `
     and ` y ` must have different values and thus cannot be the same
     object-language variable.  Similarly, ` x ` and ` z ` cannot be the same
     object-language variable.  Therefore, ` x ` will not occur in the wff
     ` y = z ` when the first two antecedents hold, so analogous to ~ ax-17 ,
     the conclusion ` ( y = z -> A. x y = z ) ` follows.

     The original version of this axiom was ~ ax-12o and was replaced with this
     shorter ~ ax-12 in December 2015.  The old axiom is proved from this one
     as theorem ~ ax12o .  Conversely, this axiom is proved from ~ ax-12o as
     theorem ~ ax12 .

     The primary purpose of this axiom is to provide a way to introduce the
     quantifier ` A. x ` on ` y = z ` even when ` x ` and ` y ` are substituted
     with the same variable.  In this case, the first antecedent becomes
     ` -. x = x ` and the axiom still holds.

     Although this version is shorter, the original version ~ ax12o may be more
     practical to work with because of the "distinctor" form of its
     antecedents.  A typical application of ~ ax12o is in ~ dvelimh which
     converts a distinct variable pair to the distinctor antecendent
     ` -. A. x x = y ` .

     This axiom can be weakened if desired by adding distinct variable
     restrictions on pairs ` x , z ` and ` y , z ` .  To show that, we add
     these restrictions to theorem ~ ax12v and use only ~ ax12v for further
     derivations.  Thus, ~ ax12v should be the only theorem referencing this
     axiom.  Other theorems can reference either ~ ax12v or ~ ax12o .

     This axiom scheme is logically redundant (see ~ ax12w ) but is used as an
     auxiliary axiom to achieve metalogical completeness.  (Contributed by NM,
     21-Dec-2015.)  (New usage is discouraged.) $)

${
	$v x y z  $.
	f0_ax-12 $f set x $.
	f1_ax-12 $f set y $.
	f2_ax-12 $f set z $.
	a_ax-12 $a |- ( -. x = y -> ( y = z -> A. x y = z ) ) $.
$}

$(A weaker version of ~ ax-12 with distinct variable restrictions on pairs
       ` x , z ` and ` y , z ` .  In order to show that this weakening is
       adequate, this should be the only theorem referencing ~ ax-12 directly.
       (Contributed by NM, 30-Jun-2016.) $)

${
	$v x y z  $.
	$d x z  $.
	$d y z  $.
	f0_ax12v $f set x $.
	f1_ax12v $f set y $.
	f2_ax12v $f set z $.
	p_ax12v $p |- ( -. x = y -> ( y = z -> A. x y = z ) ) $= f0_ax12v f1_ax12v f2_ax12v a_ax-12 $.
$}

$(Lemma for ~ ax12o .  Similar to ~ equvin but with a negated equality.
       (Contributed by NM, 24-Dec-2015.) $)

${
	$v y z w  $.
	$d w y  $.
	$d w z  $.
	f0_ax12olem1 $f set y $.
	f1_ax12olem1 $f set z $.
	f2_ax12olem1 $f set w $.
	p_ax12olem1 $p |- ( E. w ( y = w /\ -. z = w ) <-> -. y = z ) $= f0_ax12olem1 f2_ax12olem1 f1_ax12olem1 a_ax-8 f2_ax12olem1 f1_ax12olem1 p_equcomi f0_ax12olem1 a_sup_set_class f2_ax12olem1 a_sup_set_class a_wceq f0_ax12olem1 a_sup_set_class f1_ax12olem1 a_sup_set_class a_wceq f2_ax12olem1 a_sup_set_class f1_ax12olem1 a_sup_set_class a_wceq f1_ax12olem1 a_sup_set_class f2_ax12olem1 a_sup_set_class a_wceq p_syl6 f0_ax12olem1 a_sup_set_class f2_ax12olem1 a_sup_set_class a_wceq f0_ax12olem1 a_sup_set_class f1_ax12olem1 a_sup_set_class a_wceq f1_ax12olem1 a_sup_set_class f2_ax12olem1 a_sup_set_class a_wceq p_con3and f0_ax12olem1 a_sup_set_class f2_ax12olem1 a_sup_set_class a_wceq f1_ax12olem1 a_sup_set_class f2_ax12olem1 a_sup_set_class a_wceq a_wn a_wa f0_ax12olem1 a_sup_set_class f1_ax12olem1 a_sup_set_class a_wceq a_wn f2_ax12olem1 p_exlimiv f0_ax12olem1 a_sup_set_class f1_ax12olem1 a_sup_set_class a_wceq a_wn f2_ax12olem1 a_ax-17 f2_ax12olem1 f1_ax12olem1 f0_ax12olem1 a_ax-8 f1_ax12olem1 f0_ax12olem1 p_equcomi f2_ax12olem1 a_sup_set_class f1_ax12olem1 a_sup_set_class a_wceq f2_ax12olem1 a_sup_set_class f0_ax12olem1 a_sup_set_class a_wceq f1_ax12olem1 a_sup_set_class f0_ax12olem1 a_sup_set_class a_wceq f0_ax12olem1 a_sup_set_class f1_ax12olem1 a_sup_set_class a_wceq p_syl6 f2_ax12olem1 a_sup_set_class f0_ax12olem1 a_sup_set_class a_wceq f0_ax12olem1 a_sup_set_class f1_ax12olem1 a_sup_set_class a_wceq a_wi f2_ax12olem1 f1_ax12olem1 p_equcoms f1_ax12olem1 a_sup_set_class f2_ax12olem1 a_sup_set_class a_wceq f2_ax12olem1 a_sup_set_class f0_ax12olem1 a_sup_set_class a_wceq f0_ax12olem1 a_sup_set_class f1_ax12olem1 a_sup_set_class a_wceq p_com12 f2_ax12olem1 a_sup_set_class f0_ax12olem1 a_sup_set_class a_wceq f1_ax12olem1 a_sup_set_class f2_ax12olem1 a_sup_set_class a_wceq f0_ax12olem1 a_sup_set_class f1_ax12olem1 a_sup_set_class a_wceq p_con3d f2_ax12olem1 f0_ax12olem1 p_equcomi f2_ax12olem1 a_sup_set_class f0_ax12olem1 a_sup_set_class a_wceq f0_ax12olem1 a_sup_set_class f1_ax12olem1 a_sup_set_class a_wceq a_wn f1_ax12olem1 a_sup_set_class f2_ax12olem1 a_sup_set_class a_wceq a_wn f0_ax12olem1 a_sup_set_class f2_ax12olem1 a_sup_set_class a_wceq p_jctild f0_ax12olem1 a_sup_set_class f1_ax12olem1 a_sup_set_class a_wceq a_wn f0_ax12olem1 a_sup_set_class f2_ax12olem1 a_sup_set_class a_wceq f1_ax12olem1 a_sup_set_class f2_ax12olem1 a_sup_set_class a_wceq a_wn a_wa f2_ax12olem1 f0_ax12olem1 p_spimeh f0_ax12olem1 a_sup_set_class f2_ax12olem1 a_sup_set_class a_wceq f1_ax12olem1 a_sup_set_class f2_ax12olem1 a_sup_set_class a_wceq a_wn a_wa f2_ax12olem1 a_wex f0_ax12olem1 a_sup_set_class f1_ax12olem1 a_sup_set_class a_wceq a_wn p_impbii $.
$}

$(Lemma for ~ ax12o .  Negate the equalities in ~ ax-12 , shown as the
       hypothesis.  (Contributed by NM, 24-Dec-2015.) $)

${
	$v x y z w  $.
	$d w x z  $.
	$d w y  $.
	f0_ax12olem2 $f set x $.
	f1_ax12olem2 $f set y $.
	f2_ax12olem2 $f set z $.
	f3_ax12olem2 $f set w $.
	e0_ax12olem2 $e |- ( -. x = y -> ( y = w -> A. x y = w ) ) $.
	p_ax12olem2 $p |- ( -. x = y -> ( -. y = z -> A. x -. y = z ) ) $= e0_ax12olem2 f0_ax12olem2 a_sup_set_class f1_ax12olem2 a_sup_set_class a_wceq a_wn f1_ax12olem2 a_sup_set_class f3_ax12olem2 a_sup_set_class a_wceq f1_ax12olem2 a_sup_set_class f3_ax12olem2 a_sup_set_class a_wceq f0_ax12olem2 a_wal f2_ax12olem2 a_sup_set_class f3_ax12olem2 a_sup_set_class a_wceq a_wn p_anim1d f2_ax12olem2 a_sup_set_class f3_ax12olem2 a_sup_set_class a_wceq a_wn f0_ax12olem2 a_ax-17 f2_ax12olem2 a_sup_set_class f3_ax12olem2 a_sup_set_class a_wceq a_wn f2_ax12olem2 a_sup_set_class f3_ax12olem2 a_sup_set_class a_wceq a_wn f0_ax12olem2 a_wal f1_ax12olem2 a_sup_set_class f3_ax12olem2 a_sup_set_class a_wceq f0_ax12olem2 a_wal p_anim2i f1_ax12olem2 a_sup_set_class f3_ax12olem2 a_sup_set_class a_wceq f2_ax12olem2 a_sup_set_class f3_ax12olem2 a_sup_set_class a_wceq a_wn f0_ax12olem2 p_19.26 f1_ax12olem2 a_sup_set_class f3_ax12olem2 a_sup_set_class a_wceq f0_ax12olem2 a_wal f2_ax12olem2 a_sup_set_class f3_ax12olem2 a_sup_set_class a_wceq a_wn a_wa f1_ax12olem2 a_sup_set_class f3_ax12olem2 a_sup_set_class a_wceq f0_ax12olem2 a_wal f2_ax12olem2 a_sup_set_class f3_ax12olem2 a_sup_set_class a_wceq a_wn f0_ax12olem2 a_wal a_wa f1_ax12olem2 a_sup_set_class f3_ax12olem2 a_sup_set_class a_wceq f2_ax12olem2 a_sup_set_class f3_ax12olem2 a_sup_set_class a_wceq a_wn a_wa f0_ax12olem2 a_wal p_sylibr f0_ax12olem2 a_sup_set_class f1_ax12olem2 a_sup_set_class a_wceq a_wn f1_ax12olem2 a_sup_set_class f3_ax12olem2 a_sup_set_class a_wceq f2_ax12olem2 a_sup_set_class f3_ax12olem2 a_sup_set_class a_wceq a_wn a_wa f1_ax12olem2 a_sup_set_class f3_ax12olem2 a_sup_set_class a_wceq f0_ax12olem2 a_wal f2_ax12olem2 a_sup_set_class f3_ax12olem2 a_sup_set_class a_wceq a_wn a_wa f1_ax12olem2 a_sup_set_class f3_ax12olem2 a_sup_set_class a_wceq f2_ax12olem2 a_sup_set_class f3_ax12olem2 a_sup_set_class a_wceq a_wn a_wa f0_ax12olem2 a_wal p_syl6 f0_ax12olem2 a_sup_set_class f1_ax12olem2 a_sup_set_class a_wceq a_wn f1_ax12olem2 a_sup_set_class f3_ax12olem2 a_sup_set_class a_wceq f2_ax12olem2 a_sup_set_class f3_ax12olem2 a_sup_set_class a_wceq a_wn a_wa f1_ax12olem2 a_sup_set_class f3_ax12olem2 a_sup_set_class a_wceq f2_ax12olem2 a_sup_set_class f3_ax12olem2 a_sup_set_class a_wceq a_wn a_wa f0_ax12olem2 a_wal f3_ax12olem2 p_eximdv f1_ax12olem2 a_sup_set_class f3_ax12olem2 a_sup_set_class a_wceq f2_ax12olem2 a_sup_set_class f3_ax12olem2 a_sup_set_class a_wceq a_wn a_wa f3_ax12olem2 f0_ax12olem2 p_19.12 f0_ax12olem2 a_sup_set_class f1_ax12olem2 a_sup_set_class a_wceq a_wn f1_ax12olem2 a_sup_set_class f3_ax12olem2 a_sup_set_class a_wceq f2_ax12olem2 a_sup_set_class f3_ax12olem2 a_sup_set_class a_wceq a_wn a_wa f3_ax12olem2 a_wex f1_ax12olem2 a_sup_set_class f3_ax12olem2 a_sup_set_class a_wceq f2_ax12olem2 a_sup_set_class f3_ax12olem2 a_sup_set_class a_wceq a_wn a_wa f0_ax12olem2 a_wal f3_ax12olem2 a_wex f1_ax12olem2 a_sup_set_class f3_ax12olem2 a_sup_set_class a_wceq f2_ax12olem2 a_sup_set_class f3_ax12olem2 a_sup_set_class a_wceq a_wn a_wa f3_ax12olem2 a_wex f0_ax12olem2 a_wal p_syl6 f1_ax12olem2 f2_ax12olem2 f3_ax12olem2 p_ax12olem1 f1_ax12olem2 f2_ax12olem2 f3_ax12olem2 p_ax12olem1 f1_ax12olem2 a_sup_set_class f3_ax12olem2 a_sup_set_class a_wceq f2_ax12olem2 a_sup_set_class f3_ax12olem2 a_sup_set_class a_wceq a_wn a_wa f3_ax12olem2 a_wex f1_ax12olem2 a_sup_set_class f2_ax12olem2 a_sup_set_class a_wceq a_wn f0_ax12olem2 p_albii f0_ax12olem2 a_sup_set_class f1_ax12olem2 a_sup_set_class a_wceq a_wn f1_ax12olem2 a_sup_set_class f3_ax12olem2 a_sup_set_class a_wceq f2_ax12olem2 a_sup_set_class f3_ax12olem2 a_sup_set_class a_wceq a_wn a_wa f3_ax12olem2 a_wex f1_ax12olem2 a_sup_set_class f3_ax12olem2 a_sup_set_class a_wceq f2_ax12olem2 a_sup_set_class f3_ax12olem2 a_sup_set_class a_wceq a_wn a_wa f3_ax12olem2 a_wex f0_ax12olem2 a_wal f1_ax12olem2 a_sup_set_class f2_ax12olem2 a_sup_set_class a_wceq a_wn f1_ax12olem2 a_sup_set_class f2_ax12olem2 a_sup_set_class a_wceq a_wn f0_ax12olem2 a_wal p_3imtr3g $.
$}

$(Lemma for ~ ax12o .  Show the equivalence of an intermediate equivalent to
     ~ ax12o with the conjunction of ~ ax-12 and a variant with negated
     equalities.  (Contributed by NM, 24-Dec-2015.) $)

${
	$v x y z  $.
	f0_ax12olem3 $f set x $.
	f1_ax12olem3 $f set y $.
	f2_ax12olem3 $f set z $.
	p_ax12olem3 $p |- ( ( -. x = y -> ( -. A. x -. y = z -> A. x y = z ) ) <-> ( ( -. x = y -> ( y = z -> A. x y = z ) ) /\ ( -. x = y -> ( -. y = z -> A. x -. y = z ) ) ) ) $= f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq a_wn f0_ax12olem3 p_sp f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq a_wn f0_ax12olem3 a_wal f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq p_con2i f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq a_wn f0_ax12olem3 a_wal a_wn f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq f0_ax12olem3 a_wal p_imim1i f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq a_wn f0_ax12olem3 a_wal a_wn f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq f0_ax12olem3 a_wal a_wi f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq f0_ax12olem3 a_wal a_wi f0_ax12olem3 a_sup_set_class f1_ax12olem3 a_sup_set_class a_wceq a_wn p_imim2i f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq f0_ax12olem3 p_sp f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq f0_ax12olem3 a_wal f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq a_wn f0_ax12olem3 a_wal a_wn p_imim2i f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq a_wn f0_ax12olem3 a_wal a_wn f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq f0_ax12olem3 a_wal a_wi f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq a_wn f0_ax12olem3 a_wal f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq p_con1d f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq a_wn f0_ax12olem3 a_wal a_wn f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq f0_ax12olem3 a_wal a_wi f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq a_wn f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq a_wn f0_ax12olem3 a_wal a_wi f0_ax12olem3 a_sup_set_class f1_ax12olem3 a_sup_set_class a_wceq a_wn p_imim2i f0_ax12olem3 a_sup_set_class f1_ax12olem3 a_sup_set_class a_wceq a_wn f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq a_wn f0_ax12olem3 a_wal a_wn f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq f0_ax12olem3 a_wal a_wi a_wi f0_ax12olem3 a_sup_set_class f1_ax12olem3 a_sup_set_class a_wceq a_wn f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq f0_ax12olem3 a_wal a_wi a_wi f0_ax12olem3 a_sup_set_class f1_ax12olem3 a_sup_set_class a_wceq a_wn f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq a_wn f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq a_wn f0_ax12olem3 a_wal a_wi a_wi p_jca f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq a_wn f0_ax12olem3 a_wal p_con1 f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq a_wn f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq a_wn f0_ax12olem3 a_wal a_wi f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq a_wn f0_ax12olem3 a_wal a_wn f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq f0_ax12olem3 a_wal p_imim1d f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq a_wn f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq a_wn f0_ax12olem3 a_wal a_wi f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq f0_ax12olem3 a_wal a_wi f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq a_wn f0_ax12olem3 a_wal a_wn f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq f0_ax12olem3 a_wal a_wi p_com12 f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq f0_ax12olem3 a_wal a_wi f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq a_wn f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq a_wn f0_ax12olem3 a_wal a_wi f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq a_wn f0_ax12olem3 a_wal a_wn f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq f0_ax12olem3 a_wal a_wi f0_ax12olem3 a_sup_set_class f1_ax12olem3 a_sup_set_class a_wceq a_wn p_imim3i f0_ax12olem3 a_sup_set_class f1_ax12olem3 a_sup_set_class a_wceq a_wn f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq f0_ax12olem3 a_wal a_wi a_wi f0_ax12olem3 a_sup_set_class f1_ax12olem3 a_sup_set_class a_wceq a_wn f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq a_wn f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq a_wn f0_ax12olem3 a_wal a_wi a_wi f0_ax12olem3 a_sup_set_class f1_ax12olem3 a_sup_set_class a_wceq a_wn f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq a_wn f0_ax12olem3 a_wal a_wn f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq f0_ax12olem3 a_wal a_wi a_wi p_imp f0_ax12olem3 a_sup_set_class f1_ax12olem3 a_sup_set_class a_wceq a_wn f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq a_wn f0_ax12olem3 a_wal a_wn f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq f0_ax12olem3 a_wal a_wi a_wi f0_ax12olem3 a_sup_set_class f1_ax12olem3 a_sup_set_class a_wceq a_wn f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq f0_ax12olem3 a_wal a_wi a_wi f0_ax12olem3 a_sup_set_class f1_ax12olem3 a_sup_set_class a_wceq a_wn f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq a_wn f1_ax12olem3 a_sup_set_class f2_ax12olem3 a_sup_set_class a_wceq a_wn f0_ax12olem3 a_wal a_wi a_wi a_wa p_impbii $.
$}

$(Lemma for ~ ax12o .  Construct an intermediate equivalent to ~ ax-12
       from two instances of ~ ax-12 .  (Contributed by NM, 24-Dec-2015.) $)

${
	$v x y z w  $.
	$d w x z  $.
	$d w y z  $.
	f0_ax12olem4 $f set x $.
	f1_ax12olem4 $f set y $.
	f2_ax12olem4 $f set z $.
	f3_ax12olem4 $f set w $.
	e0_ax12olem4 $e |- ( -. x = y -> ( y = z -> A. x y = z ) ) $.
	e1_ax12olem4 $e |- ( -. x = y -> ( y = w -> A. x y = w ) ) $.
	p_ax12olem4 $p |- ( -. x = y -> ( -. A. x -. y = z -> A. x y = z ) ) $= e0_ax12olem4 e1_ax12olem4 f0_ax12olem4 f1_ax12olem4 f2_ax12olem4 f3_ax12olem4 p_ax12olem2 f0_ax12olem4 f1_ax12olem4 f2_ax12olem4 p_ax12olem3 f0_ax12olem4 a_sup_set_class f1_ax12olem4 a_sup_set_class a_wceq a_wn f1_ax12olem4 a_sup_set_class f2_ax12olem4 a_sup_set_class a_wceq a_wn f0_ax12olem4 a_wal a_wn f1_ax12olem4 a_sup_set_class f2_ax12olem4 a_sup_set_class a_wceq f0_ax12olem4 a_wal a_wi a_wi f0_ax12olem4 a_sup_set_class f1_ax12olem4 a_sup_set_class a_wceq a_wn f1_ax12olem4 a_sup_set_class f2_ax12olem4 a_sup_set_class a_wceq f1_ax12olem4 a_sup_set_class f2_ax12olem4 a_sup_set_class a_wceq f0_ax12olem4 a_wal a_wi a_wi f0_ax12olem4 a_sup_set_class f1_ax12olem4 a_sup_set_class a_wceq a_wn f1_ax12olem4 a_sup_set_class f2_ax12olem4 a_sup_set_class a_wceq a_wn f1_ax12olem4 a_sup_set_class f2_ax12olem4 a_sup_set_class a_wceq a_wn f0_ax12olem4 a_wal a_wi a_wi p_mpbir2an $.
$}

$(Lemma for ~ ax12o .  See ~ ax12olem6 for derivation of ~ ax12o from the
       conclusion.  (Contributed by NM, 24-Dec-2015.) $)

${
	$v x y z  $.
	f0_ax12olem5 $f set x $.
	f1_ax12olem5 $f set y $.
	f2_ax12olem5 $f set z $.
	e0_ax12olem5 $e |- ( -. x = y -> ( -. A. x -. y = z -> A. x y = z ) ) $.
	p_ax12olem5 $p |- ( -. A. x x = y -> ( y = z -> A. x y = z ) ) $= f0_ax12olem5 a_sup_set_class f1_ax12olem5 a_sup_set_class a_wceq f0_ax12olem5 p_exnal f1_ax12olem5 a_sup_set_class f2_ax12olem5 a_sup_set_class a_wceq f0_ax12olem5 p_19.8a f1_ax12olem5 a_sup_set_class f2_ax12olem5 a_sup_set_class a_wceq f0_ax12olem5 p_hbe1 f1_ax12olem5 a_sup_set_class f2_ax12olem5 a_sup_set_class a_wceq f0_ax12olem5 p_hba1 f1_ax12olem5 a_sup_set_class f2_ax12olem5 a_sup_set_class a_wceq f0_ax12olem5 a_wex f1_ax12olem5 a_sup_set_class f2_ax12olem5 a_sup_set_class a_wceq f0_ax12olem5 a_wal f0_ax12olem5 p_hbim f1_ax12olem5 a_sup_set_class f2_ax12olem5 a_sup_set_class a_wceq f0_ax12olem5 a_df-ex e0_ax12olem5 f1_ax12olem5 a_sup_set_class f2_ax12olem5 a_sup_set_class a_wceq f0_ax12olem5 a_wex f1_ax12olem5 a_sup_set_class f2_ax12olem5 a_sup_set_class a_wceq a_wn f0_ax12olem5 a_wal a_wn f0_ax12olem5 a_sup_set_class f1_ax12olem5 a_sup_set_class a_wceq a_wn f1_ax12olem5 a_sup_set_class f2_ax12olem5 a_sup_set_class a_wceq f0_ax12olem5 a_wal p_syl5bi f0_ax12olem5 a_sup_set_class f1_ax12olem5 a_sup_set_class a_wceq a_wn f1_ax12olem5 a_sup_set_class f2_ax12olem5 a_sup_set_class a_wceq f0_ax12olem5 a_wex f1_ax12olem5 a_sup_set_class f2_ax12olem5 a_sup_set_class a_wceq f0_ax12olem5 a_wal a_wi f0_ax12olem5 p_exlimih f1_ax12olem5 a_sup_set_class f2_ax12olem5 a_sup_set_class a_wceq f1_ax12olem5 a_sup_set_class f2_ax12olem5 a_sup_set_class a_wceq f0_ax12olem5 a_wex f0_ax12olem5 a_sup_set_class f1_ax12olem5 a_sup_set_class a_wceq a_wn f0_ax12olem5 a_wex f1_ax12olem5 a_sup_set_class f2_ax12olem5 a_sup_set_class a_wceq f0_ax12olem5 a_wal p_syl5 f0_ax12olem5 a_sup_set_class f1_ax12olem5 a_sup_set_class a_wceq f0_ax12olem5 a_wal a_wn f0_ax12olem5 a_sup_set_class f1_ax12olem5 a_sup_set_class a_wceq a_wn f0_ax12olem5 a_wex f1_ax12olem5 a_sup_set_class f2_ax12olem5 a_sup_set_class a_wceq f1_ax12olem5 a_sup_set_class f2_ax12olem5 a_sup_set_class a_wceq f0_ax12olem5 a_wal a_wi p_sylbir $.
$}

$(Lemma for ~ ax12o .  Derivation of ~ ax12o from the hypotheses, without
       using ~ ax12o .  (Contributed by Andrew Salmon, 21-Jul-2011.)  (Revised
       by NM, 24-Dec-2015.) $)

${
	$v x y z w  $.
	$d w x  $.
	$d w y  $.
	$d w z  $.
	f0_ax12olem6 $f set x $.
	f1_ax12olem6 $f set y $.
	f2_ax12olem6 $f set z $.
	f3_ax12olem6 $f set w $.
	e0_ax12olem6 $e |- ( -. A. x x = z -> ( z = w -> A. x z = w ) ) $.
	e1_ax12olem6 $e |- ( -. A. x x = y -> ( y = w -> A. x y = w ) ) $.
	p_ax12olem6 $p |- ( -. A. x x = y -> ( -. A. x x = z -> ( y = z -> A. x y = z ) ) ) $= f0_ax12olem6 a_sup_set_class f2_ax12olem6 a_sup_set_class a_wceq f0_ax12olem6 p_hbn1 e0_ax12olem6 f0_ax12olem6 a_sup_set_class f2_ax12olem6 a_sup_set_class a_wceq f0_ax12olem6 a_wal a_wn f2_ax12olem6 a_sup_set_class f3_ax12olem6 a_sup_set_class a_wceq f0_ax12olem6 p_hbim1 f0_ax12olem6 a_sup_set_class f2_ax12olem6 a_sup_set_class a_wceq f0_ax12olem6 a_wal a_wn f1_ax12olem6 a_sup_set_class f2_ax12olem6 a_sup_set_class a_wceq a_wi f3_ax12olem6 a_ax-17 f2_ax12olem6 f3_ax12olem6 p_equcom f3_ax12olem6 f1_ax12olem6 f2_ax12olem6 p_equequ1 f2_ax12olem6 a_sup_set_class f3_ax12olem6 a_sup_set_class a_wceq f3_ax12olem6 a_sup_set_class f2_ax12olem6 a_sup_set_class a_wceq f3_ax12olem6 a_sup_set_class f1_ax12olem6 a_sup_set_class a_wceq f1_ax12olem6 a_sup_set_class f2_ax12olem6 a_sup_set_class a_wceq p_syl5bb f3_ax12olem6 a_sup_set_class f1_ax12olem6 a_sup_set_class a_wceq f2_ax12olem6 a_sup_set_class f3_ax12olem6 a_sup_set_class a_wceq f1_ax12olem6 a_sup_set_class f2_ax12olem6 a_sup_set_class a_wceq f0_ax12olem6 a_sup_set_class f2_ax12olem6 a_sup_set_class a_wceq f0_ax12olem6 a_wal a_wn p_imbi2d e1_ax12olem6 f0_ax12olem6 a_sup_set_class f2_ax12olem6 a_sup_set_class a_wceq f0_ax12olem6 a_wal a_wn f2_ax12olem6 a_sup_set_class f3_ax12olem6 a_sup_set_class a_wceq a_wi f0_ax12olem6 a_sup_set_class f2_ax12olem6 a_sup_set_class a_wceq f0_ax12olem6 a_wal a_wn f1_ax12olem6 a_sup_set_class f2_ax12olem6 a_sup_set_class a_wceq a_wi f0_ax12olem6 f1_ax12olem6 f3_ax12olem6 p_dvelimhw f0_ax12olem6 a_sup_set_class f2_ax12olem6 a_sup_set_class a_wceq f0_ax12olem6 p_hbn1 f0_ax12olem6 a_sup_set_class f2_ax12olem6 a_sup_set_class a_wceq f0_ax12olem6 a_wal a_wn f1_ax12olem6 a_sup_set_class f2_ax12olem6 a_sup_set_class a_wceq f0_ax12olem6 p_19.21h f0_ax12olem6 a_sup_set_class f1_ax12olem6 a_sup_set_class a_wceq f0_ax12olem6 a_wal a_wn f0_ax12olem6 a_sup_set_class f2_ax12olem6 a_sup_set_class a_wceq f0_ax12olem6 a_wal a_wn f1_ax12olem6 a_sup_set_class f2_ax12olem6 a_sup_set_class a_wceq a_wi f0_ax12olem6 a_sup_set_class f2_ax12olem6 a_sup_set_class a_wceq f0_ax12olem6 a_wal a_wn f1_ax12olem6 a_sup_set_class f2_ax12olem6 a_sup_set_class a_wceq a_wi f0_ax12olem6 a_wal f0_ax12olem6 a_sup_set_class f2_ax12olem6 a_sup_set_class a_wceq f0_ax12olem6 a_wal a_wn f1_ax12olem6 a_sup_set_class f2_ax12olem6 a_sup_set_class a_wceq f0_ax12olem6 a_wal a_wi p_syl6ib f0_ax12olem6 a_sup_set_class f1_ax12olem6 a_sup_set_class a_wceq f0_ax12olem6 a_wal a_wn f0_ax12olem6 a_sup_set_class f2_ax12olem6 a_sup_set_class a_wceq f0_ax12olem6 a_wal a_wn f1_ax12olem6 a_sup_set_class f2_ax12olem6 a_sup_set_class a_wceq f1_ax12olem6 a_sup_set_class f2_ax12olem6 a_sup_set_class a_wceq f0_ax12olem6 a_wal p_pm2.86d $.
$}

$(Lemma for ~ ax12o .  Derivation of ~ ax12o from the hypotheses, without
       using ~ ax12o .  (Contributed by NM, 24-Dec-2015.) $)

${
	$v x y z w  $.
	$d w x  $.
	$d w y  $.
	$d w z  $.
	f0_ax12olem7 $f set x $.
	f1_ax12olem7 $f set y $.
	f2_ax12olem7 $f set z $.
	f3_ax12olem7 $f set w $.
	e0_ax12olem7 $e |- ( -. x = z -> ( -. A. x -. z = w -> A. x z = w ) ) $.
	e1_ax12olem7 $e |- ( -. x = y -> ( -. A. x -. y = w -> A. x y = w ) ) $.
	p_ax12olem7 $p |- ( -. A. x x = y -> ( -. A. x x = z -> ( y = z -> A. x y = z ) ) ) $= e0_ax12olem7 f0_ax12olem7 f2_ax12olem7 f3_ax12olem7 p_ax12olem5 e1_ax12olem7 f0_ax12olem7 f1_ax12olem7 f3_ax12olem7 p_ax12olem5 f0_ax12olem7 f1_ax12olem7 f2_ax12olem7 f3_ax12olem7 p_ax12olem6 $.
$}

$(Derive set.mm's original ~ ax-12o from the shorter ~ ax-12 .
       (Contributed by NM, 29-Nov-2015.)  (Revised by NM, 24-Dec-2015.) $)

${
	$v x y z  $.
	$d x w v  $.
	$d y w v  $.
	$d z w v  $.
	f0_ax12o $f set x $.
	f1_ax12o $f set y $.
	f2_ax12o $f set z $.
	i0_ax12o $f set w $.
	i1_ax12o $f set v $.
	p_ax12o $p |- ( -. A. z z = x -> ( -. A. z z = y -> ( x = y -> A. z x = y ) ) ) $= f2_ax12o f1_ax12o i0_ax12o p_ax12v f2_ax12o f1_ax12o i1_ax12o p_ax12v f2_ax12o f1_ax12o i0_ax12o i1_ax12o p_ax12olem4 f2_ax12o f0_ax12o i0_ax12o p_ax12v f2_ax12o f0_ax12o i1_ax12o p_ax12v f2_ax12o f0_ax12o i0_ax12o i1_ax12o p_ax12olem4 f2_ax12o f0_ax12o f1_ax12o i0_ax12o p_ax12olem7 $.
$}

$(Lemma for ~ ax10 .  Change bound variable.  (Contributed by NM,
       22-Jul-2015.) $)

${
	$v x y w  $.
	$d x v w  $.
	$d y v w  $.
	f0_ax10lem1 $f set x $.
	f1_ax10lem1 $f set y $.
	f2_ax10lem1 $f set w $.
	i0_ax10lem1 $f set v $.
	p_ax10lem1 $p |- ( A. x x = w -> A. y y = w ) $= f0_ax10lem1 i0_ax10lem1 f2_ax10lem1 a_ax-8 f0_ax10lem1 a_sup_set_class f2_ax10lem1 a_sup_set_class a_wceq i0_ax10lem1 a_sup_set_class f2_ax10lem1 a_sup_set_class a_wceq f0_ax10lem1 i0_ax10lem1 p_cbvalivw i0_ax10lem1 f1_ax10lem1 f2_ax10lem1 a_ax-8 i0_ax10lem1 a_sup_set_class f2_ax10lem1 a_sup_set_class a_wceq f1_ax10lem1 a_sup_set_class f2_ax10lem1 a_sup_set_class a_wceq i0_ax10lem1 f1_ax10lem1 p_cbvalivw f0_ax10lem1 a_sup_set_class f2_ax10lem1 a_sup_set_class a_wceq f0_ax10lem1 a_wal i0_ax10lem1 a_sup_set_class f2_ax10lem1 a_sup_set_class a_wceq i0_ax10lem1 a_wal f1_ax10lem1 a_sup_set_class f2_ax10lem1 a_sup_set_class a_wceq f1_ax10lem1 a_wal p_syl $.
$}

$(Lemma for ~ ax10 .  Change free variable.  (Contributed by NM,
       25-Jul-2015.) $)

${
	$v x y z  $.
	$d x y  $.
	$d x z  $.
	f0_ax10lem2 $f set x $.
	f1_ax10lem2 $f set y $.
	f2_ax10lem2 $f set z $.
	p_ax10lem2 $p |- ( A. x x = y -> A. x x = z ) $= f0_ax10lem2 a_sup_set_class f1_ax10lem2 a_sup_set_class a_wceq a_wn f0_ax10lem2 p_hbe1 f2_ax10lem2 f1_ax10lem2 f0_ax10lem2 p_equequ2 f2_ax10lem2 a_sup_set_class f1_ax10lem2 a_sup_set_class a_wceq f0_ax10lem2 a_sup_set_class f2_ax10lem2 a_sup_set_class a_wceq f0_ax10lem2 a_sup_set_class f1_ax10lem2 a_sup_set_class a_wceq p_biimprd f2_ax10lem2 a_sup_set_class f1_ax10lem2 a_sup_set_class a_wceq f0_ax10lem2 a_sup_set_class f1_ax10lem2 a_sup_set_class a_wceq f0_ax10lem2 a_sup_set_class f2_ax10lem2 a_sup_set_class a_wceq p_con3rr3 f0_ax10lem2 a_sup_set_class f1_ax10lem2 a_sup_set_class a_wceq a_wn f0_ax10lem2 p_19.8a f0_ax10lem2 a_sup_set_class f2_ax10lem2 a_sup_set_class a_wceq a_wn f2_ax10lem2 a_sup_set_class f1_ax10lem2 a_sup_set_class a_wceq f0_ax10lem2 a_sup_set_class f1_ax10lem2 a_sup_set_class a_wceq a_wn f0_ax10lem2 a_sup_set_class f1_ax10lem2 a_sup_set_class a_wceq a_wn f0_ax10lem2 a_wex p_syl6 f2_ax10lem2 a_sup_set_class f1_ax10lem2 a_sup_set_class a_wceq a_wn f0_ax10lem2 a_ax-17 f0_ax10lem2 f2_ax10lem2 f1_ax10lem2 p_equequ1 f0_ax10lem2 a_sup_set_class f2_ax10lem2 a_sup_set_class a_wceq f0_ax10lem2 a_sup_set_class f1_ax10lem2 a_sup_set_class a_wceq f2_ax10lem2 a_sup_set_class f1_ax10lem2 a_sup_set_class a_wceq p_notbid f0_ax10lem2 a_sup_set_class f2_ax10lem2 a_sup_set_class a_wceq f0_ax10lem2 a_sup_set_class f1_ax10lem2 a_sup_set_class a_wceq a_wn f2_ax10lem2 a_sup_set_class f1_ax10lem2 a_sup_set_class a_wceq a_wn p_biimprd f2_ax10lem2 a_sup_set_class f1_ax10lem2 a_sup_set_class a_wceq a_wn f0_ax10lem2 a_sup_set_class f1_ax10lem2 a_sup_set_class a_wceq a_wn f0_ax10lem2 f2_ax10lem2 p_spimeh f0_ax10lem2 a_sup_set_class f2_ax10lem2 a_sup_set_class a_wceq a_wn f2_ax10lem2 a_sup_set_class f1_ax10lem2 a_sup_set_class a_wceq f0_ax10lem2 a_sup_set_class f1_ax10lem2 a_sup_set_class a_wceq a_wn f0_ax10lem2 a_wex p_pm2.61d1 f0_ax10lem2 a_sup_set_class f2_ax10lem2 a_sup_set_class a_wceq a_wn f0_ax10lem2 a_sup_set_class f1_ax10lem2 a_sup_set_class a_wceq a_wn f0_ax10lem2 a_wex f0_ax10lem2 p_exlimih f0_ax10lem2 a_sup_set_class f2_ax10lem2 a_sup_set_class a_wceq f0_ax10lem2 p_exnal f0_ax10lem2 a_sup_set_class f1_ax10lem2 a_sup_set_class a_wceq f0_ax10lem2 p_exnal f0_ax10lem2 a_sup_set_class f2_ax10lem2 a_sup_set_class a_wceq a_wn f0_ax10lem2 a_wex f0_ax10lem2 a_sup_set_class f1_ax10lem2 a_sup_set_class a_wceq a_wn f0_ax10lem2 a_wex f0_ax10lem2 a_sup_set_class f2_ax10lem2 a_sup_set_class a_wceq f0_ax10lem2 a_wal a_wn f0_ax10lem2 a_sup_set_class f1_ax10lem2 a_sup_set_class a_wceq f0_ax10lem2 a_wal a_wn p_3imtr3i f0_ax10lem2 a_sup_set_class f2_ax10lem2 a_sup_set_class a_wceq f0_ax10lem2 a_wal f0_ax10lem2 a_sup_set_class f1_ax10lem2 a_sup_set_class a_wceq f0_ax10lem2 a_wal p_con4i $.
$}

$(Lemma for ~ ax10 .  Similar to ~ ax-10 but with distinct variables.
       (Contributed by NM, 25-Jul-2015.) $)

${
	$v x y  $.
	$d w x y  $.
	$d w x z  $.
	f0_ax10lem3 $f set x $.
	f1_ax10lem3 $f set y $.
	i0_ax10lem3 $f set z $.
	i1_ax10lem3 $f set w $.
	p_ax10lem3 $p |- ( A. x x = y -> A. y y = x ) $= f0_ax10lem3 f1_ax10lem3 i0_ax10lem3 p_ax10lem2 f0_ax10lem3 i1_ax10lem3 i0_ax10lem3 p_ax10lem1 i1_ax10lem3 i0_ax10lem3 f0_ax10lem3 p_ax10lem2 f0_ax10lem3 a_sup_set_class i0_ax10lem3 a_sup_set_class a_wceq f0_ax10lem3 a_wal i1_ax10lem3 a_sup_set_class i0_ax10lem3 a_sup_set_class a_wceq i1_ax10lem3 a_wal i1_ax10lem3 a_sup_set_class f0_ax10lem3 a_sup_set_class a_wceq i1_ax10lem3 a_wal p_syl i1_ax10lem3 f1_ax10lem3 f0_ax10lem3 p_ax10lem1 f0_ax10lem3 a_sup_set_class i0_ax10lem3 a_sup_set_class a_wceq f0_ax10lem3 a_wal i1_ax10lem3 a_sup_set_class f0_ax10lem3 a_sup_set_class a_wceq i1_ax10lem3 a_wal f1_ax10lem3 a_sup_set_class f0_ax10lem3 a_sup_set_class a_wceq f1_ax10lem3 a_wal p_syl f0_ax10lem3 a_sup_set_class f1_ax10lem3 a_sup_set_class a_wceq f0_ax10lem3 a_wal f0_ax10lem3 a_sup_set_class i0_ax10lem3 a_sup_set_class a_wceq f0_ax10lem3 a_wal f1_ax10lem3 a_sup_set_class f0_ax10lem3 a_sup_set_class a_wceq f1_ax10lem3 a_wal p_syl $.
$}

$(Similar to ~ dvelim with first hypothesis replaced by distinct variable
       condition.  (Contributed by NM, 25-Jul-2015.) $)

${
	$v ph ps x y z  $.
	$d x z  $.
	$d y z  $.
	$d z ps  $.
	$d x ph  $.
	f0_dvelimv $f wff ph $.
	f1_dvelimv $f wff ps $.
	f2_dvelimv $f set x $.
	f3_dvelimv $f set y $.
	f4_dvelimv $f set z $.
	e0_dvelimv $e |- ( z = y -> ( ph <-> ps ) ) $.
	p_dvelimv $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $= f1_dvelimv f4_dvelimv a_ax-17 f1_dvelimv f4_dvelimv a_ax-17 f1_dvelimv f1_dvelimv f4_dvelimv a_wal f4_dvelimv a_sup_set_class f3_dvelimv a_sup_set_class a_wceq p_a1d f1_dvelimv f4_dvelimv a_sup_set_class f3_dvelimv a_sup_set_class a_wceq f1_dvelimv f4_dvelimv a_wal a_wi f4_dvelimv p_alrimih f1_dvelimv f4_dvelimv p_sp e0_dvelimv f1_dvelimv f4_dvelimv a_wal f0_dvelimv f4_dvelimv a_sup_set_class f3_dvelimv a_sup_set_class a_wceq f1_dvelimv p_syl5ibr f4_dvelimv a_sup_set_class f3_dvelimv a_sup_set_class a_wceq f1_dvelimv f4_dvelimv a_wal f0_dvelimv p_a2i f4_dvelimv a_sup_set_class f3_dvelimv a_sup_set_class a_wceq f1_dvelimv f4_dvelimv a_wal a_wi f4_dvelimv a_sup_set_class f3_dvelimv a_sup_set_class a_wceq f0_dvelimv a_wi f4_dvelimv p_alimi f1_dvelimv f4_dvelimv a_sup_set_class f3_dvelimv a_sup_set_class a_wceq f1_dvelimv f4_dvelimv a_wal a_wi f4_dvelimv a_wal f4_dvelimv a_sup_set_class f3_dvelimv a_sup_set_class a_wceq f0_dvelimv a_wi f4_dvelimv a_wal p_syl f4_dvelimv f2_dvelimv p_ax10lem3 f4_dvelimv a_sup_set_class f2_dvelimv a_sup_set_class a_wceq f4_dvelimv a_wal f2_dvelimv a_sup_set_class f4_dvelimv a_sup_set_class a_wceq f2_dvelimv a_wal p_con3i f4_dvelimv a_sup_set_class f2_dvelimv a_sup_set_class a_wceq f4_dvelimv p_hbn1 f2_dvelimv f4_dvelimv p_ax10lem3 f2_dvelimv a_sup_set_class f4_dvelimv a_sup_set_class a_wceq f2_dvelimv a_wal f4_dvelimv a_sup_set_class f2_dvelimv a_sup_set_class a_wceq f4_dvelimv a_wal p_con3i f4_dvelimv a_sup_set_class f2_dvelimv a_sup_set_class a_wceq f4_dvelimv a_wal a_wn f2_dvelimv a_sup_set_class f4_dvelimv a_sup_set_class a_wceq f2_dvelimv a_wal a_wn f4_dvelimv p_alrimih f2_dvelimv a_sup_set_class f4_dvelimv a_sup_set_class a_wceq f2_dvelimv a_wal a_wn f4_dvelimv a_sup_set_class f2_dvelimv a_sup_set_class a_wceq f4_dvelimv a_wal a_wn f2_dvelimv a_sup_set_class f4_dvelimv a_sup_set_class a_wceq f2_dvelimv a_wal a_wn f4_dvelimv a_wal p_syl f2_dvelimv a_sup_set_class f3_dvelimv a_sup_set_class a_wceq f2_dvelimv a_wal a_wn f4_dvelimv a_ax-17 f2_dvelimv a_sup_set_class f4_dvelimv a_sup_set_class a_wceq f2_dvelimv a_wal a_wn f2_dvelimv a_sup_set_class f3_dvelimv a_sup_set_class a_wceq f2_dvelimv a_wal a_wn f4_dvelimv p_hban f2_dvelimv a_sup_set_class f4_dvelimv a_sup_set_class a_wceq f2_dvelimv p_hbn1 f2_dvelimv a_sup_set_class f3_dvelimv a_sup_set_class a_wceq f2_dvelimv p_hbn1 f2_dvelimv a_sup_set_class f4_dvelimv a_sup_set_class a_wceq f2_dvelimv a_wal a_wn f2_dvelimv a_sup_set_class f3_dvelimv a_sup_set_class a_wceq f2_dvelimv a_wal a_wn f2_dvelimv p_hban f4_dvelimv f3_dvelimv f2_dvelimv p_ax12o f2_dvelimv a_sup_set_class f4_dvelimv a_sup_set_class a_wceq f2_dvelimv a_wal a_wn f2_dvelimv a_sup_set_class f3_dvelimv a_sup_set_class a_wceq f2_dvelimv a_wal a_wn f4_dvelimv a_sup_set_class f3_dvelimv a_sup_set_class a_wceq f4_dvelimv a_sup_set_class f3_dvelimv a_sup_set_class a_wceq f2_dvelimv a_wal a_wi p_imp f2_dvelimv a_sup_set_class f4_dvelimv a_sup_set_class a_wceq f2_dvelimv a_wal a_wn f2_dvelimv a_sup_set_class f3_dvelimv a_sup_set_class a_wceq f2_dvelimv a_wal a_wn a_wa f0_dvelimv f2_dvelimv p_a17d f2_dvelimv a_sup_set_class f4_dvelimv a_sup_set_class a_wceq f2_dvelimv a_wal a_wn f2_dvelimv a_sup_set_class f3_dvelimv a_sup_set_class a_wceq f2_dvelimv a_wal a_wn a_wa f4_dvelimv a_sup_set_class f3_dvelimv a_sup_set_class a_wceq f0_dvelimv f2_dvelimv p_hbimd f2_dvelimv a_sup_set_class f4_dvelimv a_sup_set_class a_wceq f2_dvelimv a_wal a_wn f2_dvelimv a_sup_set_class f3_dvelimv a_sup_set_class a_wceq f2_dvelimv a_wal a_wn a_wa f4_dvelimv a_sup_set_class f3_dvelimv a_sup_set_class a_wceq f0_dvelimv a_wi f2_dvelimv f4_dvelimv p_hbald e0_dvelimv f4_dvelimv a_sup_set_class f3_dvelimv a_sup_set_class a_wceq f0_dvelimv f1_dvelimv p_biimpd f4_dvelimv a_sup_set_class f3_dvelimv a_sup_set_class a_wceq f0_dvelimv f1_dvelimv p_a2i f4_dvelimv a_sup_set_class f3_dvelimv a_sup_set_class a_wceq f0_dvelimv a_wi f4_dvelimv a_sup_set_class f3_dvelimv a_sup_set_class a_wceq f1_dvelimv a_wi f4_dvelimv p_alimi f4_dvelimv f3_dvelimv p_ax9v f4_dvelimv a_sup_set_class f3_dvelimv a_sup_set_class a_wceq f1_dvelimv p_con3 f4_dvelimv a_sup_set_class f3_dvelimv a_sup_set_class a_wceq f1_dvelimv a_wi f1_dvelimv a_wn f4_dvelimv a_sup_set_class f3_dvelimv a_sup_set_class a_wceq a_wn f4_dvelimv p_al2imi f4_dvelimv a_sup_set_class f3_dvelimv a_sup_set_class a_wceq f1_dvelimv a_wi f4_dvelimv a_wal f1_dvelimv a_wn f4_dvelimv a_wal f4_dvelimv a_sup_set_class f3_dvelimv a_sup_set_class a_wceq a_wn f4_dvelimv a_wal p_mtoi f4_dvelimv a_sup_set_class f3_dvelimv a_sup_set_class a_wceq f0_dvelimv a_wi f4_dvelimv a_wal f4_dvelimv a_sup_set_class f3_dvelimv a_sup_set_class a_wceq f1_dvelimv a_wi f4_dvelimv a_wal f1_dvelimv a_wn f4_dvelimv a_wal a_wn p_syl f1_dvelimv a_wn f4_dvelimv a_ax-17 f4_dvelimv a_sup_set_class f3_dvelimv a_sup_set_class a_wceq f0_dvelimv a_wi f4_dvelimv a_wal f1_dvelimv a_wn f4_dvelimv a_wal f1_dvelimv p_nsyl2 f4_dvelimv a_sup_set_class f3_dvelimv a_sup_set_class a_wceq f0_dvelimv a_wi f4_dvelimv a_wal f1_dvelimv f2_dvelimv p_alimi f1_dvelimv f4_dvelimv a_sup_set_class f3_dvelimv a_sup_set_class a_wceq f0_dvelimv a_wi f4_dvelimv a_wal f2_dvelimv a_sup_set_class f4_dvelimv a_sup_set_class a_wceq f2_dvelimv a_wal a_wn f2_dvelimv a_sup_set_class f3_dvelimv a_sup_set_class a_wceq f2_dvelimv a_wal a_wn a_wa f4_dvelimv a_sup_set_class f3_dvelimv a_sup_set_class a_wceq f0_dvelimv a_wi f4_dvelimv a_wal f2_dvelimv a_wal f1_dvelimv f2_dvelimv a_wal p_syl56 f2_dvelimv a_sup_set_class f4_dvelimv a_sup_set_class a_wceq f2_dvelimv a_wal a_wn f2_dvelimv a_sup_set_class f3_dvelimv a_sup_set_class a_wceq f2_dvelimv a_wal a_wn f1_dvelimv f1_dvelimv f2_dvelimv a_wal a_wi p_expcom f2_dvelimv a_sup_set_class f4_dvelimv a_sup_set_class a_wceq f2_dvelimv p_sp f1_dvelimv f4_dvelimv a_ax-17 f1_dvelimv f2_dvelimv f4_dvelimv a_ax-11 f2_dvelimv a_sup_set_class f4_dvelimv a_sup_set_class a_wceq f2_dvelimv a_wal f2_dvelimv a_sup_set_class f4_dvelimv a_sup_set_class a_wceq f1_dvelimv f1_dvelimv f4_dvelimv a_wal f2_dvelimv a_sup_set_class f4_dvelimv a_sup_set_class a_wceq f1_dvelimv a_wi f2_dvelimv a_wal p_syl2im f2_dvelimv a_sup_set_class f4_dvelimv a_sup_set_class a_wceq f1_dvelimv p_pm2.27 f2_dvelimv a_sup_set_class f4_dvelimv a_sup_set_class a_wceq f2_dvelimv a_sup_set_class f4_dvelimv a_sup_set_class a_wceq f1_dvelimv a_wi f1_dvelimv f2_dvelimv p_al2imi f2_dvelimv a_sup_set_class f4_dvelimv a_sup_set_class a_wceq f2_dvelimv a_wal f1_dvelimv f2_dvelimv a_sup_set_class f4_dvelimv a_sup_set_class a_wceq f1_dvelimv a_wi f2_dvelimv a_wal f1_dvelimv f2_dvelimv a_wal p_syld f2_dvelimv a_sup_set_class f3_dvelimv a_sup_set_class a_wceq f2_dvelimv a_wal a_wn f2_dvelimv a_sup_set_class f4_dvelimv a_sup_set_class a_wceq f2_dvelimv a_wal f1_dvelimv f1_dvelimv f2_dvelimv a_wal a_wi p_pm2.61d2 $.
$}

$(Quantifier introduction when one pair of variables is distinct.
       (Contributed by NM, 2-Jan-2002.)  (Revised by NM, 20-Jul-2015.) $)

${
	$v x y z  $.
	$d w z x  $.
	$d w y  $.
	f0_dveeq2 $f set x $.
	f1_dveeq2 $f set y $.
	f2_dveeq2 $f set z $.
	i0_dveeq2 $f set w $.
	p_dveeq2 $p |- ( -. A. x x = y -> ( z = y -> A. x z = y ) ) $= i0_dveeq2 f1_dveeq2 f2_dveeq2 p_equequ2 f2_dveeq2 a_sup_set_class i0_dveeq2 a_sup_set_class a_wceq f2_dveeq2 a_sup_set_class f1_dveeq2 a_sup_set_class a_wceq f0_dveeq2 f1_dveeq2 i0_dveeq2 p_dvelimv $.
$}

$(Lemma for ~ ax10 .  Change bound variable.  (Contributed by NM,
       8-Jul-2016.) $)

${
	$v x y w  $.
	$d w z x  $.
	$d w z y  $.
	f0_ax10lem4 $f set x $.
	f1_ax10lem4 $f set y $.
	f2_ax10lem4 $f set w $.
	i0_ax10lem4 $f set z $.
	p_ax10lem4 $p |- ( A. x x = w -> A. y y = x ) $= f0_ax10lem4 f1_ax10lem4 f2_ax10lem4 p_ax10lem1 i0_ax10lem4 f0_ax10lem4 f2_ax10lem4 p_equequ1 i0_ax10lem4 a_sup_set_class f2_ax10lem4 a_sup_set_class a_wceq f0_ax10lem4 a_sup_set_class f2_ax10lem4 a_sup_set_class a_wceq f1_ax10lem4 f0_ax10lem4 i0_ax10lem4 p_dvelimv f0_ax10lem4 a_sup_set_class f2_ax10lem4 a_sup_set_class a_wceq f1_ax10lem4 p_hba1 f0_ax10lem4 f2_ax10lem4 f1_ax10lem4 p_equequ2 f0_ax10lem4 a_sup_set_class f2_ax10lem4 a_sup_set_class a_wceq f1_ax10lem4 a_sup_set_class f0_ax10lem4 a_sup_set_class a_wceq f1_ax10lem4 a_sup_set_class f2_ax10lem4 a_sup_set_class a_wceq a_wb f1_ax10lem4 p_sps f0_ax10lem4 a_sup_set_class f2_ax10lem4 a_sup_set_class a_wceq f1_ax10lem4 a_wal f1_ax10lem4 a_sup_set_class f0_ax10lem4 a_sup_set_class a_wceq f1_ax10lem4 a_sup_set_class f2_ax10lem4 a_sup_set_class a_wceq f1_ax10lem4 p_albidh f0_ax10lem4 a_sup_set_class f2_ax10lem4 a_sup_set_class a_wceq f1_ax10lem4 a_wal f1_ax10lem4 a_sup_set_class f0_ax10lem4 a_sup_set_class a_wceq f1_ax10lem4 a_wal f1_ax10lem4 a_sup_set_class f2_ax10lem4 a_sup_set_class a_wceq f1_ax10lem4 a_wal p_biimprd f1_ax10lem4 a_sup_set_class f0_ax10lem4 a_sup_set_class a_wceq f1_ax10lem4 a_wal a_wn f0_ax10lem4 a_sup_set_class f2_ax10lem4 a_sup_set_class a_wceq f0_ax10lem4 a_sup_set_class f2_ax10lem4 a_sup_set_class a_wceq f1_ax10lem4 a_wal f1_ax10lem4 a_sup_set_class f2_ax10lem4 a_sup_set_class a_wceq f1_ax10lem4 a_wal f1_ax10lem4 a_sup_set_class f0_ax10lem4 a_sup_set_class a_wceq f1_ax10lem4 a_wal a_wi p_syl6 f0_ax10lem4 a_sup_set_class f2_ax10lem4 a_sup_set_class a_wceq f0_ax10lem4 a_wal f1_ax10lem4 a_sup_set_class f2_ax10lem4 a_sup_set_class a_wceq f1_ax10lem4 a_wal f1_ax10lem4 a_sup_set_class f0_ax10lem4 a_sup_set_class a_wceq f1_ax10lem4 a_wal a_wn f0_ax10lem4 a_sup_set_class f2_ax10lem4 a_sup_set_class a_wceq f1_ax10lem4 a_sup_set_class f0_ax10lem4 a_sup_set_class a_wceq f1_ax10lem4 a_wal p_syl7 f1_ax10lem4 a_sup_set_class f0_ax10lem4 a_sup_set_class a_wceq f1_ax10lem4 a_wal a_wn f0_ax10lem4 a_sup_set_class f2_ax10lem4 a_sup_set_class a_wceq f0_ax10lem4 a_sup_set_class f2_ax10lem4 a_sup_set_class a_wceq f0_ax10lem4 a_wal f1_ax10lem4 a_sup_set_class f0_ax10lem4 a_sup_set_class a_wceq f1_ax10lem4 a_wal a_wi f0_ax10lem4 p_spsd f1_ax10lem4 a_sup_set_class f0_ax10lem4 a_sup_set_class a_wceq f1_ax10lem4 a_wal a_wn f0_ax10lem4 a_sup_set_class f2_ax10lem4 a_sup_set_class a_wceq f0_ax10lem4 a_wal f1_ax10lem4 a_sup_set_class f0_ax10lem4 a_sup_set_class a_wceq f1_ax10lem4 a_wal p_pm2.43d f1_ax10lem4 a_sup_set_class f0_ax10lem4 a_sup_set_class a_wceq f1_ax10lem4 a_wal a_wn f0_ax10lem4 a_sup_set_class f2_ax10lem4 a_sup_set_class a_wceq f0_ax10lem4 a_wal f1_ax10lem4 a_sup_set_class f0_ax10lem4 a_sup_set_class a_wceq f1_ax10lem4 a_wal p_com12 f0_ax10lem4 a_sup_set_class f2_ax10lem4 a_sup_set_class a_wceq f0_ax10lem4 a_wal f1_ax10lem4 a_sup_set_class f0_ax10lem4 a_sup_set_class a_wceq f1_ax10lem4 a_wal p_pm2.18d $.
$}

$(Lemma for ~ ax10 .  Change free and bound variables.  (Contributed by
       NM, 22-Jul-2015.) $)

${
	$v x y z w  $.
	$d w z  $.
	$d u v w  $.
	$d v x  $.
	$d v y  $.
	f0_ax10lem5 $f set x $.
	f1_ax10lem5 $f set y $.
	f2_ax10lem5 $f set z $.
	f3_ax10lem5 $f set w $.
	i0_ax10lem5 $f set v $.
	i1_ax10lem5 $f set u $.
	p_ax10lem5 $p |- ( A. z z = w -> A. y y = x ) $= f2_ax10lem5 i0_ax10lem5 f3_ax10lem5 p_ax10lem1 i0_ax10lem5 i1_ax10lem5 f3_ax10lem5 p_ax10lem4 f2_ax10lem5 a_sup_set_class f3_ax10lem5 a_sup_set_class a_wceq f2_ax10lem5 a_wal i0_ax10lem5 a_sup_set_class f3_ax10lem5 a_sup_set_class a_wceq i0_ax10lem5 a_wal i1_ax10lem5 a_sup_set_class i0_ax10lem5 a_sup_set_class a_wceq i1_ax10lem5 a_wal p_syl i1_ax10lem5 f0_ax10lem5 i0_ax10lem5 p_ax10lem1 f2_ax10lem5 a_sup_set_class f3_ax10lem5 a_sup_set_class a_wceq f2_ax10lem5 a_wal i1_ax10lem5 a_sup_set_class i0_ax10lem5 a_sup_set_class a_wceq i1_ax10lem5 a_wal f0_ax10lem5 a_sup_set_class i0_ax10lem5 a_sup_set_class a_wceq f0_ax10lem5 a_wal p_syl f0_ax10lem5 f1_ax10lem5 i0_ax10lem5 p_ax10lem4 f2_ax10lem5 a_sup_set_class f3_ax10lem5 a_sup_set_class a_wceq f2_ax10lem5 a_wal f0_ax10lem5 a_sup_set_class i0_ax10lem5 a_sup_set_class a_wceq f0_ax10lem5 a_wal f1_ax10lem5 a_sup_set_class f0_ax10lem5 a_sup_set_class a_wceq f1_ax10lem5 a_wal p_syl $.
$}

$(Lemma for ~ ax10 .  Similar to ~ ax10o but with reversed antecedent.
     (Contributed by NM, 25-Jul-2015.) $)

${
	$v ph x y  $.
	f0_ax10lem6 $f wff ph $.
	f1_ax10lem6 $f set x $.
	f2_ax10lem6 $f set y $.
	p_ax10lem6 $p |- ( A. y y = x -> ( A. x ph -> A. y ph ) ) $= f0_ax10lem6 f2_ax10lem6 f1_ax10lem6 a_ax-11 f2_ax10lem6 a_sup_set_class f1_ax10lem6 a_sup_set_class a_wceq f0_ax10lem6 f1_ax10lem6 a_wal f2_ax10lem6 a_sup_set_class f1_ax10lem6 a_sup_set_class a_wceq f0_ax10lem6 a_wi f2_ax10lem6 a_wal a_wi f2_ax10lem6 p_sps f2_ax10lem6 a_sup_set_class f1_ax10lem6 a_sup_set_class a_wceq f0_ax10lem6 p_pm2.27 f2_ax10lem6 a_sup_set_class f1_ax10lem6 a_sup_set_class a_wceq f2_ax10lem6 a_sup_set_class f1_ax10lem6 a_sup_set_class a_wceq f0_ax10lem6 a_wi f0_ax10lem6 f2_ax10lem6 p_al2imi f2_ax10lem6 a_sup_set_class f1_ax10lem6 a_sup_set_class a_wceq f2_ax10lem6 a_wal f0_ax10lem6 f1_ax10lem6 a_wal f2_ax10lem6 a_sup_set_class f1_ax10lem6 a_sup_set_class a_wceq f0_ax10lem6 a_wi f2_ax10lem6 a_wal f0_ax10lem6 f2_ax10lem6 a_wal p_syld $.
$}

$(Derive set.mm's original ~ ax-10 from others.  (Contributed by NM,
       25-Jul-2015.)  (Revised by NM, 7-Nov-2015.) $)

${
	$v x y  $.
	$d x z  $.
	$d y z  $.
	f0_ax10 $f set x $.
	f1_ax10 $f set y $.
	i0_ax10 $f set z $.
	p_ax10 $p |- ( A. x x = y -> A. y y = x ) $= i0_ax10 f0_ax10 p_ax9v i0_ax10 a_sup_set_class f0_ax10 a_sup_set_class a_wceq i0_ax10 a_df-ex f1_ax10 f0_ax10 i0_ax10 p_dveeq2 f1_ax10 a_sup_set_class f0_ax10 a_sup_set_class a_wceq f1_ax10 a_wal a_wn i0_ax10 a_sup_set_class f0_ax10 a_sup_set_class a_wceq i0_ax10 a_sup_set_class f0_ax10 a_sup_set_class a_wceq f1_ax10 a_wal p_imp i0_ax10 a_sup_set_class f0_ax10 a_sup_set_class a_wceq f1_ax10 f0_ax10 p_ax10lem6 i0_ax10 f0_ax10 p_equcomi i0_ax10 a_sup_set_class f0_ax10 a_sup_set_class a_wceq f0_ax10 a_sup_set_class i0_ax10 a_sup_set_class a_wceq f0_ax10 p_alimi f0_ax10 a_sup_set_class f1_ax10 a_sup_set_class a_wceq f0_ax10 a_wal i0_ax10 a_sup_set_class f0_ax10 a_sup_set_class a_wceq f1_ax10 a_wal i0_ax10 a_sup_set_class f0_ax10 a_sup_set_class a_wceq f0_ax10 a_wal f0_ax10 a_sup_set_class i0_ax10 a_sup_set_class a_wceq f0_ax10 a_wal p_syl6 f0_ax10 f1_ax10 f0_ax10 i0_ax10 p_ax10lem5 f1_ax10 a_sup_set_class f0_ax10 a_sup_set_class a_wceq f1_ax10 a_wal a_wn i0_ax10 a_sup_set_class f0_ax10 a_sup_set_class a_wceq a_wa i0_ax10 a_sup_set_class f0_ax10 a_sup_set_class a_wceq f1_ax10 a_wal f0_ax10 a_sup_set_class f1_ax10 a_sup_set_class a_wceq f0_ax10 a_wal f0_ax10 a_sup_set_class i0_ax10 a_sup_set_class a_wceq f0_ax10 a_wal f1_ax10 a_sup_set_class f0_ax10 a_sup_set_class a_wceq f1_ax10 a_wal p_syl56 f0_ax10 a_sup_set_class f1_ax10 a_sup_set_class a_wceq f0_ax10 a_wal f1_ax10 a_sup_set_class f0_ax10 a_sup_set_class a_wceq f1_ax10 a_wal a_wn i0_ax10 a_sup_set_class f0_ax10 a_sup_set_class a_wceq f1_ax10 a_sup_set_class f0_ax10 a_sup_set_class a_wceq f1_ax10 a_wal p_exp3acom23 f1_ax10 a_sup_set_class f0_ax10 a_sup_set_class a_wceq f1_ax10 a_wal p_pm2.18 f0_ax10 a_sup_set_class f1_ax10 a_sup_set_class a_wceq f0_ax10 a_wal i0_ax10 a_sup_set_class f0_ax10 a_sup_set_class a_wceq f1_ax10 a_sup_set_class f0_ax10 a_sup_set_class a_wceq f1_ax10 a_wal a_wn f1_ax10 a_sup_set_class f0_ax10 a_sup_set_class a_wceq f1_ax10 a_wal a_wi f1_ax10 a_sup_set_class f0_ax10 a_sup_set_class a_wceq f1_ax10 a_wal p_syl6 f0_ax10 a_sup_set_class f1_ax10 a_sup_set_class a_wceq f0_ax10 a_wal i0_ax10 a_sup_set_class f0_ax10 a_sup_set_class a_wceq f1_ax10 a_sup_set_class f0_ax10 a_sup_set_class a_wceq f1_ax10 a_wal i0_ax10 p_exlimdv i0_ax10 a_sup_set_class f0_ax10 a_sup_set_class a_wceq a_wn i0_ax10 a_wal a_wn i0_ax10 a_sup_set_class f0_ax10 a_sup_set_class a_wceq i0_ax10 a_wex f0_ax10 a_sup_set_class f1_ax10 a_sup_set_class a_wceq f0_ax10 a_wal f1_ax10 a_sup_set_class f0_ax10 a_sup_set_class a_wceq f1_ax10 a_wal p_syl5bir f0_ax10 a_sup_set_class f1_ax10 a_sup_set_class a_wceq f0_ax10 a_wal i0_ax10 a_sup_set_class f0_ax10 a_sup_set_class a_wceq a_wn i0_ax10 a_wal a_wn f1_ax10 a_sup_set_class f0_ax10 a_sup_set_class a_wceq f1_ax10 a_wal p_mpi $.
$}

$(Generalization of ~ ax16 .  (Contributed by NM, 25-Jul-2015.) $)

${
	$v ph x y z  $.
	$d x y  $.
	$d w ph  $.
	$d w z  $.
	f0_a16g $f wff ph $.
	f1_a16g $f set x $.
	f2_a16g $f set y $.
	f3_a16g $f set z $.
	i0_a16g $f set w $.
	p_a16g $p |- ( A. x x = y -> ( ph -> A. z ph ) ) $= i0_a16g f3_a16g p_a9ev f3_a16g i0_a16g f1_a16g f2_a16g p_ax10lem5 i0_a16g a_sup_set_class f3_a16g a_sup_set_class a_wceq i0_a16g p_hbn1 i0_a16g a_sup_set_class f3_a16g a_sup_set_class a_wceq i0_a16g a_wal f0_a16g f0_a16g f3_a16g a_wal a_wi p_pm2.21 i0_a16g a_sup_set_class f3_a16g a_sup_set_class a_wceq i0_a16g a_wal a_wn i0_a16g a_sup_set_class f3_a16g a_sup_set_class a_wceq i0_a16g a_wal f0_a16g f0_a16g f3_a16g a_wal a_wi a_wi i0_a16g p_alrimih f0_a16g f0_a16g f3_a16g a_wal a_wi i0_a16g a_ax-17 f0_a16g f0_a16g f3_a16g a_wal a_wi i0_a16g a_sup_set_class f3_a16g a_sup_set_class a_wceq i0_a16g a_wal a_ax-1 f0_a16g f0_a16g f3_a16g a_wal a_wi i0_a16g a_sup_set_class f3_a16g a_sup_set_class a_wceq i0_a16g a_wal f0_a16g f0_a16g f3_a16g a_wal a_wi a_wi i0_a16g p_alrimih i0_a16g a_sup_set_class f3_a16g a_sup_set_class a_wceq i0_a16g a_wal f0_a16g f0_a16g f3_a16g a_wal a_wi i0_a16g a_sup_set_class f3_a16g a_sup_set_class a_wceq i0_a16g a_wal f0_a16g f0_a16g f3_a16g a_wal a_wi a_wi i0_a16g a_wal p_ja i0_a16g f3_a16g i0_a16g f3_a16g p_ax10lem5 i0_a16g f3_a16g p_equcomi f0_a16g i0_a16g a_ax-17 f0_a16g f3_a16g i0_a16g a_ax-11 i0_a16g a_sup_set_class f3_a16g a_sup_set_class a_wceq f3_a16g a_sup_set_class i0_a16g a_sup_set_class a_wceq f0_a16g f0_a16g i0_a16g a_wal f3_a16g a_sup_set_class i0_a16g a_sup_set_class a_wceq f0_a16g a_wi f3_a16g a_wal p_syl2im f3_a16g a_sup_set_class i0_a16g a_sup_set_class a_wceq f0_a16g f3_a16g a_ax-5 i0_a16g a_sup_set_class f3_a16g a_sup_set_class a_wceq f0_a16g f3_a16g a_sup_set_class i0_a16g a_sup_set_class a_wceq f0_a16g a_wi f3_a16g a_wal f3_a16g a_sup_set_class i0_a16g a_sup_set_class a_wceq f3_a16g a_wal f0_a16g f3_a16g a_wal a_wi p_syl6 i0_a16g a_sup_set_class f3_a16g a_sup_set_class a_wceq f0_a16g f3_a16g a_sup_set_class i0_a16g a_sup_set_class a_wceq f3_a16g a_wal f0_a16g f3_a16g a_wal p_com23 i0_a16g a_sup_set_class f3_a16g a_sup_set_class a_wceq i0_a16g a_wal f3_a16g a_sup_set_class i0_a16g a_sup_set_class a_wceq f3_a16g a_wal i0_a16g a_sup_set_class f3_a16g a_sup_set_class a_wceq f0_a16g f0_a16g f3_a16g a_wal a_wi p_syl5 i0_a16g a_sup_set_class f3_a16g a_sup_set_class a_wceq i0_a16g a_sup_set_class f3_a16g a_sup_set_class a_wceq i0_a16g a_wal f0_a16g f0_a16g f3_a16g a_wal a_wi a_wi i0_a16g p_exlimih i0_a16g a_sup_set_class f3_a16g a_sup_set_class a_wceq i0_a16g a_wex f1_a16g a_sup_set_class f2_a16g a_sup_set_class a_wceq f1_a16g a_wal i0_a16g a_sup_set_class f3_a16g a_sup_set_class a_wceq i0_a16g a_wal f0_a16g f0_a16g f3_a16g a_wal a_wi p_mpsyl $.
$}

$(Commutation law for identical variable specifiers.  The antecedent and
     consequent are true when ` x ` and ` y ` are substituted with the same
     variable.  Lemma L12 in [Megill] p. 445 (p. 12 of the preprint).
     (Contributed by NM, 5-Aug-1993.) $)

${
	$v x y  $.
	f0_aecom $f set x $.
	f1_aecom $f set y $.
	p_aecom $p |- ( A. x x = y -> A. y y = x ) $= f0_aecom f1_aecom p_ax10 $.
$}

$(A commutation rule for identical variable specifiers.  (Contributed by
       NM, 5-Aug-1993.) $)

${
	$v ph x y  $.
	f0_aecoms $f wff ph $.
	f1_aecoms $f set x $.
	f2_aecoms $f set y $.
	e0_aecoms $e |- ( A. x x = y -> ph ) $.
	p_aecoms $p |- ( A. y y = x -> ph ) $= f2_aecoms f1_aecoms p_aecom e0_aecoms f2_aecoms a_sup_set_class f1_aecoms a_sup_set_class a_wceq f2_aecoms a_wal f1_aecoms a_sup_set_class f2_aecoms a_sup_set_class a_wceq f1_aecoms a_wal f0_aecoms p_syl $.
$}

$(A commutation rule for distinct variable specifiers.  (Contributed by
       NM, 2-Jan-2002.) $)

${
	$v ph x y  $.
	f0_naecoms $f wff ph $.
	f1_naecoms $f set x $.
	f2_naecoms $f set y $.
	e0_naecoms $e |- ( -. A. x x = y -> ph ) $.
	p_naecoms $p |- ( -. A. y y = x -> ph ) $= f1_naecoms f2_naecoms p_aecom e0_naecoms f1_naecoms a_sup_set_class f2_naecoms a_sup_set_class a_wceq f1_naecoms a_wal f2_naecoms a_sup_set_class f1_naecoms a_sup_set_class a_wceq f2_naecoms a_wal f0_naecoms p_nsyl4 f0_naecoms f2_naecoms a_sup_set_class f1_naecoms a_sup_set_class a_wceq f2_naecoms a_wal p_con1i $.
$}

$(Theorem showing that ~ ax-9 follows from the weaker version ~ ax9v .
       (Even though this theorem depends on ~ ax-9 , all references of ~ ax-9
       are made via ~ ax9v .  An earlier version stated ~ ax9v as a separate
       axiom, but having two axioms caused some confusion.)

       This theorem should be referenced in place of ~ ax-9 so that all proofs
       can be traced back to ~ ax9v .  (Contributed by NM, 12-Nov-2013.)
       (Revised by NM, 25-Jul-2015.) $)

${
	$v x y  $.
	$d x v  $.
	$d y v  $.
	f0_ax9 $f set x $.
	f1_ax9 $f set y $.
	i0_ax9 $f set v $.
	p_ax9 $p |- -. A. x -. x = y $= f0_ax9 a_sup_set_class f1_ax9 a_sup_set_class a_wceq a_wn f0_ax9 p_sp f0_ax9 a_sup_set_class f1_ax9 a_sup_set_class a_wceq f0_ax9 p_sp f0_ax9 a_sup_set_class f1_ax9 a_sup_set_class a_wceq a_wn f0_ax9 a_wal f0_ax9 a_sup_set_class f1_ax9 a_sup_set_class a_wceq f0_ax9 a_sup_set_class f1_ax9 a_sup_set_class a_wceq f0_ax9 a_wal p_nsyl3 i0_ax9 f1_ax9 p_ax9v f0_ax9 f1_ax9 i0_ax9 p_dveeq2 f0_ax9 i0_ax9 p_ax9v i0_ax9 a_sup_set_class f1_ax9 a_sup_set_class a_wceq f0_ax9 p_hba1 i0_ax9 a_sup_set_class f1_ax9 a_sup_set_class a_wceq f0_ax9 p_sp i0_ax9 f1_ax9 f0_ax9 p_equequ2 i0_ax9 a_sup_set_class f1_ax9 a_sup_set_class a_wceq f0_ax9 a_wal i0_ax9 a_sup_set_class f1_ax9 a_sup_set_class a_wceq f0_ax9 a_sup_set_class i0_ax9 a_sup_set_class a_wceq f0_ax9 a_sup_set_class f1_ax9 a_sup_set_class a_wceq a_wb p_syl i0_ax9 a_sup_set_class f1_ax9 a_sup_set_class a_wceq f0_ax9 a_wal f0_ax9 a_sup_set_class i0_ax9 a_sup_set_class a_wceq f0_ax9 a_sup_set_class f1_ax9 a_sup_set_class a_wceq p_notbid i0_ax9 a_sup_set_class f1_ax9 a_sup_set_class a_wceq f0_ax9 a_wal f0_ax9 a_sup_set_class i0_ax9 a_sup_set_class a_wceq a_wn f0_ax9 a_sup_set_class f1_ax9 a_sup_set_class a_wceq a_wn f0_ax9 p_albidh i0_ax9 a_sup_set_class f1_ax9 a_sup_set_class a_wceq f0_ax9 a_wal f0_ax9 a_sup_set_class i0_ax9 a_sup_set_class a_wceq a_wn f0_ax9 a_wal f0_ax9 a_sup_set_class f1_ax9 a_sup_set_class a_wceq a_wn f0_ax9 a_wal p_mtbii f0_ax9 a_sup_set_class f1_ax9 a_sup_set_class a_wceq f0_ax9 a_wal a_wn i0_ax9 a_sup_set_class f1_ax9 a_sup_set_class a_wceq i0_ax9 a_sup_set_class f1_ax9 a_sup_set_class a_wceq f0_ax9 a_wal f0_ax9 a_sup_set_class f1_ax9 a_sup_set_class a_wceq a_wn f0_ax9 a_wal a_wn p_syl6com i0_ax9 a_sup_set_class f1_ax9 a_sup_set_class a_wceq f0_ax9 a_sup_set_class f1_ax9 a_sup_set_class a_wceq f0_ax9 a_wal a_wn f0_ax9 a_sup_set_class f1_ax9 a_sup_set_class a_wceq a_wn f0_ax9 a_wal a_wn a_wi p_con3i f0_ax9 a_sup_set_class f1_ax9 a_sup_set_class a_wceq f0_ax9 a_wal a_wn f0_ax9 a_sup_set_class f1_ax9 a_sup_set_class a_wceq a_wn f0_ax9 a_wal a_wn a_wi a_wn i0_ax9 a_sup_set_class f1_ax9 a_sup_set_class a_wceq a_wn i0_ax9 p_alrimiv f0_ax9 a_sup_set_class f1_ax9 a_sup_set_class a_wceq f0_ax9 a_wal a_wn f0_ax9 a_sup_set_class f1_ax9 a_sup_set_class a_wceq a_wn f0_ax9 a_wal a_wn a_wi i0_ax9 a_sup_set_class f1_ax9 a_sup_set_class a_wceq a_wn i0_ax9 a_wal p_mt3 f0_ax9 a_sup_set_class f1_ax9 a_sup_set_class a_wceq f0_ax9 a_wal f0_ax9 a_sup_set_class f1_ax9 a_sup_set_class a_wceq a_wn f0_ax9 a_wal a_wn p_pm2.61i $.
$}

$(Show that the original axiom ~ ax-9o can be derived from ~ ax9 and
     others.  See ~ ax9from9o for the rederivation of ~ ax9 from ~ ax-9o .

     Normally, ~ ax9o should be used rather than ~ ax-9o , except by theorems
     specifically studying the latter's properties.  (Contributed by NM,
     5-Aug-1993.)  (Proof modification is discouraged.) $)

${
	$v ph x y  $.
	f0_ax9o $f wff ph $.
	f1_ax9o $f set x $.
	f2_ax9o $f set y $.
	p_ax9o $p |- ( A. x ( x = y -> A. x ph ) -> ph ) $= f1_ax9o f2_ax9o p_ax9 f1_ax9o a_sup_set_class f2_ax9o a_sup_set_class a_wceq f0_ax9o f1_ax9o a_wal p_con3 f1_ax9o a_sup_set_class f2_ax9o a_sup_set_class a_wceq f0_ax9o f1_ax9o a_wal a_wi f0_ax9o f1_ax9o a_wal a_wn f1_ax9o a_sup_set_class f2_ax9o a_sup_set_class a_wceq a_wn f1_ax9o p_al2imi f1_ax9o a_sup_set_class f2_ax9o a_sup_set_class a_wceq f0_ax9o f1_ax9o a_wal a_wi f1_ax9o a_wal f0_ax9o f1_ax9o a_wal a_wn f1_ax9o a_wal f1_ax9o a_sup_set_class f2_ax9o a_sup_set_class a_wceq a_wn f1_ax9o a_wal p_mtoi f0_ax9o f1_ax9o p_ax6o f1_ax9o a_sup_set_class f2_ax9o a_sup_set_class a_wceq f0_ax9o f1_ax9o a_wal a_wi f1_ax9o a_wal f0_ax9o f1_ax9o a_wal a_wn f1_ax9o a_wal a_wn f0_ax9o p_syl $.
$}

$(At least one individual exists.  This is not a theorem of free logic,
     which is sound in empty domains.  For such a logic, we would add this
     theorem as an axiom of set theory (Axiom 0 of [Kunen] p. 10).  In the
     system consisting of ~ ax-5 through ~ ax-14 and ~ ax-17 , all axioms other
     than ~ ax9 are believed to be theorems of free logic, although the system
     without ~ ax9 is probably not complete in free logic.  (Contributed by NM,
     5-Aug-1993.) $)

${
	$v x y  $.
	f0_a9e $f set x $.
	f1_a9e $f set y $.
	p_a9e $p |- E. x x = y $= f0_a9e f1_a9e p_ax9 f0_a9e a_sup_set_class f1_a9e a_sup_set_class a_wceq f0_a9e a_df-ex f0_a9e a_sup_set_class f1_a9e a_sup_set_class a_wceq f0_a9e a_wex f0_a9e a_sup_set_class f1_a9e a_sup_set_class a_wceq a_wn f0_a9e a_wal a_wn p_mpbir $.
$}

$(Show that ~ ax-10o can be derived from ~ ax-10 in the form of ~ ax10 .
     Normally, ~ ax10o should be used rather than ~ ax-10o , except by theorems
     specifically studying the latter's properties.  (Contributed by NM,
     16-May-2008.)  (Proof modification is discouraged.) $)

${
	$v ph x y  $.
	f0_ax10o $f wff ph $.
	f1_ax10o $f set x $.
	f2_ax10o $f set y $.
	p_ax10o $p |- ( A. x x = y -> ( A. x ph -> A. y ph ) ) $= f1_ax10o f2_ax10o p_ax10 f0_ax10o f2_ax10o f1_ax10o a_ax-11 f0_ax10o f1_ax10o a_wal f2_ax10o a_sup_set_class f1_ax10o a_sup_set_class a_wceq f0_ax10o a_wi f2_ax10o a_wal a_wi f2_ax10o f1_ax10o p_equcoms f1_ax10o a_sup_set_class f2_ax10o a_sup_set_class a_wceq f0_ax10o f1_ax10o a_wal f2_ax10o a_sup_set_class f1_ax10o a_sup_set_class a_wceq f0_ax10o a_wi f2_ax10o a_wal a_wi f1_ax10o p_sps f2_ax10o a_sup_set_class f1_ax10o a_sup_set_class a_wceq f0_ax10o p_pm2.27 f2_ax10o a_sup_set_class f1_ax10o a_sup_set_class a_wceq f2_ax10o a_sup_set_class f1_ax10o a_sup_set_class a_wceq f0_ax10o a_wi f0_ax10o f2_ax10o p_al2imi f1_ax10o a_sup_set_class f2_ax10o a_sup_set_class a_wceq f1_ax10o a_wal f2_ax10o a_sup_set_class f1_ax10o a_sup_set_class a_wceq f2_ax10o a_wal f0_ax10o f1_ax10o a_wal f2_ax10o a_sup_set_class f1_ax10o a_sup_set_class a_wceq f0_ax10o a_wi f2_ax10o a_wal f0_ax10o f2_ax10o a_wal p_sylsyld $.
$}

$(All variables are effectively bound in an identical variable specifier.
     (Contributed by NM, 5-Aug-1993.) $)

${
	$v x y z  $.
	f0_hbae $f set x $.
	f1_hbae $f set y $.
	f2_hbae $f set z $.
	p_hbae $p |- ( A. x x = y -> A. z A. x x = y ) $= f0_hbae a_sup_set_class f1_hbae a_sup_set_class a_wceq f0_hbae p_sp f0_hbae f1_hbae f2_hbae p_ax12o f0_hbae a_sup_set_class f1_hbae a_sup_set_class a_wceq f0_hbae a_wal f0_hbae a_sup_set_class f1_hbae a_sup_set_class a_wceq f2_hbae a_sup_set_class f0_hbae a_sup_set_class a_wceq f2_hbae a_wal a_wn f2_hbae a_sup_set_class f1_hbae a_sup_set_class a_wceq f2_hbae a_wal a_wn f0_hbae a_sup_set_class f1_hbae a_sup_set_class a_wceq f2_hbae a_wal p_syl7 f0_hbae a_sup_set_class f1_hbae a_sup_set_class a_wceq f0_hbae f2_hbae p_ax10o f0_hbae a_sup_set_class f1_hbae a_sup_set_class a_wceq f0_hbae a_wal f0_hbae a_sup_set_class f1_hbae a_sup_set_class a_wceq f2_hbae a_wal a_wi f0_hbae f2_hbae p_aecoms f0_hbae a_sup_set_class f1_hbae a_sup_set_class a_wceq f0_hbae f1_hbae p_ax10o f0_hbae a_sup_set_class f1_hbae a_sup_set_class a_wceq f0_hbae a_wal f0_hbae a_sup_set_class f1_hbae a_sup_set_class a_wceq f1_hbae a_wal p_pm2.43i f0_hbae a_sup_set_class f1_hbae a_sup_set_class a_wceq f1_hbae f2_hbae p_ax10o f0_hbae a_sup_set_class f1_hbae a_sup_set_class a_wceq f0_hbae a_wal f0_hbae a_sup_set_class f1_hbae a_sup_set_class a_wceq f1_hbae a_wal f1_hbae a_sup_set_class f2_hbae a_sup_set_class a_wceq f1_hbae a_wal f0_hbae a_sup_set_class f1_hbae a_sup_set_class a_wceq f2_hbae a_wal p_syl5 f0_hbae a_sup_set_class f1_hbae a_sup_set_class a_wceq f0_hbae a_wal f0_hbae a_sup_set_class f1_hbae a_sup_set_class a_wceq f2_hbae a_wal a_wi f1_hbae f2_hbae p_aecoms f2_hbae a_sup_set_class f0_hbae a_sup_set_class a_wceq f2_hbae a_wal f2_hbae a_sup_set_class f1_hbae a_sup_set_class a_wceq f2_hbae a_wal f0_hbae a_sup_set_class f1_hbae a_sup_set_class a_wceq f0_hbae a_wal f0_hbae a_sup_set_class f1_hbae a_sup_set_class a_wceq f2_hbae a_wal a_wi p_pm2.61ii f0_hbae a_sup_set_class f1_hbae a_sup_set_class a_wceq f0_hbae a_sup_set_class f1_hbae a_sup_set_class a_wceq f2_hbae a_wal f0_hbae p_a5i f0_hbae a_sup_set_class f1_hbae a_sup_set_class a_wceq f0_hbae f2_hbae a_ax-7 f0_hbae a_sup_set_class f1_hbae a_sup_set_class a_wceq f0_hbae a_wal f0_hbae a_sup_set_class f1_hbae a_sup_set_class a_wceq f2_hbae a_wal f0_hbae a_wal f0_hbae a_sup_set_class f1_hbae a_sup_set_class a_wceq f0_hbae a_wal f2_hbae a_wal p_syl $.
$}

$(All variables are effectively bound in an identical variable specifier.
     (Contributed by Mario Carneiro, 11-Aug-2016.) $)

${
	$v x y z  $.
	f0_nfae $f set x $.
	f1_nfae $f set y $.
	f2_nfae $f set z $.
	p_nfae $p |- F/ z A. x x = y $= f0_nfae f1_nfae f2_nfae p_hbae f0_nfae a_sup_set_class f1_nfae a_sup_set_class a_wceq f0_nfae a_wal f2_nfae p_nfi $.
$}

$(All variables are effectively bound in a distinct variable specifier.
     Lemma L19 in [Megill] p. 446 (p. 14 of the preprint).  (Contributed by NM,
     5-Aug-1993.) $)

${
	$v x y z  $.
	f0_hbnae $f set x $.
	f1_hbnae $f set y $.
	f2_hbnae $f set z $.
	p_hbnae $p |- ( -. A. x x = y -> A. z -. A. x x = y ) $= f0_hbnae f1_hbnae f2_hbnae p_hbae f0_hbnae a_sup_set_class f1_hbnae a_sup_set_class a_wceq f0_hbnae a_wal f2_hbnae p_hbn $.
$}

$(All variables are effectively bound in a distinct variable specifier.
     (Contributed by Mario Carneiro, 11-Aug-2016.) $)

${
	$v x y z  $.
	f0_nfnae $f set x $.
	f1_nfnae $f set y $.
	f2_nfnae $f set z $.
	p_nfnae $p |- F/ z -. A. x x = y $= f0_nfnae f1_nfnae f2_nfnae p_nfae f0_nfnae a_sup_set_class f1_nfnae a_sup_set_class a_wceq f0_nfnae a_wal f2_nfnae p_nfn $.
$}

$(Rule that applies ~ hbnae to antecedent.  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v ph x y z  $.
	f0_hbnaes $f wff ph $.
	f1_hbnaes $f set x $.
	f2_hbnaes $f set y $.
	f3_hbnaes $f set z $.
	e0_hbnaes $e |- ( A. z -. A. x x = y -> ph ) $.
	p_hbnaes $p |- ( -. A. x x = y -> ph ) $= f1_hbnaes f2_hbnaes f3_hbnaes p_hbnae e0_hbnaes f1_hbnaes a_sup_set_class f2_hbnaes a_sup_set_class a_wceq f1_hbnaes a_wal a_wn f1_hbnaes a_sup_set_class f2_hbnaes a_sup_set_class a_wceq f1_hbnaes a_wal a_wn f3_hbnaes a_wal f0_hbnaes p_syl $.
$}

$(A variable is effectively not free in an equality if it is not either of
     the involved variables. ` F/ ` version of ~ ax-12o .  (Contributed by
     Mario Carneiro, 6-Oct-2016.) $)

${
	$v x y z  $.
	f0_nfeqf $f set x $.
	f1_nfeqf $f set y $.
	f2_nfeqf $f set z $.
	p_nfeqf $p |- ( ( -. A. z z = x /\ -. A. z z = y ) -> F/ z x = y ) $= f2_nfeqf f0_nfeqf f2_nfeqf p_nfnae f2_nfeqf f1_nfeqf f2_nfeqf p_nfnae f2_nfeqf a_sup_set_class f0_nfeqf a_sup_set_class a_wceq f2_nfeqf a_wal a_wn f2_nfeqf a_sup_set_class f1_nfeqf a_sup_set_class a_wceq f2_nfeqf a_wal a_wn f2_nfeqf p_nfan f0_nfeqf f1_nfeqf f2_nfeqf p_ax12o f2_nfeqf a_sup_set_class f0_nfeqf a_sup_set_class a_wceq f2_nfeqf a_wal a_wn f2_nfeqf a_sup_set_class f1_nfeqf a_sup_set_class a_wceq f2_nfeqf a_wal a_wn f0_nfeqf a_sup_set_class f1_nfeqf a_sup_set_class a_wceq f0_nfeqf a_sup_set_class f1_nfeqf a_sup_set_class a_wceq f2_nfeqf a_wal a_wi p_imp f2_nfeqf a_sup_set_class f0_nfeqf a_sup_set_class a_wceq f2_nfeqf a_wal a_wn f2_nfeqf a_sup_set_class f1_nfeqf a_sup_set_class a_wceq f2_nfeqf a_wal a_wn a_wa f0_nfeqf a_sup_set_class f1_nfeqf a_sup_set_class a_wceq f2_nfeqf p_nfd $.
$}

$(Lemma used in proofs of substitution properties.  (Contributed by NM,
     5-Aug-1993.)  (Proof shortened by Mario Carneiro, 20-May-2014.) $)

${
	$v ph x y  $.
	f0_equs4 $f wff ph $.
	f1_equs4 $f set x $.
	f2_equs4 $f set y $.
	p_equs4 $p |- ( A. x ( x = y -> ph ) -> E. x ( x = y /\ ph ) ) $= f1_equs4 f2_equs4 p_a9e f1_equs4 a_sup_set_class f2_equs4 a_sup_set_class a_wceq f0_equs4 a_wi f1_equs4 a_sup_set_class f2_equs4 a_sup_set_class a_wceq f1_equs4 p_19.29 f1_equs4 a_sup_set_class f2_equs4 a_sup_set_class a_wceq f0_equs4 a_wi f1_equs4 a_wal f1_equs4 a_sup_set_class f2_equs4 a_sup_set_class a_wceq f1_equs4 a_wex f1_equs4 a_sup_set_class f2_equs4 a_sup_set_class a_wceq f0_equs4 a_wi f1_equs4 a_sup_set_class f2_equs4 a_sup_set_class a_wceq a_wa f1_equs4 a_wex p_mpan2 f1_equs4 a_sup_set_class f2_equs4 a_sup_set_class a_wceq f0_equs4 p_ancl f1_equs4 a_sup_set_class f2_equs4 a_sup_set_class a_wceq f0_equs4 a_wi f1_equs4 a_sup_set_class f2_equs4 a_sup_set_class a_wceq f1_equs4 a_sup_set_class f2_equs4 a_sup_set_class a_wceq f0_equs4 a_wa p_imp f1_equs4 a_sup_set_class f2_equs4 a_sup_set_class a_wceq f0_equs4 a_wi f1_equs4 a_sup_set_class f2_equs4 a_sup_set_class a_wceq a_wa f1_equs4 a_sup_set_class f2_equs4 a_sup_set_class a_wceq f0_equs4 a_wa f1_equs4 p_eximi f1_equs4 a_sup_set_class f2_equs4 a_sup_set_class a_wceq f0_equs4 a_wi f1_equs4 a_wal f1_equs4 a_sup_set_class f2_equs4 a_sup_set_class a_wceq f0_equs4 a_wi f1_equs4 a_sup_set_class f2_equs4 a_sup_set_class a_wceq a_wa f1_equs4 a_wex f1_equs4 a_sup_set_class f2_equs4 a_sup_set_class a_wceq f0_equs4 a_wa f1_equs4 a_wex p_syl $.
$}

$(A useful equivalence related to substitution.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Andrew Salmon, 12-Aug-2011.)  (Revised
       by Mario Carneiro, 3-Oct-2016.) $)

${
	$v ph ps x y  $.
	f0_equsal $f wff ph $.
	f1_equsal $f wff ps $.
	f2_equsal $f set x $.
	f3_equsal $f set y $.
	e0_equsal $e |- F/ x ps $.
	e1_equsal $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_equsal $p |- ( A. x ( x = y -> ph ) <-> ps ) $= e1_equsal e0_equsal f1_equsal f2_equsal p_19.3 f2_equsal a_sup_set_class f3_equsal a_sup_set_class a_wceq f0_equsal f1_equsal f1_equsal f2_equsal a_wal p_syl6bbr f2_equsal a_sup_set_class f3_equsal a_sup_set_class a_wceq f0_equsal f1_equsal f2_equsal a_wal p_pm5.74i f2_equsal a_sup_set_class f3_equsal a_sup_set_class a_wceq f0_equsal a_wi f2_equsal a_sup_set_class f3_equsal a_sup_set_class a_wceq f1_equsal f2_equsal a_wal a_wi f2_equsal p_albii e0_equsal e0_equsal f1_equsal f2_equsal p_nfri f1_equsal f1_equsal f2_equsal a_wal f2_equsal a_sup_set_class f3_equsal a_sup_set_class a_wceq p_a1d f1_equsal f2_equsal a_sup_set_class f3_equsal a_sup_set_class a_wceq f1_equsal f2_equsal a_wal a_wi f2_equsal p_alrimi f1_equsal f2_equsal f3_equsal p_ax9o f1_equsal f2_equsal a_sup_set_class f3_equsal a_sup_set_class a_wceq f1_equsal f2_equsal a_wal a_wi f2_equsal a_wal p_impbii f2_equsal a_sup_set_class f3_equsal a_sup_set_class a_wceq f0_equsal a_wi f2_equsal a_wal f2_equsal a_sup_set_class f3_equsal a_sup_set_class a_wceq f1_equsal f2_equsal a_wal a_wi f2_equsal a_wal f1_equsal p_bitr4i $.
$}

$(A useful equivalence related to substitution.  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v ph ps x y  $.
	f0_equsalh $f wff ph $.
	f1_equsalh $f wff ps $.
	f2_equsalh $f set x $.
	f3_equsalh $f set y $.
	e0_equsalh $e |- ( ps -> A. x ps ) $.
	e1_equsalh $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_equsalh $p |- ( A. x ( x = y -> ph ) <-> ps ) $= e0_equsalh f1_equsalh f2_equsalh p_nfi e1_equsalh f0_equsalh f1_equsalh f2_equsalh f3_equsalh p_equsal $.
$}

$(A useful equivalence related to substitution.  (Contributed by NM,
       5-Aug-1993.)  (Revised by Mario Carneiro, 3-Oct-2016.) $)

${
	$v ph ps x y  $.
	f0_equsex $f wff ph $.
	f1_equsex $f wff ps $.
	f2_equsex $f set x $.
	f3_equsex $f set y $.
	e0_equsex $e |- F/ x ps $.
	e1_equsex $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_equsex $p |- ( E. x ( x = y /\ ph ) <-> ps ) $= f2_equsex a_sup_set_class f3_equsex a_sup_set_class a_wceq f0_equsex a_wn a_wi f2_equsex p_exnal f2_equsex a_sup_set_class f3_equsex a_sup_set_class a_wceq f0_equsex a_df-an f2_equsex a_sup_set_class f3_equsex a_sup_set_class a_wceq f0_equsex a_wa f2_equsex a_sup_set_class f3_equsex a_sup_set_class a_wceq f0_equsex a_wn a_wi a_wn f2_equsex p_exbii e0_equsex f1_equsex f2_equsex p_nfn e1_equsex f2_equsex a_sup_set_class f3_equsex a_sup_set_class a_wceq f0_equsex f1_equsex p_notbid f0_equsex a_wn f1_equsex a_wn f2_equsex f3_equsex p_equsal f2_equsex a_sup_set_class f3_equsex a_sup_set_class a_wceq f0_equsex a_wn a_wi f2_equsex a_wal f1_equsex p_con2bii f2_equsex a_sup_set_class f3_equsex a_sup_set_class a_wceq f0_equsex a_wn a_wi a_wn f2_equsex a_wex f2_equsex a_sup_set_class f3_equsex a_sup_set_class a_wceq f0_equsex a_wn a_wi f2_equsex a_wal a_wn f2_equsex a_sup_set_class f3_equsex a_sup_set_class a_wceq f0_equsex a_wa f2_equsex a_wex f1_equsex p_3bitr4i $.
$}

$(A useful equivalence related to substitution.  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v ph ps x y  $.
	f0_equsexh $f wff ph $.
	f1_equsexh $f wff ps $.
	f2_equsexh $f set x $.
	f3_equsexh $f set y $.
	e0_equsexh $e |- ( ps -> A. x ps ) $.
	e1_equsexh $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_equsexh $p |- ( E. x ( x = y /\ ph ) <-> ps ) $= e0_equsexh f1_equsexh f2_equsexh p_nfi e1_equsexh f0_equsexh f1_equsexh f2_equsexh f3_equsexh p_equsex $.
$}

$(Version of ~ dvelim without any variable restrictions.  (Contributed by
       NM, 1-Oct-2002.) $)

${
	$v ph ps x y z  $.
	f0_dvelimh $f wff ph $.
	f1_dvelimh $f wff ps $.
	f2_dvelimh $f set x $.
	f3_dvelimh $f set y $.
	f4_dvelimh $f set z $.
	e0_dvelimh $e |- ( ph -> A. x ph ) $.
	e1_dvelimh $e |- ( ps -> A. z ps ) $.
	e2_dvelimh $e |- ( z = y -> ( ph <-> ps ) ) $.
	p_dvelimh $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $= f4_dvelimh a_sup_set_class f3_dvelimh a_sup_set_class a_wceq f0_dvelimh a_wi f4_dvelimh p_hba1 f4_dvelimh a_sup_set_class f3_dvelimh a_sup_set_class a_wceq f0_dvelimh a_wi f4_dvelimh a_wal f4_dvelimh f2_dvelimh p_ax10o f4_dvelimh a_sup_set_class f3_dvelimh a_sup_set_class a_wceq f0_dvelimh a_wi f4_dvelimh a_wal f4_dvelimh a_wal f4_dvelimh a_sup_set_class f3_dvelimh a_sup_set_class a_wceq f0_dvelimh a_wi f4_dvelimh a_wal f2_dvelimh a_wal a_wi f4_dvelimh f2_dvelimh p_aecoms f4_dvelimh a_sup_set_class f3_dvelimh a_sup_set_class a_wceq f0_dvelimh a_wi f4_dvelimh a_wal f4_dvelimh a_sup_set_class f3_dvelimh a_sup_set_class a_wceq f0_dvelimh a_wi f4_dvelimh a_wal f4_dvelimh a_wal f2_dvelimh a_sup_set_class f4_dvelimh a_sup_set_class a_wceq f2_dvelimh a_wal f4_dvelimh a_sup_set_class f3_dvelimh a_sup_set_class a_wceq f0_dvelimh a_wi f4_dvelimh a_wal f2_dvelimh a_wal p_syl5 f2_dvelimh a_sup_set_class f4_dvelimh a_sup_set_class a_wceq f2_dvelimh a_wal f4_dvelimh a_sup_set_class f3_dvelimh a_sup_set_class a_wceq f0_dvelimh a_wi f4_dvelimh a_wal f4_dvelimh a_sup_set_class f3_dvelimh a_sup_set_class a_wceq f0_dvelimh a_wi f4_dvelimh a_wal f2_dvelimh a_wal a_wi f2_dvelimh a_sup_set_class f3_dvelimh a_sup_set_class a_wceq f2_dvelimh a_wal a_wn p_a1d f2_dvelimh f4_dvelimh f4_dvelimh p_hbnae f2_dvelimh f3_dvelimh f4_dvelimh p_hbnae f2_dvelimh a_sup_set_class f4_dvelimh a_sup_set_class a_wceq f2_dvelimh a_wal a_wn f2_dvelimh a_sup_set_class f3_dvelimh a_sup_set_class a_wceq f2_dvelimh a_wal a_wn f4_dvelimh p_hban f2_dvelimh f4_dvelimh f2_dvelimh p_hbnae f2_dvelimh f3_dvelimh f2_dvelimh p_hbnae f2_dvelimh a_sup_set_class f4_dvelimh a_sup_set_class a_wceq f2_dvelimh a_wal a_wn f2_dvelimh a_sup_set_class f3_dvelimh a_sup_set_class a_wceq f2_dvelimh a_wal a_wn f2_dvelimh p_hban f4_dvelimh f3_dvelimh f2_dvelimh p_ax12o f2_dvelimh a_sup_set_class f4_dvelimh a_sup_set_class a_wceq f2_dvelimh a_wal a_wn f2_dvelimh a_sup_set_class f3_dvelimh a_sup_set_class a_wceq f2_dvelimh a_wal a_wn f4_dvelimh a_sup_set_class f3_dvelimh a_sup_set_class a_wceq f4_dvelimh a_sup_set_class f3_dvelimh a_sup_set_class a_wceq f2_dvelimh a_wal a_wi p_imp e0_dvelimh f0_dvelimh f0_dvelimh f2_dvelimh a_wal a_wi f2_dvelimh a_sup_set_class f4_dvelimh a_sup_set_class a_wceq f2_dvelimh a_wal a_wn f2_dvelimh a_sup_set_class f3_dvelimh a_sup_set_class a_wceq f2_dvelimh a_wal a_wn a_wa p_a1i f2_dvelimh a_sup_set_class f4_dvelimh a_sup_set_class a_wceq f2_dvelimh a_wal a_wn f2_dvelimh a_sup_set_class f3_dvelimh a_sup_set_class a_wceq f2_dvelimh a_wal a_wn a_wa f4_dvelimh a_sup_set_class f3_dvelimh a_sup_set_class a_wceq f0_dvelimh f2_dvelimh p_hbimd f2_dvelimh a_sup_set_class f4_dvelimh a_sup_set_class a_wceq f2_dvelimh a_wal a_wn f2_dvelimh a_sup_set_class f3_dvelimh a_sup_set_class a_wceq f2_dvelimh a_wal a_wn a_wa f4_dvelimh a_sup_set_class f3_dvelimh a_sup_set_class a_wceq f0_dvelimh a_wi f2_dvelimh f4_dvelimh p_hbald f2_dvelimh a_sup_set_class f4_dvelimh a_sup_set_class a_wceq f2_dvelimh a_wal a_wn f2_dvelimh a_sup_set_class f3_dvelimh a_sup_set_class a_wceq f2_dvelimh a_wal a_wn f4_dvelimh a_sup_set_class f3_dvelimh a_sup_set_class a_wceq f0_dvelimh a_wi f4_dvelimh a_wal f4_dvelimh a_sup_set_class f3_dvelimh a_sup_set_class a_wceq f0_dvelimh a_wi f4_dvelimh a_wal f2_dvelimh a_wal a_wi p_ex f2_dvelimh a_sup_set_class f4_dvelimh a_sup_set_class a_wceq f2_dvelimh a_wal f2_dvelimh a_sup_set_class f3_dvelimh a_sup_set_class a_wceq f2_dvelimh a_wal a_wn f4_dvelimh a_sup_set_class f3_dvelimh a_sup_set_class a_wceq f0_dvelimh a_wi f4_dvelimh a_wal f4_dvelimh a_sup_set_class f3_dvelimh a_sup_set_class a_wceq f0_dvelimh a_wi f4_dvelimh a_wal f2_dvelimh a_wal a_wi a_wi p_pm2.61i e1_dvelimh e2_dvelimh f0_dvelimh f1_dvelimh f4_dvelimh f3_dvelimh p_equsalh e1_dvelimh e2_dvelimh f0_dvelimh f1_dvelimh f4_dvelimh f3_dvelimh p_equsalh f4_dvelimh a_sup_set_class f3_dvelimh a_sup_set_class a_wceq f0_dvelimh a_wi f4_dvelimh a_wal f1_dvelimh f2_dvelimh p_albii f2_dvelimh a_sup_set_class f3_dvelimh a_sup_set_class a_wceq f2_dvelimh a_wal a_wn f4_dvelimh a_sup_set_class f3_dvelimh a_sup_set_class a_wceq f0_dvelimh a_wi f4_dvelimh a_wal f4_dvelimh a_sup_set_class f3_dvelimh a_sup_set_class a_wceq f0_dvelimh a_wi f4_dvelimh a_wal f2_dvelimh a_wal f1_dvelimh f1_dvelimh f2_dvelimh a_wal p_3imtr3g $.
$}

$(Formula-building lemma for use with the Distinctor Reduction Theorem.
       Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).
       (Contributed by NM, 24-Nov-1994.) $)

${
	$v ph ps x y  $.
	f0_dral1 $f wff ph $.
	f1_dral1 $f wff ps $.
	f2_dral1 $f set x $.
	f3_dral1 $f set y $.
	e0_dral1 $e |- ( A. x x = y -> ( ph <-> ps ) ) $.
	p_dral1 $p |- ( A. x x = y -> ( A. x ph <-> A. y ps ) ) $= f2_dral1 f3_dral1 f2_dral1 p_hbae e0_dral1 f2_dral1 a_sup_set_class f3_dral1 a_sup_set_class a_wceq f2_dral1 a_wal f0_dral1 f1_dral1 p_biimpd f2_dral1 a_sup_set_class f3_dral1 a_sup_set_class a_wceq f2_dral1 a_wal f0_dral1 f1_dral1 f2_dral1 p_alimdh f1_dral1 f2_dral1 f3_dral1 p_ax10o f2_dral1 a_sup_set_class f3_dral1 a_sup_set_class a_wceq f2_dral1 a_wal f0_dral1 f2_dral1 a_wal f1_dral1 f2_dral1 a_wal f1_dral1 f3_dral1 a_wal p_syld f2_dral1 f3_dral1 f3_dral1 p_hbae e0_dral1 f2_dral1 a_sup_set_class f3_dral1 a_sup_set_class a_wceq f2_dral1 a_wal f0_dral1 f1_dral1 p_biimprd f2_dral1 a_sup_set_class f3_dral1 a_sup_set_class a_wceq f2_dral1 a_wal f1_dral1 f0_dral1 f3_dral1 p_alimdh f0_dral1 f3_dral1 f2_dral1 p_ax10o f0_dral1 f3_dral1 a_wal f0_dral1 f2_dral1 a_wal a_wi f3_dral1 f2_dral1 p_aecoms f2_dral1 a_sup_set_class f3_dral1 a_sup_set_class a_wceq f2_dral1 a_wal f1_dral1 f3_dral1 a_wal f0_dral1 f3_dral1 a_wal f0_dral1 f2_dral1 a_wal p_syld f2_dral1 a_sup_set_class f3_dral1 a_sup_set_class a_wceq f2_dral1 a_wal f0_dral1 f2_dral1 a_wal f1_dral1 f3_dral1 a_wal p_impbid $.
$}

$(Formula-building lemma for use with the Distinctor Reduction Theorem.
       Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).
       (Contributed by NM, 27-Feb-2005.) $)

${
	$v ph ps x y z  $.
	f0_dral2 $f wff ph $.
	f1_dral2 $f wff ps $.
	f2_dral2 $f set x $.
	f3_dral2 $f set y $.
	f4_dral2 $f set z $.
	e0_dral2 $e |- ( A. x x = y -> ( ph <-> ps ) ) $.
	p_dral2 $p |- ( A. x x = y -> ( A. z ph <-> A. z ps ) ) $= f2_dral2 f3_dral2 f4_dral2 p_hbae e0_dral2 f2_dral2 a_sup_set_class f3_dral2 a_sup_set_class a_wceq f2_dral2 a_wal f0_dral2 f1_dral2 f4_dral2 p_albidh $.
$}

$(Formula-building lemma for use with the Distinctor Reduction Theorem.
       Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).
       (Contributed by NM, 27-Feb-2005.) $)

${
	$v ph ps x y  $.
	f0_drex1 $f wff ph $.
	f1_drex1 $f wff ps $.
	f2_drex1 $f set x $.
	f3_drex1 $f set y $.
	e0_drex1 $e |- ( A. x x = y -> ( ph <-> ps ) ) $.
	p_drex1 $p |- ( A. x x = y -> ( E. x ph <-> E. y ps ) ) $= e0_drex1 f2_drex1 a_sup_set_class f3_drex1 a_sup_set_class a_wceq f2_drex1 a_wal f0_drex1 f1_drex1 p_notbid f0_drex1 a_wn f1_drex1 a_wn f2_drex1 f3_drex1 p_dral1 f2_drex1 a_sup_set_class f3_drex1 a_sup_set_class a_wceq f2_drex1 a_wal f0_drex1 a_wn f2_drex1 a_wal f1_drex1 a_wn f3_drex1 a_wal p_notbid f0_drex1 f2_drex1 a_df-ex f1_drex1 f3_drex1 a_df-ex f2_drex1 a_sup_set_class f3_drex1 a_sup_set_class a_wceq f2_drex1 a_wal f0_drex1 a_wn f2_drex1 a_wal a_wn f1_drex1 a_wn f3_drex1 a_wal a_wn f0_drex1 f2_drex1 a_wex f1_drex1 f3_drex1 a_wex p_3bitr4g $.
$}

$(Formula-building lemma for use with the Distinctor Reduction Theorem.
       Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).
       (Contributed by NM, 27-Feb-2005.) $)

${
	$v ph ps x y z  $.
	f0_drex2 $f wff ph $.
	f1_drex2 $f wff ps $.
	f2_drex2 $f set x $.
	f3_drex2 $f set y $.
	f4_drex2 $f set z $.
	e0_drex2 $e |- ( A. x x = y -> ( ph <-> ps ) ) $.
	p_drex2 $p |- ( A. x x = y -> ( E. z ph <-> E. z ps ) ) $= f2_drex2 f3_drex2 f4_drex2 p_hbae e0_drex2 f2_drex2 a_sup_set_class f3_drex2 a_sup_set_class a_wceq f2_drex2 a_wal f0_drex2 f1_drex2 f4_drex2 p_exbidh $.
$}

$(Formula-building lemma for use with the Distinctor Reduction Theorem.
       (Contributed by Mario Carneiro, 4-Oct-2016.) $)

${
	$v ph ps x y  $.
	f0_drnf1 $f wff ph $.
	f1_drnf1 $f wff ps $.
	f2_drnf1 $f set x $.
	f3_drnf1 $f set y $.
	e0_drnf1 $e |- ( A. x x = y -> ( ph <-> ps ) ) $.
	p_drnf1 $p |- ( A. x x = y -> ( F/ x ph <-> F/ y ps ) ) $= e0_drnf1 e0_drnf1 f0_drnf1 f1_drnf1 f2_drnf1 f3_drnf1 p_dral1 f2_drnf1 a_sup_set_class f3_drnf1 a_sup_set_class a_wceq f2_drnf1 a_wal f0_drnf1 f1_drnf1 f0_drnf1 f2_drnf1 a_wal f1_drnf1 f3_drnf1 a_wal p_imbi12d f0_drnf1 f0_drnf1 f2_drnf1 a_wal a_wi f1_drnf1 f1_drnf1 f3_drnf1 a_wal a_wi f2_drnf1 f3_drnf1 p_dral1 f0_drnf1 f2_drnf1 a_df-nf f1_drnf1 f3_drnf1 a_df-nf f2_drnf1 a_sup_set_class f3_drnf1 a_sup_set_class a_wceq f2_drnf1 a_wal f0_drnf1 f0_drnf1 f2_drnf1 a_wal a_wi f2_drnf1 a_wal f1_drnf1 f1_drnf1 f3_drnf1 a_wal a_wi f3_drnf1 a_wal f0_drnf1 f2_drnf1 a_wnf f1_drnf1 f3_drnf1 a_wnf p_3bitr4g $.
$}

$(Formula-building lemma for use with the Distinctor Reduction Theorem.
       (Contributed by Mario Carneiro, 4-Oct-2016.) $)

${
	$v ph ps x y z  $.
	f0_drnf2 $f wff ph $.
	f1_drnf2 $f wff ps $.
	f2_drnf2 $f set x $.
	f3_drnf2 $f set y $.
	f4_drnf2 $f set z $.
	e0_drnf2 $e |- ( A. x x = y -> ( ph <-> ps ) ) $.
	p_drnf2 $p |- ( A. x x = y -> ( F/ z ph <-> F/ z ps ) ) $= e0_drnf2 e0_drnf2 f0_drnf2 f1_drnf2 f2_drnf2 f3_drnf2 f4_drnf2 p_dral2 f2_drnf2 a_sup_set_class f3_drnf2 a_sup_set_class a_wceq f2_drnf2 a_wal f0_drnf2 f1_drnf2 f0_drnf2 f4_drnf2 a_wal f1_drnf2 f4_drnf2 a_wal p_imbi12d f0_drnf2 f0_drnf2 f4_drnf2 a_wal a_wi f1_drnf2 f1_drnf2 f4_drnf2 a_wal a_wi f2_drnf2 f3_drnf2 f4_drnf2 p_dral2 f0_drnf2 f4_drnf2 a_df-nf f1_drnf2 f4_drnf2 a_df-nf f2_drnf2 a_sup_set_class f3_drnf2 a_sup_set_class a_wceq f2_drnf2 a_wal f0_drnf2 f0_drnf2 f4_drnf2 a_wal a_wi f4_drnf2 a_wal f1_drnf2 f1_drnf2 f4_drnf2 a_wal a_wi f4_drnf2 a_wal f0_drnf2 f4_drnf2 a_wnf f1_drnf2 f4_drnf2 a_wnf p_3bitr4g $.
$}

$(Distribution of existential quantifiers, with a bound-variable
       hypothesis saying that ` y ` is not free in ` ph ` , but ` x ` can be
       free in ` ph ` (and there is no distinct variable condition on ` x ` and
       ` y ` ).  (Contributed by Mario Carneiro, 20-Mar-2013.) $)

${
	$v ph ps x y  $.
	f0_exdistrf $f wff ph $.
	f1_exdistrf $f wff ps $.
	f2_exdistrf $f set x $.
	f3_exdistrf $f set y $.
	e0_exdistrf $e |- ( -. A. x x = y -> F/ y ph ) $.
	p_exdistrf $p |- ( E. x E. y ( ph /\ ps ) -> E. x ( ph /\ E. y ps ) ) $= f2_exdistrf a_sup_set_class f3_exdistrf a_sup_set_class a_wceq f2_exdistrf a_wal f0_exdistrf f1_exdistrf a_wa p_biidd f0_exdistrf f1_exdistrf a_wa f0_exdistrf f1_exdistrf a_wa f2_exdistrf f3_exdistrf p_drex1 f0_exdistrf f1_exdistrf a_wa f2_exdistrf a_wex f0_exdistrf f1_exdistrf a_wa f3_exdistrf a_wex f2_exdistrf f3_exdistrf f2_exdistrf p_drex2 f0_exdistrf f1_exdistrf a_wa f2_exdistrf p_nfe1 f0_exdistrf f1_exdistrf a_wa f2_exdistrf a_wex f2_exdistrf p_19.9 f1_exdistrf f3_exdistrf p_19.8a f1_exdistrf f1_exdistrf f3_exdistrf a_wex f0_exdistrf p_anim2i f0_exdistrf f1_exdistrf a_wa f0_exdistrf f1_exdistrf f3_exdistrf a_wex a_wa f2_exdistrf p_eximi f0_exdistrf f1_exdistrf a_wa f2_exdistrf a_wex f2_exdistrf a_wex f0_exdistrf f1_exdistrf a_wa f2_exdistrf a_wex f0_exdistrf f1_exdistrf f3_exdistrf a_wex a_wa f2_exdistrf a_wex p_sylbi f2_exdistrf a_sup_set_class f3_exdistrf a_sup_set_class a_wceq f2_exdistrf a_wal f0_exdistrf f1_exdistrf a_wa f3_exdistrf a_wex f2_exdistrf a_wex f0_exdistrf f1_exdistrf a_wa f2_exdistrf a_wex f2_exdistrf a_wex f0_exdistrf f1_exdistrf f3_exdistrf a_wex a_wa f2_exdistrf a_wex p_syl6bir f2_exdistrf f3_exdistrf f2_exdistrf p_nfnae f0_exdistrf f1_exdistrf f3_exdistrf p_19.40 e0_exdistrf f0_exdistrf f2_exdistrf a_sup_set_class f3_exdistrf a_sup_set_class a_wceq f2_exdistrf a_wal a_wn f3_exdistrf p_19.9d f2_exdistrf a_sup_set_class f3_exdistrf a_sup_set_class a_wceq f2_exdistrf a_wal a_wn f0_exdistrf f3_exdistrf a_wex f0_exdistrf f1_exdistrf f3_exdistrf a_wex p_anim1d f0_exdistrf f1_exdistrf a_wa f3_exdistrf a_wex f0_exdistrf f3_exdistrf a_wex f1_exdistrf f3_exdistrf a_wex a_wa f2_exdistrf a_sup_set_class f3_exdistrf a_sup_set_class a_wceq f2_exdistrf a_wal a_wn f0_exdistrf f1_exdistrf f3_exdistrf a_wex a_wa p_syl5 f2_exdistrf a_sup_set_class f3_exdistrf a_sup_set_class a_wceq f2_exdistrf a_wal a_wn f0_exdistrf f1_exdistrf a_wa f3_exdistrf a_wex f0_exdistrf f1_exdistrf f3_exdistrf a_wex a_wa f2_exdistrf p_eximd f2_exdistrf a_sup_set_class f3_exdistrf a_sup_set_class a_wceq f2_exdistrf a_wal f0_exdistrf f1_exdistrf a_wa f3_exdistrf a_wex f2_exdistrf a_wex f0_exdistrf f1_exdistrf f3_exdistrf a_wex a_wa f2_exdistrf a_wex a_wi p_pm2.61i $.
$}

$(Variation on ~ nfald which adds the hypothesis that ` x ` and ` y ` are
       distinct in the inner subproof.  (Contributed by Mario Carneiro,
       8-Oct-2016.) $)

${
	$v ph ps x y  $.
	f0_nfald2 $f wff ph $.
	f1_nfald2 $f wff ps $.
	f2_nfald2 $f set x $.
	f3_nfald2 $f set y $.
	e0_nfald2 $e |- F/ y ph $.
	e1_nfald2 $e |- ( ( ph /\ -. A. x x = y ) -> F/ x ps ) $.
	p_nfald2 $p |- ( ph -> F/ x A. y ps ) $= e0_nfald2 f2_nfald2 f3_nfald2 f3_nfald2 p_nfnae f0_nfald2 f2_nfald2 a_sup_set_class f3_nfald2 a_sup_set_class a_wceq f2_nfald2 a_wal a_wn f3_nfald2 p_nfan e1_nfald2 f0_nfald2 f2_nfald2 a_sup_set_class f3_nfald2 a_sup_set_class a_wceq f2_nfald2 a_wal a_wn a_wa f1_nfald2 f2_nfald2 f3_nfald2 p_nfald f0_nfald2 f2_nfald2 a_sup_set_class f3_nfald2 a_sup_set_class a_wceq f2_nfald2 a_wal a_wn f1_nfald2 f3_nfald2 a_wal f2_nfald2 a_wnf p_ex f1_nfald2 f3_nfald2 p_nfa1 f2_nfald2 a_sup_set_class f3_nfald2 a_sup_set_class a_wceq f2_nfald2 a_wal f1_nfald2 f3_nfald2 a_wal p_biidd f1_nfald2 f3_nfald2 a_wal f1_nfald2 f3_nfald2 a_wal f2_nfald2 f3_nfald2 p_drnf1 f2_nfald2 a_sup_set_class f3_nfald2 a_sup_set_class a_wceq f2_nfald2 a_wal f1_nfald2 f3_nfald2 a_wal f2_nfald2 a_wnf f1_nfald2 f3_nfald2 a_wal f3_nfald2 a_wnf p_mpbiri f0_nfald2 f2_nfald2 a_sup_set_class f3_nfald2 a_sup_set_class a_wceq f2_nfald2 a_wal f1_nfald2 f3_nfald2 a_wal f2_nfald2 a_wnf p_pm2.61d2 $.
$}

$(Variation on ~ nfexd which adds the hypothesis that ` x ` and ` y ` are
       distinct in the inner subproof.  (Contributed by Mario Carneiro,
       8-Oct-2016.) $)

${
	$v ph ps x y  $.
	f0_nfexd2 $f wff ph $.
	f1_nfexd2 $f wff ps $.
	f2_nfexd2 $f set x $.
	f3_nfexd2 $f set y $.
	e0_nfexd2 $e |- F/ y ph $.
	e1_nfexd2 $e |- ( ( ph /\ -. A. x x = y ) -> F/ x ps ) $.
	p_nfexd2 $p |- ( ph -> F/ x E. y ps ) $= f1_nfexd2 f3_nfexd2 a_df-ex e0_nfexd2 e1_nfexd2 f0_nfexd2 f2_nfexd2 a_sup_set_class f3_nfexd2 a_sup_set_class a_wceq f2_nfexd2 a_wal a_wn a_wa f1_nfexd2 f2_nfexd2 p_nfnd f0_nfexd2 f1_nfexd2 a_wn f2_nfexd2 f3_nfexd2 p_nfald2 f0_nfexd2 f1_nfexd2 a_wn f3_nfexd2 a_wal f2_nfexd2 p_nfnd f1_nfexd2 f3_nfexd2 a_wex f1_nfexd2 a_wn f3_nfexd2 a_wal a_wn f0_nfexd2 f2_nfexd2 p_nfxfrd $.
$}

$(Closed theorem form of ~ spim .  (Contributed by NM, 15-Jan-2008.)
     (Revised by Mario Carneiro, 17-Oct-2016.) $)

${
	$v ph ps x y  $.
	f0_spimt $f wff ph $.
	f1_spimt $f wff ps $.
	f2_spimt $f set x $.
	f3_spimt $f set y $.
	p_spimt $p |- ( ( F/ x ps /\ A. x ( x = y -> ( ph -> ps ) ) ) -> ( A. x ph -> ps ) ) $= f1_spimt f2_spimt p_nfnf1 f0_spimt f2_spimt p_nfa1 f1_spimt f2_spimt a_wnf f0_spimt f2_spimt a_wal f2_spimt p_nfan f0_spimt f2_spimt p_sp f0_spimt f2_spimt a_wal f0_spimt f1_spimt f2_spimt a_wnf p_adantl f1_spimt f2_spimt p_nfr f1_spimt f2_spimt a_wnf f1_spimt f1_spimt f2_spimt a_wal a_wi f0_spimt f2_spimt a_wal p_adantr f1_spimt f2_spimt a_wnf f0_spimt f2_spimt a_wal a_wa f0_spimt f1_spimt f1_spimt f2_spimt a_wal p_embantd f1_spimt f2_spimt a_wnf f0_spimt f2_spimt a_wal a_wa f0_spimt f1_spimt a_wi f1_spimt f2_spimt a_wal f2_spimt a_sup_set_class f3_spimt a_sup_set_class a_wceq p_imim2d f1_spimt f2_spimt a_wnf f0_spimt f2_spimt a_wal a_wa f2_spimt a_sup_set_class f3_spimt a_sup_set_class a_wceq f0_spimt f1_spimt a_wi a_wi f2_spimt a_sup_set_class f3_spimt a_sup_set_class a_wceq f1_spimt f2_spimt a_wal a_wi f2_spimt p_alimd f1_spimt f2_spimt a_wnf f0_spimt f2_spimt a_wal f2_spimt a_sup_set_class f3_spimt a_sup_set_class a_wceq f0_spimt f1_spimt a_wi a_wi f2_spimt a_wal f2_spimt a_sup_set_class f3_spimt a_sup_set_class a_wceq f1_spimt f2_spimt a_wal a_wi f2_spimt a_wal p_impancom f1_spimt f2_spimt f3_spimt p_ax9o f1_spimt f2_spimt a_wnf f2_spimt a_sup_set_class f3_spimt a_sup_set_class a_wceq f0_spimt f1_spimt a_wi a_wi f2_spimt a_wal a_wa f0_spimt f2_spimt a_wal f2_spimt a_sup_set_class f3_spimt a_sup_set_class a_wceq f1_spimt f2_spimt a_wal a_wi f2_spimt a_wal f1_spimt p_syl6 $.
$}

$(Specialization, using implicit substitution.  Compare Lemma 14 of
       [Tarski] p. 70.  The ~ spim series of theorems requires that only one
       direction of the substitution hypothesis hold.  (Contributed by NM,
       5-Aug-1993.)  (Revised by Mario Carneiro, 3-Oct-2016.) $)

${
	$v ph ps x y  $.
	f0_spim $f wff ph $.
	f1_spim $f wff ps $.
	f2_spim $f set x $.
	f3_spim $f set y $.
	e0_spim $e |- F/ x ps $.
	e1_spim $e |- ( x = y -> ( ph -> ps ) ) $.
	p_spim $p |- ( A. x ph -> ps ) $= e0_spim e1_spim f2_spim a_sup_set_class f3_spim a_sup_set_class a_wceq f0_spim f1_spim a_wi a_wi f2_spim a_ax-gen f0_spim f1_spim f2_spim f3_spim p_spimt f1_spim f2_spim a_wnf f2_spim a_sup_set_class f3_spim a_sup_set_class a_wceq f0_spim f1_spim a_wi a_wi f2_spim a_wal f0_spim f2_spim a_wal f1_spim a_wi p_mp2an $.
$}

$(Existential introduction, using implicit substitution.  Compare Lemma 14
       of [Tarski] p. 70.  (Contributed by NM, 7-Aug-1994.)  (Revised by Mario
       Carneiro, 3-Oct-2016.) $)

${
	$v ph ps x y  $.
	f0_spime $f wff ph $.
	f1_spime $f wff ps $.
	f2_spime $f set x $.
	f3_spime $f set y $.
	e0_spime $e |- F/ x ph $.
	e1_spime $e |- ( x = y -> ( ph -> ps ) ) $.
	p_spime $p |- ( ph -> E. x ps ) $= e0_spime f0_spime f2_spime p_nfn e1_spime f2_spime a_sup_set_class f3_spime a_sup_set_class a_wceq f0_spime f1_spime p_con3d f1_spime a_wn f0_spime a_wn f2_spime f3_spime p_spim f1_spime a_wn f2_spime a_wal f0_spime p_con2i f1_spime f2_spime a_df-ex f0_spime f1_spime a_wn f2_spime a_wal a_wn f1_spime f2_spime a_wex p_sylibr $.
$}

$(Deduction version of ~ spime .  (Contributed by NM, 5-Aug-1993.)
       (Revised by Mario Carneiro, 3-Oct-2016.) $)

${
	$v ph ps ch x y  $.
	f0_spimed $f wff ph $.
	f1_spimed $f wff ps $.
	f2_spimed $f wff ch $.
	f3_spimed $f set x $.
	f4_spimed $f set y $.
	e0_spimed $e |- ( ch -> F/ x ph ) $.
	e1_spimed $e |- ( x = y -> ( ph -> ps ) ) $.
	p_spimed $p |- ( ch -> ( ph -> E. x ps ) ) $= e0_spimed f0_spimed f3_spimed p_nfnf1 f0_spimed f3_spimed a_wnf p_id f0_spimed f3_spimed a_wnf f0_spimed f3_spimed p_nfan1 e1_spimed f3_spimed a_sup_set_class f4_spimed a_sup_set_class a_wceq f0_spimed f1_spimed f0_spimed f3_spimed a_wnf p_adantld f0_spimed f3_spimed a_wnf f0_spimed a_wa f1_spimed f3_spimed f4_spimed p_spime f0_spimed f3_spimed a_wnf f0_spimed f1_spimed f3_spimed a_wex p_ex f2_spimed f0_spimed f3_spimed a_wnf f0_spimed f1_spimed f3_spimed a_wex a_wi p_syl $.
$}

$(Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps ch x y  $.
	f0_cbv1h $f wff ph $.
	f1_cbv1h $f wff ps $.
	f2_cbv1h $f wff ch $.
	f3_cbv1h $f set x $.
	f4_cbv1h $f set y $.
	e0_cbv1h $e |- ( ph -> ( ps -> A. y ps ) ) $.
	e1_cbv1h $e |- ( ph -> ( ch -> A. x ch ) ) $.
	e2_cbv1h $e |- ( ph -> ( x = y -> ( ps -> ch ) ) ) $.
	p_cbv1h $p |- ( A. x A. y ph -> ( A. x ps -> A. y ch ) ) $= e0_cbv1h f0_cbv1h f1_cbv1h f1_cbv1h f4_cbv1h a_wal a_wi f4_cbv1h p_sps f0_cbv1h f4_cbv1h a_wal f1_cbv1h f1_cbv1h f4_cbv1h a_wal f3_cbv1h p_al2imi f1_cbv1h f3_cbv1h f4_cbv1h a_ax-7 f0_cbv1h f4_cbv1h a_wal f3_cbv1h a_wal f1_cbv1h f3_cbv1h a_wal f1_cbv1h f4_cbv1h a_wal f3_cbv1h a_wal f1_cbv1h f3_cbv1h a_wal f4_cbv1h a_wal p_syl6 e2_cbv1h f0_cbv1h f3_cbv1h a_sup_set_class f4_cbv1h a_sup_set_class a_wceq f1_cbv1h f2_cbv1h p_com23 e1_cbv1h f0_cbv1h f1_cbv1h f3_cbv1h a_sup_set_class f4_cbv1h a_sup_set_class a_wceq f2_cbv1h f2_cbv1h f3_cbv1h a_wal p_syl6d f0_cbv1h f1_cbv1h f3_cbv1h a_sup_set_class f4_cbv1h a_sup_set_class a_wceq f2_cbv1h f3_cbv1h a_wal a_wi f3_cbv1h p_al2imi f2_cbv1h f3_cbv1h f4_cbv1h p_ax9o f0_cbv1h f3_cbv1h a_wal f1_cbv1h f3_cbv1h a_wal f3_cbv1h a_sup_set_class f4_cbv1h a_sup_set_class a_wceq f2_cbv1h f3_cbv1h a_wal a_wi f3_cbv1h a_wal f2_cbv1h p_syl6 f0_cbv1h f3_cbv1h a_wal f1_cbv1h f3_cbv1h a_wal f2_cbv1h f4_cbv1h p_al2imi f0_cbv1h f1_cbv1h f3_cbv1h a_wal f4_cbv1h a_wal f2_cbv1h f4_cbv1h a_wal a_wi f4_cbv1h f3_cbv1h p_a7s f0_cbv1h f4_cbv1h a_wal f3_cbv1h a_wal f1_cbv1h f3_cbv1h a_wal f1_cbv1h f3_cbv1h a_wal f4_cbv1h a_wal f2_cbv1h f4_cbv1h a_wal p_syld $.
$}

$(Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 5-Aug-1993.)  (Revised by Mario Carneiro,
       3-Oct-2016.) $)

${
	$v ph ps ch x y  $.
	f0_cbv1 $f wff ph $.
	f1_cbv1 $f wff ps $.
	f2_cbv1 $f wff ch $.
	f3_cbv1 $f set x $.
	f4_cbv1 $f set y $.
	e0_cbv1 $e |- ( ph -> F/ y ps ) $.
	e1_cbv1 $e |- ( ph -> F/ x ch ) $.
	e2_cbv1 $e |- ( ph -> ( x = y -> ( ps -> ch ) ) ) $.
	p_cbv1 $p |- ( A. x A. y ph -> ( A. x ps -> A. y ch ) ) $= e0_cbv1 f0_cbv1 f1_cbv1 f4_cbv1 p_nfrd e1_cbv1 f0_cbv1 f2_cbv1 f3_cbv1 p_nfrd e2_cbv1 f0_cbv1 f1_cbv1 f2_cbv1 f3_cbv1 f4_cbv1 p_cbv1h $.
$}

$(Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps ch x y  $.
	f0_cbv2h $f wff ph $.
	f1_cbv2h $f wff ps $.
	f2_cbv2h $f wff ch $.
	f3_cbv2h $f set x $.
	f4_cbv2h $f set y $.
	e0_cbv2h $e |- ( ph -> ( ps -> A. y ps ) ) $.
	e1_cbv2h $e |- ( ph -> ( ch -> A. x ch ) ) $.
	e2_cbv2h $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
	p_cbv2h $p |- ( A. x A. y ph -> ( A. x ps <-> A. y ch ) ) $= e0_cbv2h e1_cbv2h e2_cbv2h f1_cbv2h f2_cbv2h p_bi1 f0_cbv2h f3_cbv2h a_sup_set_class f4_cbv2h a_sup_set_class a_wceq f1_cbv2h f2_cbv2h a_wb f1_cbv2h f2_cbv2h a_wi p_syl6 f0_cbv2h f1_cbv2h f2_cbv2h f3_cbv2h f4_cbv2h p_cbv1h e1_cbv2h e0_cbv2h f4_cbv2h f3_cbv2h p_equcomi e2_cbv2h f1_cbv2h f2_cbv2h p_bi2 f4_cbv2h a_sup_set_class f3_cbv2h a_sup_set_class a_wceq f3_cbv2h a_sup_set_class f4_cbv2h a_sup_set_class a_wceq f0_cbv2h f1_cbv2h f2_cbv2h a_wb f2_cbv2h f1_cbv2h a_wi p_syl56 f0_cbv2h f2_cbv2h f1_cbv2h f4_cbv2h f3_cbv2h p_cbv1h f0_cbv2h f2_cbv2h f4_cbv2h a_wal f1_cbv2h f3_cbv2h a_wal a_wi f4_cbv2h f3_cbv2h p_a7s f0_cbv2h f4_cbv2h a_wal f3_cbv2h a_wal f1_cbv2h f3_cbv2h a_wal f2_cbv2h f4_cbv2h a_wal p_impbid $.
$}

$(Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 5-Aug-1993.)  (Revised by Mario Carneiro,
       3-Oct-2016.) $)

${
	$v ph ps ch x y  $.
	f0_cbv2 $f wff ph $.
	f1_cbv2 $f wff ps $.
	f2_cbv2 $f wff ch $.
	f3_cbv2 $f set x $.
	f4_cbv2 $f set y $.
	e0_cbv2 $e |- ( ph -> F/ y ps ) $.
	e1_cbv2 $e |- ( ph -> F/ x ch ) $.
	e2_cbv2 $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
	p_cbv2 $p |- ( A. x A. y ph -> ( A. x ps <-> A. y ch ) ) $= e0_cbv2 f0_cbv2 f1_cbv2 f4_cbv2 p_nfrd e1_cbv2 f0_cbv2 f2_cbv2 f3_cbv2 p_nfrd e2_cbv2 f0_cbv2 f1_cbv2 f2_cbv2 f3_cbv2 f4_cbv2 p_cbv2h $.
$}

$(Rule used to change bound variables, using implicit substitution, that
       does not use ~ ax-12o .  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps x y  $.
	f0_cbv3 $f wff ph $.
	f1_cbv3 $f wff ps $.
	f2_cbv3 $f set x $.
	f3_cbv3 $f set y $.
	e0_cbv3 $e |- F/ y ph $.
	e1_cbv3 $e |- F/ x ps $.
	e2_cbv3 $e |- ( x = y -> ( ph -> ps ) ) $.
	p_cbv3 $p |- ( A. x ph -> A. y ps ) $= e0_cbv3 f0_cbv3 f3_cbv3 a_wnf a_wtru p_a1i e1_cbv3 f1_cbv3 f2_cbv3 a_wnf a_wtru p_a1i e2_cbv3 f2_cbv3 a_sup_set_class f3_cbv3 a_sup_set_class a_wceq f0_cbv3 f1_cbv3 a_wi a_wi a_wtru p_a1i a_wtru f0_cbv3 f1_cbv3 f2_cbv3 f3_cbv3 p_cbv1 p_tru a_wtru f3_cbv3 a_ax-gen a_wtru f3_cbv3 a_wal f0_cbv3 f2_cbv3 a_wal f1_cbv3 f3_cbv3 a_wal a_wi f2_cbv3 p_mpg $.
$}

$(Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew Salmon,
       25-May-2011.)  (Proof modification is discouraged.) $)

${
	$v ph ps x y  $.
	f0_cbv3h $f wff ph $.
	f1_cbv3h $f wff ps $.
	f2_cbv3h $f set x $.
	f3_cbv3h $f set y $.
	e0_cbv3h $e |- ( ph -> A. y ph ) $.
	e1_cbv3h $e |- ( ps -> A. x ps ) $.
	e2_cbv3h $e |- ( x = y -> ( ph -> ps ) ) $.
	p_cbv3h $p |- ( A. x ph -> A. y ps ) $= e0_cbv3h f0_cbv3h f0_cbv3h f3_cbv3h a_wal a_wi f3_cbv3h a_sup_set_class f3_cbv3h a_sup_set_class a_wceq p_a1i e1_cbv3h f1_cbv3h f1_cbv3h f2_cbv3h a_wal a_wi f3_cbv3h a_sup_set_class f3_cbv3h a_sup_set_class a_wceq p_a1i e2_cbv3h f2_cbv3h a_sup_set_class f3_cbv3h a_sup_set_class a_wceq f0_cbv3h f1_cbv3h a_wi a_wi f3_cbv3h a_sup_set_class f3_cbv3h a_sup_set_class a_wceq p_a1i f3_cbv3h a_sup_set_class f3_cbv3h a_sup_set_class a_wceq f0_cbv3h f1_cbv3h f2_cbv3h f3_cbv3h p_cbv1h f3_cbv3h p_stdpc6 f3_cbv3h a_sup_set_class f3_cbv3h a_sup_set_class a_wceq f3_cbv3h a_wal f0_cbv3h f2_cbv3h a_wal f1_cbv3h f3_cbv3h a_wal a_wi f2_cbv3h p_mpg $.
$}

$(Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 5-Aug-1993.)  (Revised by Mario Carneiro,
       3-Oct-2016.) $)

${
	$v ph ps x y  $.
	f0_cbval $f wff ph $.
	f1_cbval $f wff ps $.
	f2_cbval $f set x $.
	f3_cbval $f set y $.
	e0_cbval $e |- F/ y ph $.
	e1_cbval $e |- F/ x ps $.
	e2_cbval $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_cbval $p |- ( A. x ph <-> A. y ps ) $= e0_cbval e1_cbval e2_cbval f2_cbval a_sup_set_class f3_cbval a_sup_set_class a_wceq f0_cbval f1_cbval p_biimpd f0_cbval f1_cbval f2_cbval f3_cbval p_cbv3 e1_cbval e0_cbval e2_cbval f2_cbval a_sup_set_class f3_cbval a_sup_set_class a_wceq f0_cbval f1_cbval p_biimprd f1_cbval f0_cbval a_wi f2_cbval f3_cbval p_equcoms f1_cbval f0_cbval f3_cbval f2_cbval p_cbv3 f0_cbval f2_cbval a_wal f1_cbval f3_cbval a_wal p_impbii $.
$}

$(Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps x y  $.
	f0_cbvex $f wff ph $.
	f1_cbvex $f wff ps $.
	f2_cbvex $f set x $.
	f3_cbvex $f set y $.
	e0_cbvex $e |- F/ y ph $.
	e1_cbvex $e |- F/ x ps $.
	e2_cbvex $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_cbvex $p |- ( E. x ph <-> E. y ps ) $= e0_cbvex f0_cbvex f3_cbvex p_nfn e1_cbvex f1_cbvex f2_cbvex p_nfn e2_cbvex f2_cbvex a_sup_set_class f3_cbvex a_sup_set_class a_wceq f0_cbvex f1_cbvex p_notbid f0_cbvex a_wn f1_cbvex a_wn f2_cbvex f3_cbvex p_cbval f0_cbvex a_wn f2_cbvex a_wal f1_cbvex a_wn f3_cbvex a_wal p_notbii f0_cbvex f2_cbvex a_df-ex f1_cbvex f3_cbvex a_df-ex f0_cbvex a_wn f2_cbvex a_wal a_wn f1_cbvex a_wn f3_cbvex a_wal a_wn f0_cbvex f2_cbvex a_wex f1_cbvex f3_cbvex a_wex p_3bitr4i $.
$}

$(Implicit substitution of ` y ` for ` x ` into a theorem.  (Contributed
       by Raph Levien, 9-Jul-2003.)  (Revised by Mario Carneiro,
       3-Oct-2016.) $)

${
	$v ph ps x y  $.
	f0_chvar $f wff ph $.
	f1_chvar $f wff ps $.
	f2_chvar $f set x $.
	f3_chvar $f set y $.
	e0_chvar $e |- F/ x ps $.
	e1_chvar $e |- ( x = y -> ( ph <-> ps ) ) $.
	e2_chvar $e |- ph $.
	p_chvar $p |- ps $= e0_chvar e1_chvar f2_chvar a_sup_set_class f3_chvar a_sup_set_class a_wceq f0_chvar f1_chvar p_biimpd f0_chvar f1_chvar f2_chvar f3_chvar p_spim e2_chvar f0_chvar f1_chvar f2_chvar p_mpg $.
$}

$(A variable introduction law for equality.  Lemma 15 of [Monk2] p. 109,
     however we do not require ` z ` to be distinct from ` x ` and ` y `
     (making the proof longer).  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Andrew Salmon, 25-May-2011.) $)

${
	$v x y z  $.
	f0_equvini $f set x $.
	f1_equvini $f set y $.
	f2_equvini $f set z $.
	p_equvini $p |- ( x = y -> E. z ( x = z /\ z = y ) ) $= f2_equvini f0_equvini p_equcomi f2_equvini a_sup_set_class f0_equvini a_sup_set_class a_wceq f0_equvini a_sup_set_class f2_equvini a_sup_set_class a_wceq f2_equvini p_alimi f2_equvini f1_equvini p_a9e f2_equvini a_sup_set_class f0_equvini a_sup_set_class a_wceq f2_equvini a_wal f0_equvini a_sup_set_class f2_equvini a_sup_set_class a_wceq f2_equvini a_wal f2_equvini a_sup_set_class f1_equvini a_sup_set_class a_wceq f2_equvini a_wex p_jctir f2_equvini a_sup_set_class f0_equvini a_sup_set_class a_wceq f2_equvini a_wal f0_equvini a_sup_set_class f2_equvini a_sup_set_class a_wceq f2_equvini a_wal f2_equvini a_sup_set_class f1_equvini a_sup_set_class a_wceq f2_equvini a_wex a_wa f0_equvini a_sup_set_class f1_equvini a_sup_set_class a_wceq p_a1d f0_equvini a_sup_set_class f2_equvini a_sup_set_class a_wceq f2_equvini a_sup_set_class f1_equvini a_sup_set_class a_wceq f2_equvini p_19.29 f2_equvini a_sup_set_class f0_equvini a_sup_set_class a_wceq f2_equvini a_wal f0_equvini a_sup_set_class f1_equvini a_sup_set_class a_wceq f0_equvini a_sup_set_class f2_equvini a_sup_set_class a_wceq f2_equvini a_wal f2_equvini a_sup_set_class f1_equvini a_sup_set_class a_wceq f2_equvini a_wex a_wa f0_equvini a_sup_set_class f2_equvini a_sup_set_class a_wceq f2_equvini a_sup_set_class f1_equvini a_sup_set_class a_wceq a_wa f2_equvini a_wex p_syl6 f2_equvini f0_equvini p_a9e f2_equvini f0_equvini p_equcomi f2_equvini a_sup_set_class f0_equvini a_sup_set_class a_wceq f0_equvini a_sup_set_class f2_equvini a_sup_set_class a_wceq f2_equvini p_eximi f2_equvini a_sup_set_class f0_equvini a_sup_set_class a_wceq f2_equvini a_wex f0_equvini a_sup_set_class f2_equvini a_sup_set_class a_wceq f2_equvini a_wex a_ax-mp f2_equvini a_sup_set_class f1_equvini a_sup_set_class a_wceq f2_equvini a_wal f0_equvini a_sup_set_class f1_equvini a_sup_set_class a_wceq f0_equvini a_sup_set_class f2_equvini a_sup_set_class a_wceq f2_equvini a_wex p_a1ii f2_equvini a_sup_set_class f1_equvini a_sup_set_class a_wceq f2_equvini a_wal f0_equvini a_sup_set_class f1_equvini a_sup_set_class a_wceq f0_equvini a_sup_set_class f2_equvini a_sup_set_class a_wceq f2_equvini a_wex p_anc2ri f0_equvini a_sup_set_class f2_equvini a_sup_set_class a_wceq f2_equvini a_sup_set_class f1_equvini a_sup_set_class a_wceq f2_equvini p_19.29r f2_equvini a_sup_set_class f1_equvini a_sup_set_class a_wceq f2_equvini a_wal f0_equvini a_sup_set_class f1_equvini a_sup_set_class a_wceq f0_equvini a_sup_set_class f2_equvini a_sup_set_class a_wceq f2_equvini a_wex f2_equvini a_sup_set_class f1_equvini a_sup_set_class a_wceq f2_equvini a_wal a_wa f0_equvini a_sup_set_class f2_equvini a_sup_set_class a_wceq f2_equvini a_sup_set_class f1_equvini a_sup_set_class a_wceq a_wa f2_equvini a_wex p_syl6 f2_equvini a_sup_set_class f0_equvini a_sup_set_class a_wceq f2_equvini a_wal f2_equvini a_sup_set_class f1_equvini a_sup_set_class a_wceq f2_equvini a_wal p_ioran f0_equvini f1_equvini f2_equvini p_nfeqf f0_equvini f2_equvini f1_equvini a_ax-8 f0_equvini a_sup_set_class f2_equvini a_sup_set_class a_wceq f0_equvini a_sup_set_class f1_equvini a_sup_set_class a_wceq f2_equvini a_sup_set_class f1_equvini a_sup_set_class a_wceq p_anc2li f0_equvini a_sup_set_class f1_equvini a_sup_set_class a_wceq f0_equvini a_sup_set_class f2_equvini a_sup_set_class a_wceq f2_equvini a_sup_set_class f1_equvini a_sup_set_class a_wceq a_wa a_wi f0_equvini f2_equvini p_equcoms f0_equvini a_sup_set_class f1_equvini a_sup_set_class a_wceq f0_equvini a_sup_set_class f2_equvini a_sup_set_class a_wceq f2_equvini a_sup_set_class f1_equvini a_sup_set_class a_wceq a_wa f2_equvini a_sup_set_class f0_equvini a_sup_set_class a_wceq f2_equvini a_wal a_wn f2_equvini a_sup_set_class f1_equvini a_sup_set_class a_wceq f2_equvini a_wal a_wn a_wa f2_equvini f0_equvini p_spimed f2_equvini a_sup_set_class f0_equvini a_sup_set_class a_wceq f2_equvini a_wal f2_equvini a_sup_set_class f1_equvini a_sup_set_class a_wceq f2_equvini a_wal a_wo a_wn f2_equvini a_sup_set_class f0_equvini a_sup_set_class a_wceq f2_equvini a_wal a_wn f2_equvini a_sup_set_class f1_equvini a_sup_set_class a_wceq f2_equvini a_wal a_wn a_wa f0_equvini a_sup_set_class f1_equvini a_sup_set_class a_wceq f0_equvini a_sup_set_class f2_equvini a_sup_set_class a_wceq f2_equvini a_sup_set_class f1_equvini a_sup_set_class a_wceq a_wa f2_equvini a_wex a_wi p_sylbi f2_equvini a_sup_set_class f0_equvini a_sup_set_class a_wceq f2_equvini a_wal f2_equvini a_sup_set_class f1_equvini a_sup_set_class a_wceq f2_equvini a_wal f0_equvini a_sup_set_class f1_equvini a_sup_set_class a_wceq f0_equvini a_sup_set_class f2_equvini a_sup_set_class a_wceq f2_equvini a_sup_set_class f1_equvini a_sup_set_class a_wceq a_wa f2_equvini a_wex a_wi p_ecase3 $.
$}

$(A variable elimination law for equality with no distinct variable
     requirements.  (Compare ~ equvini .)  (Contributed by NM, 1-Mar-2013.)
     (Proof shortened by Mario Carneiro, 17-Oct-2016.) $)

${
	$v x y z  $.
	f0_equveli $f set x $.
	f1_equveli $f set y $.
	f2_equveli $f set z $.
	p_equveli $p |- ( A. z ( z = x <-> z = y ) -> x = y ) $= f2_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq f2_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq f2_equveli p_albiim f2_equveli f1_equveli f1_equveli p_equequ1 f2_equveli f1_equveli f0_equveli p_equequ1 f2_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq f2_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq f1_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq f2_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq f1_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq p_imbi12d f2_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq f2_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq f2_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq a_wi f1_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq f1_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq a_wi a_wb f2_equveli p_sps f2_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq f2_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq a_wi f1_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq f1_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq a_wi f2_equveli f1_equveli p_dral1 f1_equveli p_equid f1_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq f1_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq a_wi f1_equveli p_sp f1_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq f1_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq a_wi f1_equveli a_wal f1_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq f1_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq p_mpi f1_equveli f0_equveli p_equcomi f1_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq f1_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq a_wi f1_equveli a_wal f1_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq f0_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq p_syl f2_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq f2_equveli a_wal f2_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq f2_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq a_wi f2_equveli a_wal f1_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq f1_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq a_wi f1_equveli a_wal f0_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq p_syl6bi f2_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq f2_equveli a_wal f2_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq f2_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq a_wi f2_equveli a_wal f0_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq f2_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq f2_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq a_wi f2_equveli a_wal p_adantld f2_equveli f0_equveli f0_equveli p_equequ1 f2_equveli f0_equveli f1_equveli p_equequ1 f2_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq f2_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq f0_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq f2_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq f0_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq p_imbi12d f2_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq f2_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq f2_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq a_wi f0_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq f0_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq a_wi a_wb f2_equveli p_sps f2_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq f2_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq a_wi f0_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq f0_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq a_wi f2_equveli f0_equveli f2_equveli p_dral2 f0_equveli p_equid f0_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq f0_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq p_a1bi f0_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq f0_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq f0_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq a_wi p_biimpri f0_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq f0_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq a_wi f0_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq f2_equveli p_sps f2_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq f2_equveli a_wal f2_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq f2_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq a_wi f2_equveli a_wal f0_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq f0_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq a_wi f2_equveli a_wal f0_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq p_syl6bi f2_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq f2_equveli a_wal f2_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq f2_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq a_wi f2_equveli a_wal f0_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq a_wi f2_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq f2_equveli a_wal a_wn p_a1d f0_equveli f1_equveli f2_equveli p_nfeqf f0_equveli p_equid f2_equveli f0_equveli f0_equveli p_equtr f2_equveli f0_equveli f1_equveli a_ax-8 f2_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq f0_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq f2_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq f2_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq f0_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq p_imim12d f2_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq f2_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq f2_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq a_wi f0_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq f0_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq p_mpii f2_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq f2_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq f2_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq a_wi f0_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq a_wi a_wi f2_equveli a_ax-gen f2_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq f2_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq a_wi f0_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq f2_equveli f0_equveli p_spimt f2_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq f2_equveli a_wal a_wn f2_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq f2_equveli a_wal a_wn a_wa f0_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq f2_equveli a_wnf f2_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq f2_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq f2_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq a_wi f0_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq a_wi a_wi f2_equveli a_wal f2_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq f2_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq a_wi f2_equveli a_wal f0_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq a_wi p_sylancl f2_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq f2_equveli a_wal a_wn f2_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq f2_equveli a_wal a_wn f2_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq f2_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq a_wi f2_equveli a_wal f0_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq a_wi p_ex f2_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq f2_equveli a_wal f2_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq f2_equveli a_wal a_wn f2_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq f2_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq a_wi f2_equveli a_wal f0_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq a_wi a_wi p_pm2.61i f2_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq f2_equveli a_wal a_wn f2_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq f2_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq a_wi f2_equveli a_wal f0_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq f2_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq f2_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq a_wi f2_equveli a_wal p_adantrd f2_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq f2_equveli a_wal f2_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq f2_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq a_wi f2_equveli a_wal f2_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq f2_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq a_wi f2_equveli a_wal a_wa f0_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq a_wi p_pm2.61i f2_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq f2_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq a_wb f2_equveli a_wal f2_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq f2_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq a_wi f2_equveli a_wal f2_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq f2_equveli a_sup_set_class f0_equveli a_sup_set_class a_wceq a_wi f2_equveli a_wal a_wa f0_equveli a_sup_set_class f1_equveli a_sup_set_class a_wceq p_sylbi $.
$}

$(Two ways of expressing substitution when ` y ` is not free in ` ph ` .
       (Contributed by NM, 25-Apr-2008.)  (Revised by Mario Carneiro,
       4-Oct-2016.) $)

${
	$v ph x y  $.
	f0_equs45f $f wff ph $.
	f1_equs45f $f set x $.
	f2_equs45f $f set y $.
	e0_equs45f $e |- F/ y ph $.
	p_equs45f $p |- ( E. x ( x = y /\ ph ) <-> A. x ( x = y -> ph ) ) $= e0_equs45f f0_equs45f f2_equs45f p_nfri f0_equs45f f0_equs45f f2_equs45f a_wal f1_equs45f a_sup_set_class f2_equs45f a_sup_set_class a_wceq p_anim2i f1_equs45f a_sup_set_class f2_equs45f a_sup_set_class a_wceq f0_equs45f a_wa f1_equs45f a_sup_set_class f2_equs45f a_sup_set_class a_wceq f0_equs45f f2_equs45f a_wal a_wa f1_equs45f p_eximi f0_equs45f f1_equs45f f2_equs45f p_equs5a f1_equs45f a_sup_set_class f2_equs45f a_sup_set_class a_wceq f0_equs45f a_wa f1_equs45f a_wex f1_equs45f a_sup_set_class f2_equs45f a_sup_set_class a_wceq f0_equs45f f2_equs45f a_wal a_wa f1_equs45f a_wex f1_equs45f a_sup_set_class f2_equs45f a_sup_set_class a_wceq f0_equs45f a_wi f1_equs45f a_wal p_syl f0_equs45f f1_equs45f f2_equs45f p_equs4 f1_equs45f a_sup_set_class f2_equs45f a_sup_set_class a_wceq f0_equs45f a_wa f1_equs45f a_wex f1_equs45f a_sup_set_class f2_equs45f a_sup_set_class a_wceq f0_equs45f a_wi f1_equs45f a_wal p_impbii $.
$}

$(A version of ~ spim with a distinct variable requirement instead of a
       bound variable hypothesis.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps x y  $.
	$d x ps  $.
	f0_spimv $f wff ph $.
	f1_spimv $f wff ps $.
	f2_spimv $f set x $.
	f3_spimv $f set y $.
	e0_spimv $e |- ( x = y -> ( ph -> ps ) ) $.
	p_spimv $p |- ( A. x ph -> ps ) $= f1_spimv f2_spimv p_nfv e0_spimv f0_spimv f1_spimv f2_spimv f3_spimv p_spim $.
$}

$(A "distinctor elimination" lemma with no restrictions on variables in
       the consequent.  (Contributed by NM, 8-Nov-2006.) $)

${
	$v x y z w v  $.
	$d u v  $.
	$d u x y  $.
	$d u w  $.
	f0_aev $f set x $.
	f1_aev $f set y $.
	f2_aev $f set z $.
	f3_aev $f set w $.
	f4_aev $f set v $.
	i0_aev $f set u $.
	p_aev $p |- ( A. x x = y -> A. z w = v ) $= f0_aev f1_aev f2_aev p_hbae f4_aev i0_aev f0_aev f1_aev p_ax10lem5 i0_aev f3_aev f4_aev a_ax-8 i0_aev a_sup_set_class f4_aev a_sup_set_class a_wceq f3_aev a_sup_set_class f4_aev a_sup_set_class a_wceq i0_aev f3_aev p_spimv f0_aev a_sup_set_class f1_aev a_sup_set_class a_wceq f0_aev a_wal i0_aev a_sup_set_class f4_aev a_sup_set_class a_wceq i0_aev a_wal f3_aev a_sup_set_class f4_aev a_sup_set_class a_wceq p_syl f0_aev a_sup_set_class f1_aev a_sup_set_class a_wceq f0_aev a_wal f3_aev a_sup_set_class f4_aev a_sup_set_class a_wceq f2_aev p_alrimih $.
$}

$(Recovery of ~ ax-11o from ~ ax11v .  This proof uses ~ ax-10 and
       ~ ax-11 .  TODO: figure out if this is useful, or if it should be
       simplified or eliminated.  (Contributed by NM, 2-Feb-2007.) $)

${
	$v ph x y z  $.
	$d x z  $.
	$d y z  $.
	$d z ph  $.
	f0_ax11v2 $f wff ph $.
	f1_ax11v2 $f set x $.
	f2_ax11v2 $f set y $.
	f3_ax11v2 $f set z $.
	e0_ax11v2 $e |- ( x = z -> ( ph -> A. x ( x = z -> ph ) ) ) $.
	p_ax11v2 $p |- ( -. A. x x = y -> ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $= f3_ax11v2 f2_ax11v2 p_a9ev e0_ax11v2 f3_ax11v2 f2_ax11v2 f1_ax11v2 p_equequ2 f3_ax11v2 a_sup_set_class f2_ax11v2 a_sup_set_class a_wceq f1_ax11v2 a_sup_set_class f3_ax11v2 a_sup_set_class a_wceq f1_ax11v2 a_sup_set_class f2_ax11v2 a_sup_set_class a_wceq a_wb f1_ax11v2 a_sup_set_class f2_ax11v2 a_sup_set_class a_wceq f1_ax11v2 a_wal a_wn p_adantl f1_ax11v2 f2_ax11v2 f3_ax11v2 p_dveeq2 f1_ax11v2 a_sup_set_class f2_ax11v2 a_sup_set_class a_wceq f1_ax11v2 a_wal a_wn f3_ax11v2 a_sup_set_class f2_ax11v2 a_sup_set_class a_wceq f3_ax11v2 a_sup_set_class f2_ax11v2 a_sup_set_class a_wceq f1_ax11v2 a_wal p_imp f3_ax11v2 a_sup_set_class f2_ax11v2 a_sup_set_class a_wceq f1_ax11v2 p_nfa1 f3_ax11v2 f2_ax11v2 f1_ax11v2 p_equequ2 f3_ax11v2 a_sup_set_class f2_ax11v2 a_sup_set_class a_wceq f1_ax11v2 a_sup_set_class f3_ax11v2 a_sup_set_class a_wceq f1_ax11v2 a_sup_set_class f2_ax11v2 a_sup_set_class a_wceq f0_ax11v2 p_imbi1d f3_ax11v2 a_sup_set_class f2_ax11v2 a_sup_set_class a_wceq f1_ax11v2 a_sup_set_class f3_ax11v2 a_sup_set_class a_wceq f0_ax11v2 a_wi f1_ax11v2 a_sup_set_class f2_ax11v2 a_sup_set_class a_wceq f0_ax11v2 a_wi a_wb f1_ax11v2 p_sps f3_ax11v2 a_sup_set_class f2_ax11v2 a_sup_set_class a_wceq f1_ax11v2 a_wal f1_ax11v2 a_sup_set_class f3_ax11v2 a_sup_set_class a_wceq f0_ax11v2 a_wi f1_ax11v2 a_sup_set_class f2_ax11v2 a_sup_set_class a_wceq f0_ax11v2 a_wi f1_ax11v2 p_albid f1_ax11v2 a_sup_set_class f2_ax11v2 a_sup_set_class a_wceq f1_ax11v2 a_wal a_wn f3_ax11v2 a_sup_set_class f2_ax11v2 a_sup_set_class a_wceq a_wa f3_ax11v2 a_sup_set_class f2_ax11v2 a_sup_set_class a_wceq f1_ax11v2 a_wal f1_ax11v2 a_sup_set_class f3_ax11v2 a_sup_set_class a_wceq f0_ax11v2 a_wi f1_ax11v2 a_wal f1_ax11v2 a_sup_set_class f2_ax11v2 a_sup_set_class a_wceq f0_ax11v2 a_wi f1_ax11v2 a_wal a_wb p_syl f1_ax11v2 a_sup_set_class f2_ax11v2 a_sup_set_class a_wceq f1_ax11v2 a_wal a_wn f3_ax11v2 a_sup_set_class f2_ax11v2 a_sup_set_class a_wceq a_wa f1_ax11v2 a_sup_set_class f3_ax11v2 a_sup_set_class a_wceq f0_ax11v2 a_wi f1_ax11v2 a_wal f1_ax11v2 a_sup_set_class f2_ax11v2 a_sup_set_class a_wceq f0_ax11v2 a_wi f1_ax11v2 a_wal f0_ax11v2 p_imbi2d f1_ax11v2 a_sup_set_class f2_ax11v2 a_sup_set_class a_wceq f1_ax11v2 a_wal a_wn f3_ax11v2 a_sup_set_class f2_ax11v2 a_sup_set_class a_wceq a_wa f1_ax11v2 a_sup_set_class f3_ax11v2 a_sup_set_class a_wceq f1_ax11v2 a_sup_set_class f2_ax11v2 a_sup_set_class a_wceq f0_ax11v2 f1_ax11v2 a_sup_set_class f3_ax11v2 a_sup_set_class a_wceq f0_ax11v2 a_wi f1_ax11v2 a_wal a_wi f0_ax11v2 f1_ax11v2 a_sup_set_class f2_ax11v2 a_sup_set_class a_wceq f0_ax11v2 a_wi f1_ax11v2 a_wal a_wi p_imbi12d f1_ax11v2 a_sup_set_class f2_ax11v2 a_sup_set_class a_wceq f1_ax11v2 a_wal a_wn f3_ax11v2 a_sup_set_class f2_ax11v2 a_sup_set_class a_wceq a_wa f1_ax11v2 a_sup_set_class f3_ax11v2 a_sup_set_class a_wceq f0_ax11v2 f1_ax11v2 a_sup_set_class f3_ax11v2 a_sup_set_class a_wceq f0_ax11v2 a_wi f1_ax11v2 a_wal a_wi a_wi f1_ax11v2 a_sup_set_class f2_ax11v2 a_sup_set_class a_wceq f0_ax11v2 f1_ax11v2 a_sup_set_class f2_ax11v2 a_sup_set_class a_wceq f0_ax11v2 a_wi f1_ax11v2 a_wal a_wi a_wi p_mpbii f1_ax11v2 a_sup_set_class f2_ax11v2 a_sup_set_class a_wceq f1_ax11v2 a_wal a_wn f3_ax11v2 a_sup_set_class f2_ax11v2 a_sup_set_class a_wceq f1_ax11v2 a_sup_set_class f2_ax11v2 a_sup_set_class a_wceq f0_ax11v2 f1_ax11v2 a_sup_set_class f2_ax11v2 a_sup_set_class a_wceq f0_ax11v2 a_wi f1_ax11v2 a_wal a_wi a_wi p_ex f1_ax11v2 a_sup_set_class f2_ax11v2 a_sup_set_class a_wceq f1_ax11v2 a_wal a_wn f3_ax11v2 a_sup_set_class f2_ax11v2 a_sup_set_class a_wceq f1_ax11v2 a_sup_set_class f2_ax11v2 a_sup_set_class a_wceq f0_ax11v2 f1_ax11v2 a_sup_set_class f2_ax11v2 a_sup_set_class a_wceq f0_ax11v2 a_wi f1_ax11v2 a_wal a_wi a_wi f3_ax11v2 p_exlimdv f1_ax11v2 a_sup_set_class f2_ax11v2 a_sup_set_class a_wceq f1_ax11v2 a_wal a_wn f3_ax11v2 a_sup_set_class f2_ax11v2 a_sup_set_class a_wceq f3_ax11v2 a_wex f1_ax11v2 a_sup_set_class f2_ax11v2 a_sup_set_class a_wceq f0_ax11v2 f1_ax11v2 a_sup_set_class f2_ax11v2 a_sup_set_class a_wceq f0_ax11v2 a_wi f1_ax11v2 a_wal a_wi a_wi p_mpi $.
$}

$(Derive ~ ax-11o from a hypothesis in the form of ~ ax-11 . ~ ax-10 and
       ~ ax-11 are used by the proof, but not ~ ax-10o or ~ ax-11o .  TODO:
       figure out if this is useful, or if it should be simplified or
       eliminated.  (Contributed by NM, 2-Feb-2007.) $)

${
	$v ph x y z  $.
	$d x z  $.
	$d y z  $.
	$d z ph  $.
	f0_ax11a2 $f wff ph $.
	f1_ax11a2 $f set x $.
	f2_ax11a2 $f set y $.
	f3_ax11a2 $f set z $.
	e0_ax11a2 $e |- ( x = z -> ( A. z ph -> A. x ( x = z -> ph ) ) ) $.
	p_ax11a2 $p |- ( -. A. x x = y -> ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $= f0_ax11a2 f3_ax11a2 a_ax-17 e0_ax11a2 f0_ax11a2 f0_ax11a2 f3_ax11a2 a_wal f1_ax11a2 a_sup_set_class f3_ax11a2 a_sup_set_class a_wceq f1_ax11a2 a_sup_set_class f3_ax11a2 a_sup_set_class a_wceq f0_ax11a2 a_wi f1_ax11a2 a_wal p_syl5 f0_ax11a2 f1_ax11a2 f2_ax11a2 f3_ax11a2 p_ax11v2 $.
$}

$(Derivation of set.mm's original ~ ax-11o from ~ ax-10 and the shorter
       ~ ax-11 that has replaced it.

       An open problem is whether this theorem can be proved without relying on
       ~ ax-16 or ~ ax-17 (given all of the original and new versions of ~ sp
       through ~ ax-15 ).

       Another open problem is whether this theorem can be proved without
       relying on ~ ax12o .

       Theorem ~ ax11 shows the reverse derivation of ~ ax-11 from ~ ax-11o .

       Normally, ~ ax11o should be used rather than ~ ax-11o , except by
       theorems specifically studying the latter's properties.  (Contributed by
       NM, 3-Feb-2007.) $)

${
	$v ph x y  $.
	$d x z  $.
	$d y z  $.
	$d z ph  $.
	f0_ax11o $f wff ph $.
	f1_ax11o $f set x $.
	f2_ax11o $f set y $.
	i0_ax11o $f set z $.
	p_ax11o $p |- ( -. A. x x = y -> ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $= f0_ax11o f1_ax11o i0_ax11o a_ax-11 f0_ax11o f1_ax11o f2_ax11o i0_ax11o p_ax11a2 $.
$}

$(A bidirectional version of ~ ax11o .  (Contributed by NM, 30-Jun-2006.) $)

${
	$v ph x y  $.
	f0_ax11b $f wff ph $.
	f1_ax11b $f set x $.
	f2_ax11b $f set y $.
	p_ax11b $p |- ( ( -. A. x x = y /\ x = y ) -> ( ph <-> A. x ( x = y -> ph ) ) ) $= f0_ax11b f1_ax11b f2_ax11b p_ax11o f1_ax11b a_sup_set_class f2_ax11b a_sup_set_class a_wceq f1_ax11b a_wal a_wn f1_ax11b a_sup_set_class f2_ax11b a_sup_set_class a_wceq f0_ax11b f1_ax11b a_sup_set_class f2_ax11b a_sup_set_class a_wceq f0_ax11b a_wi f1_ax11b a_wal a_wi p_imp f1_ax11b a_sup_set_class f2_ax11b a_sup_set_class a_wceq f0_ax11b a_wi f1_ax11b p_sp f1_ax11b a_sup_set_class f2_ax11b a_sup_set_class a_wceq f0_ax11b a_wi f1_ax11b a_wal f1_ax11b a_sup_set_class f2_ax11b a_sup_set_class a_wceq f0_ax11b p_com12 f1_ax11b a_sup_set_class f2_ax11b a_sup_set_class a_wceq f1_ax11b a_sup_set_class f2_ax11b a_sup_set_class a_wceq f0_ax11b a_wi f1_ax11b a_wal f0_ax11b a_wi f1_ax11b a_sup_set_class f2_ax11b a_sup_set_class a_wceq f1_ax11b a_wal a_wn p_adantl f1_ax11b a_sup_set_class f2_ax11b a_sup_set_class a_wceq f1_ax11b a_wal a_wn f1_ax11b a_sup_set_class f2_ax11b a_sup_set_class a_wceq a_wa f0_ax11b f1_ax11b a_sup_set_class f2_ax11b a_sup_set_class a_wceq f0_ax11b a_wi f1_ax11b a_wal p_impbid $.
$}

$(Lemma used in proofs of substitution properties.  (Contributed by NM,
     5-Aug-1993.) $)

${
	$v ph x y  $.
	f0_equs5 $f wff ph $.
	f1_equs5 $f set x $.
	f2_equs5 $f set y $.
	p_equs5 $p |- ( -. A. x x = y -> ( E. x ( x = y /\ ph ) -> A. x ( x = y -> ph ) ) ) $= f1_equs5 f2_equs5 f1_equs5 p_nfnae f1_equs5 a_sup_set_class f2_equs5 a_sup_set_class a_wceq f0_equs5 a_wi f1_equs5 p_nfa1 f0_equs5 f1_equs5 f2_equs5 p_ax11o f1_equs5 a_sup_set_class f2_equs5 a_sup_set_class a_wceq f1_equs5 a_wal a_wn f1_equs5 a_sup_set_class f2_equs5 a_sup_set_class a_wceq f0_equs5 f1_equs5 a_sup_set_class f2_equs5 a_sup_set_class a_wceq f0_equs5 a_wi f1_equs5 a_wal p_imp3a f1_equs5 a_sup_set_class f2_equs5 a_sup_set_class a_wceq f1_equs5 a_wal a_wn f1_equs5 a_sup_set_class f2_equs5 a_sup_set_class a_wceq f0_equs5 a_wa f1_equs5 a_sup_set_class f2_equs5 a_sup_set_class a_wceq f0_equs5 a_wi f1_equs5 a_wal f1_equs5 p_exlimd $.
$}

$(Version of ~ dvelimv without any variable restrictions.  (Contributed by
       NM, 1-Oct-2002.)  (Revised by Mario Carneiro, 6-Oct-2016.) $)

${
	$v ph ps x y z  $.
	f0_dvelimf $f wff ph $.
	f1_dvelimf $f wff ps $.
	f2_dvelimf $f set x $.
	f3_dvelimf $f set y $.
	f4_dvelimf $f set z $.
	e0_dvelimf $e |- F/ x ph $.
	e1_dvelimf $e |- F/ z ps $.
	e2_dvelimf $e |- ( z = y -> ( ph <-> ps ) ) $.
	p_dvelimf $p |- ( -. A. x x = y -> F/ x ps ) $= e1_dvelimf e2_dvelimf f0_dvelimf f1_dvelimf f4_dvelimf f3_dvelimf p_equsal f4_dvelimf a_sup_set_class f3_dvelimf a_sup_set_class a_wceq f0_dvelimf a_wi f4_dvelimf a_wal f1_dvelimf p_bicomi f2_dvelimf f3_dvelimf f4_dvelimf p_nfnae f2_dvelimf f3_dvelimf f2_dvelimf p_nfnae f2_dvelimf f4_dvelimf f2_dvelimf p_nfnae f2_dvelimf a_sup_set_class f3_dvelimf a_sup_set_class a_wceq f2_dvelimf a_wal a_wn f2_dvelimf a_sup_set_class f4_dvelimf a_sup_set_class a_wceq f2_dvelimf a_wal a_wn f2_dvelimf p_nfan f4_dvelimf f3_dvelimf f2_dvelimf p_ax12o f2_dvelimf a_sup_set_class f4_dvelimf a_sup_set_class a_wceq f2_dvelimf a_wal a_wn f2_dvelimf a_sup_set_class f3_dvelimf a_sup_set_class a_wceq f2_dvelimf a_wal a_wn f4_dvelimf a_sup_set_class f3_dvelimf a_sup_set_class a_wceq f4_dvelimf a_sup_set_class f3_dvelimf a_sup_set_class a_wceq f2_dvelimf a_wal a_wi p_impcom f2_dvelimf a_sup_set_class f3_dvelimf a_sup_set_class a_wceq f2_dvelimf a_wal a_wn f2_dvelimf a_sup_set_class f4_dvelimf a_sup_set_class a_wceq f2_dvelimf a_wal a_wn a_wa f4_dvelimf a_sup_set_class f3_dvelimf a_sup_set_class a_wceq f2_dvelimf p_nfd e0_dvelimf f0_dvelimf f2_dvelimf a_wnf f2_dvelimf a_sup_set_class f3_dvelimf a_sup_set_class a_wceq f2_dvelimf a_wal a_wn f2_dvelimf a_sup_set_class f4_dvelimf a_sup_set_class a_wceq f2_dvelimf a_wal a_wn a_wa p_a1i f2_dvelimf a_sup_set_class f3_dvelimf a_sup_set_class a_wceq f2_dvelimf a_wal a_wn f2_dvelimf a_sup_set_class f4_dvelimf a_sup_set_class a_wceq f2_dvelimf a_wal a_wn a_wa f4_dvelimf a_sup_set_class f3_dvelimf a_sup_set_class a_wceq f0_dvelimf f2_dvelimf p_nfimd f2_dvelimf a_sup_set_class f3_dvelimf a_sup_set_class a_wceq f2_dvelimf a_wal a_wn f4_dvelimf a_sup_set_class f3_dvelimf a_sup_set_class a_wceq f0_dvelimf a_wi f2_dvelimf f4_dvelimf p_nfald2 f1_dvelimf f4_dvelimf a_sup_set_class f3_dvelimf a_sup_set_class a_wceq f0_dvelimf a_wi f4_dvelimf a_wal f2_dvelimf a_sup_set_class f3_dvelimf a_sup_set_class a_wceq f2_dvelimf a_wal a_wn f2_dvelimf p_nfxfrd $.
$}

$(Specialization, using implicit substitution.  (Contributed by NM,
       30-Aug-1993.) $)

${
	$v ph ps x y  $.
	$d x ps  $.
	f0_spv $f wff ph $.
	f1_spv $f wff ps $.
	f2_spv $f set x $.
	f3_spv $f set y $.
	e0_spv $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_spv $p |- ( A. x ph -> ps ) $= e0_spv f2_spv a_sup_set_class f3_spv a_sup_set_class a_wceq f0_spv f1_spv p_biimpd f0_spv f1_spv f2_spv f3_spv p_spimv $.
$}

$(Distinct-variable version of ~ spime .  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v ph ps x y  $.
	$d x ph  $.
	f0_spimev $f wff ph $.
	f1_spimev $f wff ps $.
	f2_spimev $f set x $.
	f3_spimev $f set y $.
	e0_spimev $e |- ( x = y -> ( ph -> ps ) ) $.
	p_spimev $p |- ( ph -> E. x ps ) $= f0_spimev f2_spimev p_nfv e0_spimev f0_spimev f1_spimev f2_spimev f3_spimev p_spime $.
$}

$(Inference from existential specialization, using implicit substitution.
       (Contributed by NM, 19-Aug-1993.) $)

${
	$v ph ps x y  $.
	$d x ps  $.
	f0_speiv $f wff ph $.
	f1_speiv $f wff ps $.
	f2_speiv $f set x $.
	f3_speiv $f set y $.
	e0_speiv $e |- ( x = y -> ( ph <-> ps ) ) $.
	e1_speiv $e |- ps $.
	p_speiv $p |- E. x ph $= e1_speiv e0_speiv f2_speiv a_sup_set_class f3_speiv a_sup_set_class a_wceq f0_speiv f1_speiv p_biimprd f1_speiv f0_speiv f2_speiv f3_speiv p_spimev f1_speiv f0_speiv f2_speiv a_wex a_ax-mp $.
$}

$(A variable introduction law for equality.  Lemma 15 of [Monk2] p. 109.
       (Contributed by NM, 5-Aug-1993.) $)

${
	$v x y z  $.
	$d x z  $.
	$d y z  $.
	f0_equvin $f set x $.
	f1_equvin $f set y $.
	f2_equvin $f set z $.
	p_equvin $p |- ( x = y <-> E. z ( x = z /\ z = y ) ) $= f0_equvin f1_equvin f2_equvin p_equvini f0_equvin f2_equvin f1_equvin p_equtr f0_equvin a_sup_set_class f2_equvin a_sup_set_class a_wceq f2_equvin a_sup_set_class f1_equvin a_sup_set_class a_wceq f0_equvin a_sup_set_class f1_equvin a_sup_set_class a_wceq p_imp f0_equvin a_sup_set_class f2_equvin a_sup_set_class a_wceq f2_equvin a_sup_set_class f1_equvin a_sup_set_class a_wceq a_wa f0_equvin a_sup_set_class f1_equvin a_sup_set_class a_wceq f2_equvin p_exlimiv f0_equvin a_sup_set_class f1_equvin a_sup_set_class a_wceq f0_equvin a_sup_set_class f2_equvin a_sup_set_class a_wceq f2_equvin a_sup_set_class f1_equvin a_sup_set_class a_wceq a_wa f2_equvin a_wex p_impbii $.
$}

$(Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps x y  $.
	$d y ph  $.
	$d x ps  $.
	f0_cbvalv $f wff ph $.
	f1_cbvalv $f wff ps $.
	f2_cbvalv $f set x $.
	f3_cbvalv $f set y $.
	e0_cbvalv $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_cbvalv $p |- ( A. x ph <-> A. y ps ) $= f0_cbvalv f3_cbvalv p_nfv f1_cbvalv f2_cbvalv p_nfv e0_cbvalv f0_cbvalv f1_cbvalv f2_cbvalv f3_cbvalv p_cbval $.
$}

$(Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps x y  $.
	$d y ph  $.
	$d x ps  $.
	f0_cbvexv $f wff ph $.
	f1_cbvexv $f wff ps $.
	f2_cbvexv $f set x $.
	f3_cbvexv $f set y $.
	e0_cbvexv $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_cbvexv $p |- ( E. x ph <-> E. y ps ) $= f0_cbvexv f3_cbvexv p_nfv f1_cbvexv f2_cbvexv p_nfv e0_cbvexv f0_cbvexv f1_cbvexv f2_cbvexv f3_cbvexv p_cbvex $.
$}

$(Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 22-Dec-2003.)  (Revised by Mario Carneiro,
       6-Oct-2016.) $)

${
	$v ph ps x y z w  $.
	$d y x  $.
	$d y z  $.
	$d w x  $.
	$d w z  $.
	f0_cbval2 $f wff ph $.
	f1_cbval2 $f wff ps $.
	f2_cbval2 $f set x $.
	f3_cbval2 $f set y $.
	f4_cbval2 $f set z $.
	f5_cbval2 $f set w $.
	e0_cbval2 $e |- F/ z ph $.
	e1_cbval2 $e |- F/ w ph $.
	e2_cbval2 $e |- F/ x ps $.
	e3_cbval2 $e |- F/ y ps $.
	e4_cbval2 $e |- ( ( x = z /\ y = w ) -> ( ph <-> ps ) ) $.
	p_cbval2 $p |- ( A. x A. y ph <-> A. z A. w ps ) $= e0_cbval2 f0_cbval2 f4_cbval2 f3_cbval2 p_nfal e2_cbval2 f1_cbval2 f2_cbval2 f5_cbval2 p_nfal f2_cbval2 a_sup_set_class f4_cbval2 a_sup_set_class a_wceq f5_cbval2 p_nfv e1_cbval2 f2_cbval2 a_sup_set_class f4_cbval2 a_sup_set_class a_wceq f0_cbval2 f5_cbval2 p_nfan f2_cbval2 a_sup_set_class f4_cbval2 a_sup_set_class a_wceq f3_cbval2 p_nfv e3_cbval2 f2_cbval2 a_sup_set_class f4_cbval2 a_sup_set_class a_wceq f1_cbval2 f3_cbval2 p_nfan e4_cbval2 f2_cbval2 a_sup_set_class f4_cbval2 a_sup_set_class a_wceq f3_cbval2 a_sup_set_class f5_cbval2 a_sup_set_class a_wceq f0_cbval2 f1_cbval2 a_wb p_expcom f3_cbval2 a_sup_set_class f5_cbval2 a_sup_set_class a_wceq f2_cbval2 a_sup_set_class f4_cbval2 a_sup_set_class a_wceq f0_cbval2 f1_cbval2 p_pm5.32d f2_cbval2 a_sup_set_class f4_cbval2 a_sup_set_class a_wceq f0_cbval2 a_wa f2_cbval2 a_sup_set_class f4_cbval2 a_sup_set_class a_wceq f1_cbval2 a_wa f3_cbval2 f5_cbval2 p_cbval f2_cbval2 a_sup_set_class f4_cbval2 a_sup_set_class a_wceq f0_cbval2 f3_cbval2 p_19.28v f2_cbval2 a_sup_set_class f4_cbval2 a_sup_set_class a_wceq f1_cbval2 f5_cbval2 p_19.28v f2_cbval2 a_sup_set_class f4_cbval2 a_sup_set_class a_wceq f0_cbval2 a_wa f3_cbval2 a_wal f2_cbval2 a_sup_set_class f4_cbval2 a_sup_set_class a_wceq f1_cbval2 a_wa f5_cbval2 a_wal f2_cbval2 a_sup_set_class f4_cbval2 a_sup_set_class a_wceq f0_cbval2 f3_cbval2 a_wal a_wa f2_cbval2 a_sup_set_class f4_cbval2 a_sup_set_class a_wceq f1_cbval2 f5_cbval2 a_wal a_wa p_3bitr3i f2_cbval2 a_sup_set_class f4_cbval2 a_sup_set_class a_wceq f0_cbval2 f3_cbval2 a_wal f1_cbval2 f5_cbval2 a_wal p_pm5.32 f2_cbval2 a_sup_set_class f4_cbval2 a_sup_set_class a_wceq f0_cbval2 f3_cbval2 a_wal f1_cbval2 f5_cbval2 a_wal a_wb a_wi f2_cbval2 a_sup_set_class f4_cbval2 a_sup_set_class a_wceq f0_cbval2 f3_cbval2 a_wal a_wa f2_cbval2 a_sup_set_class f4_cbval2 a_sup_set_class a_wceq f1_cbval2 f5_cbval2 a_wal a_wa a_wb p_mpbir f0_cbval2 f3_cbval2 a_wal f1_cbval2 f5_cbval2 a_wal f2_cbval2 f4_cbval2 p_cbval $.
$}

$(Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 14-Sep-2003.)  (Revised by Mario Carneiro,
       6-Oct-2016.) $)

${
	$v ph ps x y z w  $.
	$d y x  $.
	$d y z  $.
	$d w x  $.
	$d w z  $.
	f0_cbvex2 $f wff ph $.
	f1_cbvex2 $f wff ps $.
	f2_cbvex2 $f set x $.
	f3_cbvex2 $f set y $.
	f4_cbvex2 $f set z $.
	f5_cbvex2 $f set w $.
	e0_cbvex2 $e |- F/ z ph $.
	e1_cbvex2 $e |- F/ w ph $.
	e2_cbvex2 $e |- F/ x ps $.
	e3_cbvex2 $e |- F/ y ps $.
	e4_cbvex2 $e |- ( ( x = z /\ y = w ) -> ( ph <-> ps ) ) $.
	p_cbvex2 $p |- ( E. x E. y ph <-> E. z E. w ps ) $= e0_cbvex2 f0_cbvex2 f4_cbvex2 f3_cbvex2 p_nfex e2_cbvex2 f1_cbvex2 f2_cbvex2 f5_cbvex2 p_nfex f2_cbvex2 a_sup_set_class f4_cbvex2 a_sup_set_class a_wceq f5_cbvex2 p_nfv e1_cbvex2 f2_cbvex2 a_sup_set_class f4_cbvex2 a_sup_set_class a_wceq f0_cbvex2 f5_cbvex2 p_nfan f2_cbvex2 a_sup_set_class f4_cbvex2 a_sup_set_class a_wceq f3_cbvex2 p_nfv e3_cbvex2 f2_cbvex2 a_sup_set_class f4_cbvex2 a_sup_set_class a_wceq f1_cbvex2 f3_cbvex2 p_nfan e4_cbvex2 f2_cbvex2 a_sup_set_class f4_cbvex2 a_sup_set_class a_wceq f3_cbvex2 a_sup_set_class f5_cbvex2 a_sup_set_class a_wceq f0_cbvex2 f1_cbvex2 a_wb p_expcom f3_cbvex2 a_sup_set_class f5_cbvex2 a_sup_set_class a_wceq f2_cbvex2 a_sup_set_class f4_cbvex2 a_sup_set_class a_wceq f0_cbvex2 f1_cbvex2 p_pm5.32d f2_cbvex2 a_sup_set_class f4_cbvex2 a_sup_set_class a_wceq f0_cbvex2 a_wa f2_cbvex2 a_sup_set_class f4_cbvex2 a_sup_set_class a_wceq f1_cbvex2 a_wa f3_cbvex2 f5_cbvex2 p_cbvex f2_cbvex2 a_sup_set_class f4_cbvex2 a_sup_set_class a_wceq f0_cbvex2 f3_cbvex2 p_19.42v f2_cbvex2 a_sup_set_class f4_cbvex2 a_sup_set_class a_wceq f1_cbvex2 f5_cbvex2 p_19.42v f2_cbvex2 a_sup_set_class f4_cbvex2 a_sup_set_class a_wceq f0_cbvex2 a_wa f3_cbvex2 a_wex f2_cbvex2 a_sup_set_class f4_cbvex2 a_sup_set_class a_wceq f1_cbvex2 a_wa f5_cbvex2 a_wex f2_cbvex2 a_sup_set_class f4_cbvex2 a_sup_set_class a_wceq f0_cbvex2 f3_cbvex2 a_wex a_wa f2_cbvex2 a_sup_set_class f4_cbvex2 a_sup_set_class a_wceq f1_cbvex2 f5_cbvex2 a_wex a_wa p_3bitr3i f2_cbvex2 a_sup_set_class f4_cbvex2 a_sup_set_class a_wceq f0_cbvex2 f3_cbvex2 a_wex f1_cbvex2 f5_cbvex2 a_wex p_pm5.32 f2_cbvex2 a_sup_set_class f4_cbvex2 a_sup_set_class a_wceq f0_cbvex2 f3_cbvex2 a_wex f1_cbvex2 f5_cbvex2 a_wex a_wb a_wi f2_cbvex2 a_sup_set_class f4_cbvex2 a_sup_set_class a_wceq f0_cbvex2 f3_cbvex2 a_wex a_wa f2_cbvex2 a_sup_set_class f4_cbvex2 a_sup_set_class a_wceq f1_cbvex2 f5_cbvex2 a_wex a_wa a_wb p_mpbir f0_cbvex2 f3_cbvex2 a_wex f1_cbvex2 f5_cbvex2 a_wex f2_cbvex2 f4_cbvex2 p_cbvex $.
$}

$(Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 4-Feb-2005.) $)

${
	$v ph ps x y z w  $.
	$d z w ph  $.
	$d x y ps  $.
	$d x w  $.
	$d z y  $.
	f0_cbval2v $f wff ph $.
	f1_cbval2v $f wff ps $.
	f2_cbval2v $f set x $.
	f3_cbval2v $f set y $.
	f4_cbval2v $f set z $.
	f5_cbval2v $f set w $.
	e0_cbval2v $e |- ( ( x = z /\ y = w ) -> ( ph <-> ps ) ) $.
	p_cbval2v $p |- ( A. x A. y ph <-> A. z A. w ps ) $= f0_cbval2v f4_cbval2v p_nfv f0_cbval2v f5_cbval2v p_nfv f1_cbval2v f2_cbval2v p_nfv f1_cbval2v f3_cbval2v p_nfv e0_cbval2v f0_cbval2v f1_cbval2v f2_cbval2v f3_cbval2v f4_cbval2v f5_cbval2v p_cbval2 $.
$}

$(Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 26-Jul-1995.) $)

${
	$v ph ps x y z w  $.
	$d z w ph  $.
	$d x y ps  $.
	$d x w  $.
	$d z y  $.
	f0_cbvex2v $f wff ph $.
	f1_cbvex2v $f wff ps $.
	f2_cbvex2v $f set x $.
	f3_cbvex2v $f set y $.
	f4_cbvex2v $f set z $.
	f5_cbvex2v $f set w $.
	e0_cbvex2v $e |- ( ( x = z /\ y = w ) -> ( ph <-> ps ) ) $.
	p_cbvex2v $p |- ( E. x E. y ph <-> E. z E. w ps ) $= f0_cbvex2v f4_cbvex2v p_nfv f0_cbvex2v f5_cbvex2v p_nfv f1_cbvex2v f2_cbvex2v p_nfv f1_cbvex2v f3_cbvex2v p_nfv e0_cbvex2v f0_cbvex2v f1_cbvex2v f2_cbvex2v f3_cbvex2v f4_cbvex2v f5_cbvex2v p_cbvex2 $.
$}

$(Deduction used to change bound variables, using implicit substitution,
       particularly useful in conjunction with ~ dvelim .  (Contributed by NM,
       2-Jan-2002.)  (Revised by Mario Carneiro, 6-Oct-2016.) $)

${
	$v ph ps ch x y  $.
	$d x ph  $.
	$d x ch  $.
	f0_cbvald $f wff ph $.
	f1_cbvald $f wff ps $.
	f2_cbvald $f wff ch $.
	f3_cbvald $f set x $.
	f4_cbvald $f set y $.
	e0_cbvald $e |- F/ y ph $.
	e1_cbvald $e |- ( ph -> F/ y ps ) $.
	e2_cbvald $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
	p_cbvald $p |- ( ph -> ( A. x ps <-> A. y ch ) ) $= e0_cbvald f0_cbvald f4_cbvald p_nfri f0_cbvald f0_cbvald f4_cbvald a_wal f3_cbvald p_alrimiv e1_cbvald f0_cbvald f2_cbvald f3_cbvald p_nfvd e2_cbvald f0_cbvald f1_cbvald f2_cbvald f3_cbvald f4_cbvald p_cbv2 f0_cbvald f0_cbvald f4_cbvald a_wal f3_cbvald a_wal f1_cbvald f3_cbvald a_wal f2_cbvald f4_cbvald a_wal a_wb p_syl $.
$}

$(Deduction used to change bound variables, using implicit substitution,
       particularly useful in conjunction with ~ dvelim .  (Contributed by NM,
       2-Jan-2002.)  (Revised by Mario Carneiro, 6-Oct-2016.) $)

${
	$v ph ps ch x y  $.
	$d x ph  $.
	$d x ch  $.
	f0_cbvexd $f wff ph $.
	f1_cbvexd $f wff ps $.
	f2_cbvexd $f wff ch $.
	f3_cbvexd $f set x $.
	f4_cbvexd $f set y $.
	e0_cbvexd $e |- F/ y ph $.
	e1_cbvexd $e |- ( ph -> F/ y ps ) $.
	e2_cbvexd $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
	p_cbvexd $p |- ( ph -> ( E. x ps <-> E. y ch ) ) $= e0_cbvexd e1_cbvexd f0_cbvexd f1_cbvexd f4_cbvexd p_nfnd e2_cbvexd f1_cbvexd f2_cbvexd p_notbi f0_cbvexd f3_cbvexd a_sup_set_class f4_cbvexd a_sup_set_class a_wceq f1_cbvexd f2_cbvexd a_wb f1_cbvexd a_wn f2_cbvexd a_wn a_wb p_syl6ib f0_cbvexd f1_cbvexd a_wn f2_cbvexd a_wn f3_cbvexd f4_cbvexd p_cbvald f0_cbvexd f1_cbvexd a_wn f3_cbvexd a_wal f2_cbvexd a_wn f4_cbvexd a_wal p_notbid f1_cbvexd f3_cbvexd a_df-ex f2_cbvexd f4_cbvexd a_df-ex f0_cbvexd f1_cbvexd a_wn f3_cbvexd a_wal a_wn f2_cbvexd a_wn f4_cbvexd a_wal a_wn f1_cbvexd f3_cbvexd a_wex f2_cbvexd f4_cbvexd a_wex p_3bitr4g $.
$}

$(Rule used to change the bound variable in a universal quantifier with
       implicit substitution.  Deduction form.  (Contributed by David Moews,
       1-May-2017.) $)

${
	$v ph ps ch x y  $.
	$d ps y  $.
	$d ch x  $.
	$d ph x  $.
	$d ph y  $.
	f0_cbvaldva $f wff ph $.
	f1_cbvaldva $f wff ps $.
	f2_cbvaldva $f wff ch $.
	f3_cbvaldva $f set x $.
	f4_cbvaldva $f set y $.
	e0_cbvaldva $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
	p_cbvaldva $p |- ( ph -> ( A. x ps <-> A. y ch ) ) $= f0_cbvaldva f4_cbvaldva p_nfv f0_cbvaldva f1_cbvaldva f4_cbvaldva p_nfvd e0_cbvaldva f0_cbvaldva f3_cbvaldva a_sup_set_class f4_cbvaldva a_sup_set_class a_wceq f1_cbvaldva f2_cbvaldva a_wb p_ex f0_cbvaldva f1_cbvaldva f2_cbvaldva f3_cbvaldva f4_cbvaldva p_cbvald $.
$}

$(Rule used to change the bound variable in an existential quantifier with
       implicit substitution.  Deduction form.  (Contributed by David Moews,
       1-May-2017.) $)

${
	$v ph ps ch x y  $.
	$d ps y  $.
	$d ch x  $.
	$d ph x  $.
	$d ph y  $.
	f0_cbvexdva $f wff ph $.
	f1_cbvexdva $f wff ps $.
	f2_cbvexdva $f wff ch $.
	f3_cbvexdva $f set x $.
	f4_cbvexdva $f set y $.
	e0_cbvexdva $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
	p_cbvexdva $p |- ( ph -> ( E. x ps <-> E. y ch ) ) $= f0_cbvexdva f4_cbvexdva p_nfv f0_cbvexdva f1_cbvexdva f4_cbvexdva p_nfvd e0_cbvexdva f0_cbvexdva f3_cbvexdva a_sup_set_class f4_cbvexdva a_sup_set_class a_wceq f1_cbvexdva f2_cbvexdva a_wb p_ex f0_cbvexdva f1_cbvexdva f2_cbvexdva f3_cbvexdva f4_cbvexdva p_cbvexd $.
$}

$(Define temporary individual variables. $)

$(Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 26-Jul-1995.) $)

${
	$v ph ps ch x y z w v u f g  $.
	$d w z ch  $.
	$d u v ph  $.
	$d x y ps  $.
	$d f g ps  $.
	$d f w  $.
	$d g z  $.
	$d u v w x y z  $.
	f0_cbvex4v $f wff ph $.
	f1_cbvex4v $f wff ps $.
	f2_cbvex4v $f wff ch $.
	f3_cbvex4v $f set x $.
	f4_cbvex4v $f set y $.
	f5_cbvex4v $f set z $.
	f6_cbvex4v $f set w $.
	f7_cbvex4v $f set v $.
	f8_cbvex4v $f set u $.
	f9_cbvex4v $f set f $.
	f10_cbvex4v $f set g $.
	e0_cbvex4v $e |- ( ( x = v /\ y = u ) -> ( ph <-> ps ) ) $.
	e1_cbvex4v $e |- ( ( z = f /\ w = g ) -> ( ps <-> ch ) ) $.
	p_cbvex4v $p |- ( E. x E. y E. z E. w ph <-> E. v E. u E. f E. g ch ) $= e0_cbvex4v f3_cbvex4v a_sup_set_class f7_cbvex4v a_sup_set_class a_wceq f4_cbvex4v a_sup_set_class f8_cbvex4v a_sup_set_class a_wceq a_wa f0_cbvex4v f1_cbvex4v f5_cbvex4v f6_cbvex4v p_2exbidv f0_cbvex4v f6_cbvex4v a_wex f5_cbvex4v a_wex f1_cbvex4v f6_cbvex4v a_wex f5_cbvex4v a_wex f3_cbvex4v f4_cbvex4v f7_cbvex4v f8_cbvex4v p_cbvex2v e1_cbvex4v f1_cbvex4v f2_cbvex4v f5_cbvex4v f6_cbvex4v f9_cbvex4v f10_cbvex4v p_cbvex2v f1_cbvex4v f6_cbvex4v a_wex f5_cbvex4v a_wex f2_cbvex4v f10_cbvex4v a_wex f9_cbvex4v a_wex f7_cbvex4v f8_cbvex4v p_2exbii f0_cbvex4v f6_cbvex4v a_wex f5_cbvex4v a_wex f4_cbvex4v a_wex f3_cbvex4v a_wex f1_cbvex4v f6_cbvex4v a_wex f5_cbvex4v a_wex f8_cbvex4v a_wex f7_cbvex4v a_wex f2_cbvex4v f10_cbvex4v a_wex f9_cbvex4v a_wex f8_cbvex4v a_wex f7_cbvex4v a_wex p_bitri $.
$}

$(Implicit substitution of ` y ` for ` x ` into a theorem.  (Contributed
       by NM, 20-Apr-1994.) $)

${
	$v ph ps x y  $.
	$d x ps  $.
	f0_chvarv $f wff ph $.
	f1_chvarv $f wff ps $.
	f2_chvarv $f set x $.
	f3_chvarv $f set y $.
	e0_chvarv $e |- ( x = y -> ( ph <-> ps ) ) $.
	e1_chvarv $e |- ph $.
	p_chvarv $p |- ps $= e0_chvarv f0_chvarv f1_chvarv f2_chvarv f3_chvarv p_spv e1_chvarv f0_chvarv f1_chvarv f2_chvarv p_mpg $.
$}

$(When the class variables in definition ~ df-clel are replaced with set
       variables, this theorem of predicate calculus is the result.  This
       theorem provides part of the justification for the consistency of that
       definition, which "overloads" the set variables in ~ wel with the class
       variables in ~ wcel .  Note:  This proof is referenced on the Metamath
       Proof Explorer Home Page and shouldn't be changed.  (Contributed by NM,
       28-Jan-2004.)  (Proof modification is discouraged.) $)

${
	$v x y z  $.
	$d x z  $.
	$d y z  $.
	f0_cleljust $f set x $.
	f1_cleljust $f set y $.
	f2_cleljust $f set z $.
	p_cleljust $p |- ( x e. y <-> E. z ( z = x /\ z e. y ) ) $= f0_cleljust a_sup_set_class f1_cleljust a_sup_set_class a_wcel f2_cleljust a_ax-17 f2_cleljust f0_cleljust f1_cleljust p_elequ1 f2_cleljust a_sup_set_class f1_cleljust a_sup_set_class a_wcel f0_cleljust a_sup_set_class f1_cleljust a_sup_set_class a_wcel f2_cleljust f0_cleljust p_equsexh f2_cleljust a_sup_set_class f0_cleljust a_sup_set_class a_wceq f2_cleljust a_sup_set_class f1_cleljust a_sup_set_class a_wcel a_wa f2_cleljust a_wex f0_cleljust a_sup_set_class f1_cleljust a_sup_set_class a_wcel p_bicomi $.
$}

$(When the class variables in definition ~ df-clel are replaced with set
       variables, this theorem of predicate calculus is the result.  This
       theorem provides part of the justification for the consistency of that
       definition, which "overloads" the set variables in ~ wel with the class
       variables in ~ wcel .  (Contributed by NM, 28-Jan-2004.)  (Revised by
       Mario Carneiro, 21-Dec-2016.) $)

${
	$v x y z  $.
	$d x z  $.
	$d y z  $.
	f0_cleljustALT $f set x $.
	f1_cleljustALT $f set y $.
	f2_cleljustALT $f set z $.
	p_cleljustALT $p |- ( x e. y <-> E. z ( z = x /\ z e. y ) ) $= f0_cleljustALT a_sup_set_class f1_cleljustALT a_sup_set_class a_wcel f2_cleljustALT p_nfv f2_cleljustALT f0_cleljustALT f1_cleljustALT p_elequ1 f2_cleljustALT a_sup_set_class f1_cleljustALT a_sup_set_class a_wcel f0_cleljustALT a_sup_set_class f1_cleljustALT a_sup_set_class a_wcel f2_cleljustALT f0_cleljustALT p_equsex f2_cleljustALT a_sup_set_class f0_cleljustALT a_sup_set_class a_wceq f2_cleljustALT a_sup_set_class f1_cleljustALT a_sup_set_class a_wcel a_wa f2_cleljustALT a_wex f0_cleljustALT a_sup_set_class f1_cleljustALT a_sup_set_class a_wcel p_bicomi $.
$}

$(This theorem can be used to eliminate a distinct variable restriction on
       ` x ` and ` z ` and replace it with the "distinctor" ` -. A. x x = y `
       as an antecedent. ` ph ` normally has ` z ` free and can be read
       ` ph ( z ) ` , and ` ps ` substitutes ` y ` for ` z ` and can be read
       ` ph ( y ) ` .  We don't require that ` x ` and ` y ` be distinct: if
       they aren't, the distinctor will become false (in multiple-element
       domains of discourse) and "protect" the consequent.

       To obtain a closed-theorem form of this inference, prefix the hypotheses
       with ` A. x A. z ` , conjoin them, and apply ~ dvelimdf .

       Other variants of this theorem are ~ dvelimh (with no distinct variable
       restrictions), ~ dvelimhw (that avoids ~ ax-12 ), and ~ dvelimALT (that
       avoids ~ ax-10 ).  (Contributed by NM, 23-Nov-1994.) $)

${
	$v ph ps x y z  $.
	$d z ps  $.
	f0_dvelim $f wff ph $.
	f1_dvelim $f wff ps $.
	f2_dvelim $f set x $.
	f3_dvelim $f set y $.
	f4_dvelim $f set z $.
	e0_dvelim $e |- ( ph -> A. x ph ) $.
	e1_dvelim $e |- ( z = y -> ( ph <-> ps ) ) $.
	p_dvelim $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $= e0_dvelim f1_dvelim f4_dvelim a_ax-17 e1_dvelim f0_dvelim f1_dvelim f2_dvelim f3_dvelim f4_dvelim p_dvelimh $.
$}

$(Version of ~ dvelim using "not free" notation.  (Contributed by Mario
       Carneiro, 9-Oct-2016.) $)

${
	$v ph ps x y z  $.
	$d z ps  $.
	f0_dvelimnf $f wff ph $.
	f1_dvelimnf $f wff ps $.
	f2_dvelimnf $f set x $.
	f3_dvelimnf $f set y $.
	f4_dvelimnf $f set z $.
	e0_dvelimnf $e |- F/ x ph $.
	e1_dvelimnf $e |- ( z = y -> ( ph <-> ps ) ) $.
	p_dvelimnf $p |- ( -. A. x x = y -> F/ x ps ) $= e0_dvelimnf f1_dvelimnf f4_dvelimnf p_nfv e1_dvelimnf f0_dvelimnf f1_dvelimnf f2_dvelimnf f3_dvelimnf f4_dvelimnf p_dvelimf $.
$}

$(Quantifier introduction when one pair of variables is distinct.
       (Contributed by NM, 2-Jan-2002.) $)

${
	$v x y z  $.
	$d w z x  $.
	$d w y  $.
	f0_dveeq1 $f set x $.
	f1_dveeq1 $f set y $.
	f2_dveeq1 $f set z $.
	i0_dveeq1 $f set w $.
	p_dveeq1 $p |- ( -. A. x x = y -> ( y = z -> A. x y = z ) ) $= i0_dveeq1 f1_dveeq1 f2_dveeq1 p_equequ1 i0_dveeq1 a_sup_set_class f2_dveeq1 a_sup_set_class a_wceq f1_dveeq1 a_sup_set_class f2_dveeq1 a_sup_set_class a_wceq f0_dveeq1 f1_dveeq1 i0_dveeq1 p_dvelimv $.
$}

$(Quantifier introduction when one pair of variables is distinct.
       (Contributed by NM, 2-Jan-2002.) $)

${
	$v x y z  $.
	$d w z x  $.
	$d w y  $.
	f0_dveel1 $f set x $.
	f1_dveel1 $f set y $.
	f2_dveel1 $f set z $.
	i0_dveel1 $f set w $.
	p_dveel1 $p |- ( -. A. x x = y -> ( y e. z -> A. x y e. z ) ) $= i0_dveel1 f1_dveel1 f2_dveel1 p_elequ1 i0_dveel1 a_sup_set_class f2_dveel1 a_sup_set_class a_wcel f1_dveel1 a_sup_set_class f2_dveel1 a_sup_set_class a_wcel f0_dveel1 f1_dveel1 i0_dveel1 p_dvelimv $.
$}

$(Quantifier introduction when one pair of variables is distinct.
       (Contributed by NM, 2-Jan-2002.) $)

${
	$v x y z  $.
	$d w z x  $.
	$d w y  $.
	f0_dveel2 $f set x $.
	f1_dveel2 $f set y $.
	f2_dveel2 $f set z $.
	i0_dveel2 $f set w $.
	p_dveel2 $p |- ( -. A. x x = y -> ( z e. y -> A. x z e. y ) ) $= i0_dveel2 f1_dveel2 f2_dveel2 p_elequ2 f2_dveel2 a_sup_set_class i0_dveel2 a_sup_set_class a_wcel f2_dveel2 a_sup_set_class f1_dveel2 a_sup_set_class a_wcel f0_dveel2 f1_dveel2 i0_dveel2 p_dvelimv $.
$}

$(` w ` is dummy. $)

$(Axiom ~ ax-15 is redundant if we assume ~ ax-17 .  Remark 9.6 in
       [Megill] p. 448 (p. 16 of the preprint), regarding axiom scheme C14'.

       Note that ` w ` is a dummy variable introduced in the proof.  On the web
       page, it is implicitly assumed to be distinct from all other variables.
       (This is made explicit in the database file set.mm).  Its purpose is to
       satisfy the distinct variable requirements of ~ dveel2 and ~ ax-17 .  By
       the end of the proof it has vanished, and the final theorem has no
       distinct variable requirements.  (Contributed by NM, 29-Jun-1995.)
       (Proof modification is discouraged.) $)

${
	$v x y z  $.
	$d w y  $.
	$d w z  $.
	$d w x  $.
	f0_ax15 $f set x $.
	f1_ax15 $f set y $.
	f2_ax15 $f set z $.
	i0_ax15 $f set w $.
	p_ax15 $p |- ( -. A. z z = x -> ( -. A. z z = y -> ( x e. y -> A. z x e. y ) ) ) $= f2_ax15 a_sup_set_class f1_ax15 a_sup_set_class a_wceq f2_ax15 p_hbn1 f2_ax15 f1_ax15 i0_ax15 p_dveel2 f2_ax15 a_sup_set_class f1_ax15 a_sup_set_class a_wceq f2_ax15 a_wal a_wn i0_ax15 a_sup_set_class f1_ax15 a_sup_set_class a_wcel f2_ax15 p_hbim1 i0_ax15 f0_ax15 f1_ax15 p_elequ1 i0_ax15 a_sup_set_class f0_ax15 a_sup_set_class a_wceq i0_ax15 a_sup_set_class f1_ax15 a_sup_set_class a_wcel f0_ax15 a_sup_set_class f1_ax15 a_sup_set_class a_wcel f2_ax15 a_sup_set_class f1_ax15 a_sup_set_class a_wceq f2_ax15 a_wal a_wn p_imbi2d f2_ax15 a_sup_set_class f1_ax15 a_sup_set_class a_wceq f2_ax15 a_wal a_wn i0_ax15 a_sup_set_class f1_ax15 a_sup_set_class a_wcel a_wi f2_ax15 a_sup_set_class f1_ax15 a_sup_set_class a_wceq f2_ax15 a_wal a_wn f0_ax15 a_sup_set_class f1_ax15 a_sup_set_class a_wcel a_wi f2_ax15 f0_ax15 i0_ax15 p_dvelim f2_ax15 a_sup_set_class f1_ax15 a_sup_set_class a_wceq f2_ax15 p_nfa1 f2_ax15 a_sup_set_class f1_ax15 a_sup_set_class a_wceq f2_ax15 a_wal f2_ax15 p_nfn f2_ax15 a_sup_set_class f1_ax15 a_sup_set_class a_wceq f2_ax15 a_wal a_wn f0_ax15 a_sup_set_class f1_ax15 a_sup_set_class a_wcel f2_ax15 p_19.21 f2_ax15 a_sup_set_class f0_ax15 a_sup_set_class a_wceq f2_ax15 a_wal a_wn f2_ax15 a_sup_set_class f1_ax15 a_sup_set_class a_wceq f2_ax15 a_wal a_wn f0_ax15 a_sup_set_class f1_ax15 a_sup_set_class a_wcel a_wi f2_ax15 a_sup_set_class f1_ax15 a_sup_set_class a_wceq f2_ax15 a_wal a_wn f0_ax15 a_sup_set_class f1_ax15 a_sup_set_class a_wcel a_wi f2_ax15 a_wal f2_ax15 a_sup_set_class f1_ax15 a_sup_set_class a_wceq f2_ax15 a_wal a_wn f0_ax15 a_sup_set_class f1_ax15 a_sup_set_class a_wcel f2_ax15 a_wal a_wi p_syl6ib f2_ax15 a_sup_set_class f0_ax15 a_sup_set_class a_wceq f2_ax15 a_wal a_wn f2_ax15 a_sup_set_class f1_ax15 a_sup_set_class a_wceq f2_ax15 a_wal a_wn f0_ax15 a_sup_set_class f1_ax15 a_sup_set_class a_wcel f0_ax15 a_sup_set_class f1_ax15 a_sup_set_class a_wcel f2_ax15 a_wal p_pm2.86d $.
$}

$(Formula-building lemma for use with the Distinctor Reduction Theorem.
     Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).  (Contributed
     by NM, 5-Aug-1993.) $)

${
	$v ph x y z  $.
	f0_drsb1 $f wff ph $.
	f1_drsb1 $f set x $.
	f2_drsb1 $f set y $.
	f3_drsb1 $f set z $.
	p_drsb1 $p |- ( A. x x = y -> ( [ z / x ] ph <-> [ z / y ] ph ) ) $= f1_drsb1 f2_drsb1 f3_drsb1 p_equequ1 f1_drsb1 a_sup_set_class f2_drsb1 a_sup_set_class a_wceq f1_drsb1 a_sup_set_class f3_drsb1 a_sup_set_class a_wceq f2_drsb1 a_sup_set_class f3_drsb1 a_sup_set_class a_wceq a_wb f1_drsb1 p_sps f1_drsb1 a_sup_set_class f2_drsb1 a_sup_set_class a_wceq f1_drsb1 a_wal f1_drsb1 a_sup_set_class f3_drsb1 a_sup_set_class a_wceq f2_drsb1 a_sup_set_class f3_drsb1 a_sup_set_class a_wceq f0_drsb1 p_imbi1d f1_drsb1 f2_drsb1 f3_drsb1 p_equequ1 f1_drsb1 a_sup_set_class f2_drsb1 a_sup_set_class a_wceq f1_drsb1 a_sup_set_class f3_drsb1 a_sup_set_class a_wceq f2_drsb1 a_sup_set_class f3_drsb1 a_sup_set_class a_wceq a_wb f1_drsb1 p_sps f1_drsb1 a_sup_set_class f2_drsb1 a_sup_set_class a_wceq f1_drsb1 a_wal f1_drsb1 a_sup_set_class f3_drsb1 a_sup_set_class a_wceq f2_drsb1 a_sup_set_class f3_drsb1 a_sup_set_class a_wceq f0_drsb1 p_anbi1d f1_drsb1 a_sup_set_class f3_drsb1 a_sup_set_class a_wceq f0_drsb1 a_wa f2_drsb1 a_sup_set_class f3_drsb1 a_sup_set_class a_wceq f0_drsb1 a_wa f1_drsb1 f2_drsb1 p_drex1 f1_drsb1 a_sup_set_class f2_drsb1 a_sup_set_class a_wceq f1_drsb1 a_wal f1_drsb1 a_sup_set_class f3_drsb1 a_sup_set_class a_wceq f0_drsb1 a_wi f2_drsb1 a_sup_set_class f3_drsb1 a_sup_set_class a_wceq f0_drsb1 a_wi f1_drsb1 a_sup_set_class f3_drsb1 a_sup_set_class a_wceq f0_drsb1 a_wa f1_drsb1 a_wex f2_drsb1 a_sup_set_class f3_drsb1 a_sup_set_class a_wceq f0_drsb1 a_wa f2_drsb1 a_wex p_anbi12d f0_drsb1 f1_drsb1 f3_drsb1 a_df-sb f0_drsb1 f2_drsb1 f3_drsb1 a_df-sb f1_drsb1 a_sup_set_class f2_drsb1 a_sup_set_class a_wceq f1_drsb1 a_wal f1_drsb1 a_sup_set_class f3_drsb1 a_sup_set_class a_wceq f0_drsb1 a_wi f1_drsb1 a_sup_set_class f3_drsb1 a_sup_set_class a_wceq f0_drsb1 a_wa f1_drsb1 a_wex a_wa f2_drsb1 a_sup_set_class f3_drsb1 a_sup_set_class a_wceq f0_drsb1 a_wi f2_drsb1 a_sup_set_class f3_drsb1 a_sup_set_class a_wceq f0_drsb1 a_wa f2_drsb1 a_wex a_wa f0_drsb1 f1_drsb1 f3_drsb1 a_wsb f0_drsb1 f2_drsb1 f3_drsb1 a_wsb p_3bitr4g $.
$}

$(One direction of a simplified definition of substitution.  (Contributed by
     NM, 5-Aug-1993.) $)

${
	$v ph x y  $.
	f0_sb2 $f wff ph $.
	f1_sb2 $f set x $.
	f2_sb2 $f set y $.
	p_sb2 $p |- ( A. x ( x = y -> ph ) -> [ y / x ] ph ) $= f1_sb2 a_sup_set_class f2_sb2 a_sup_set_class a_wceq f0_sb2 a_wi f1_sb2 p_sp f0_sb2 f1_sb2 f2_sb2 p_equs4 f0_sb2 f1_sb2 f2_sb2 a_df-sb f1_sb2 a_sup_set_class f2_sb2 a_sup_set_class a_wceq f0_sb2 a_wi f1_sb2 a_wal f1_sb2 a_sup_set_class f2_sb2 a_sup_set_class a_wceq f0_sb2 a_wi f1_sb2 a_sup_set_class f2_sb2 a_sup_set_class a_wceq f0_sb2 a_wa f1_sb2 a_wex f0_sb2 f1_sb2 f2_sb2 a_wsb p_sylanbrc $.
$}

$(The specialization axiom of standard predicate calculus.  It states that
     if a statement ` ph ` holds for all ` x ` , then it also holds for the
     specific case of ` y ` (properly) substituted for ` x ` .  Translated to
     traditional notation, it can be read:  " ` A. x ph ( x ) -> ph ( y ) ` ,
     provided that ` y ` is free for ` x ` in ` ph ( x ) ` ."  Axiom 4 of
     [Mendelson] p. 69.  See also ~ spsbc and ~ rspsbc .  (Contributed by NM,
     5-Aug-1993.) $)

${
	$v ph x y  $.
	f0_stdpc4 $f wff ph $.
	f1_stdpc4 $f set x $.
	f2_stdpc4 $f set y $.
	p_stdpc4 $p |- ( A. x ph -> [ y / x ] ph ) $= f0_stdpc4 f1_stdpc4 a_sup_set_class f2_stdpc4 a_sup_set_class a_wceq a_ax-1 f0_stdpc4 f1_stdpc4 a_sup_set_class f2_stdpc4 a_sup_set_class a_wceq f0_stdpc4 a_wi f1_stdpc4 p_alimi f0_stdpc4 f1_stdpc4 f2_stdpc4 p_sb2 f0_stdpc4 f1_stdpc4 a_wal f1_stdpc4 a_sup_set_class f2_stdpc4 a_sup_set_class a_wceq f0_stdpc4 a_wi f1_stdpc4 a_wal f0_stdpc4 f1_stdpc4 f2_stdpc4 a_wsb p_syl $.
$}

$(Substitution has no effect on a non-free variable.  (Contributed by NM,
     30-May-2009.)  (Revised by Mario Carneiro, 12-Oct-2016.) $)

${
	$v ph x y  $.
	f0_sbft $f wff ph $.
	f1_sbft $f set x $.
	f2_sbft $f set y $.
	p_sbft $p |- ( F/ x ph -> ( [ y / x ] ph <-> ph ) ) $= f0_sbft f1_sbft f2_sbft p_sb1 f1_sbft a_sup_set_class f2_sbft a_sup_set_class a_wceq f0_sbft p_simpr f1_sbft a_sup_set_class f2_sbft a_sup_set_class a_wceq f0_sbft a_wa f0_sbft a_wi f1_sbft a_ax-gen f1_sbft a_sup_set_class f2_sbft a_sup_set_class a_wceq f0_sbft a_wa f0_sbft f1_sbft p_19.23t f0_sbft f1_sbft a_wnf f1_sbft a_sup_set_class f2_sbft a_sup_set_class a_wceq f0_sbft a_wa f0_sbft a_wi f1_sbft a_wal f1_sbft a_sup_set_class f2_sbft a_sup_set_class a_wceq f0_sbft a_wa f1_sbft a_wex f0_sbft a_wi p_mpbii f0_sbft f1_sbft f2_sbft a_wsb f1_sbft a_sup_set_class f2_sbft a_sup_set_class a_wceq f0_sbft a_wa f1_sbft a_wex f0_sbft f1_sbft a_wnf f0_sbft p_syl5 f0_sbft f1_sbft p_nfr f0_sbft f1_sbft f2_sbft p_stdpc4 f0_sbft f1_sbft a_wnf f0_sbft f0_sbft f1_sbft a_wal f0_sbft f1_sbft f2_sbft a_wsb p_syl6 f0_sbft f1_sbft a_wnf f0_sbft f1_sbft f2_sbft a_wsb f0_sbft p_impbid $.
$}

$(Substitution for a variable not free in a wff does not affect it.
       (Contributed by NM, 5-Aug-1993.)  (Revised by Mario Carneiro,
       4-Oct-2016.) $)

${
	$v ph x y  $.
	f0_sbf $f wff ph $.
	f1_sbf $f set x $.
	f2_sbf $f set y $.
	e0_sbf $e |- F/ x ph $.
	p_sbf $p |- ( [ y / x ] ph <-> ph ) $= e0_sbf f0_sbf f1_sbf f2_sbf p_sbft f0_sbf f1_sbf a_wnf f0_sbf f1_sbf f2_sbf a_wsb f0_sbf a_wb a_ax-mp $.
$}

$(Substitution for a variable not free in a wff does not affect it.
       (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph x y  $.
	f0_sbh $f wff ph $.
	f1_sbh $f set x $.
	f2_sbh $f set y $.
	e0_sbh $e |- ( ph -> A. x ph ) $.
	p_sbh $p |- ( [ y / x ] ph <-> ph ) $= e0_sbh f0_sbh f1_sbh p_nfi f0_sbh f1_sbh f2_sbh p_sbf $.
$}

$(Substitution has no effect on a bound variable.  (Contributed by NM,
     1-Jul-2005.) $)

${
	$v ph x y  $.
	f0_sbf2 $f wff ph $.
	f1_sbf2 $f set x $.
	f2_sbf2 $f set y $.
	p_sbf2 $p |- ( [ y / x ] A. x ph <-> A. x ph ) $= f0_sbf2 f1_sbf2 p_nfa1 f0_sbf2 f1_sbf2 a_wal f1_sbf2 f2_sbf2 p_sbf $.
$}

$(Equivalence involving substitution for a variable not free.
       (Contributed by NM, 5-Aug-1993.)  (Revised by Mario Carneiro,
       4-Oct-2016.) $)

${
	$v ph x y  $.
	f0_sb6x $f wff ph $.
	f1_sb6x $f set x $.
	f2_sb6x $f set y $.
	e0_sb6x $e |- F/ x ph $.
	p_sb6x $p |- ( [ y / x ] ph <-> A. x ( x = y -> ph ) ) $= e0_sb6x f0_sb6x f1_sb6x f2_sb6x p_sbf e0_sb6x f1_sb6x a_sup_set_class f2_sb6x a_sup_set_class a_wceq f0_sb6x p_biidd f0_sb6x f0_sb6x f1_sb6x f2_sb6x p_equsal f0_sb6x f1_sb6x f2_sb6x a_wsb f0_sb6x f1_sb6x a_sup_set_class f2_sb6x a_sup_set_class a_wceq f0_sb6x a_wi f1_sb6x a_wal p_bitr4i $.
$}

$(If ` x ` is not free in ` ph ` , it is not free in ` [ y / x ] ph ` .
       (Contributed by Mario Carneiro, 11-Aug-2016.) $)

${
	$v ph x y  $.
	f0_nfs1f $f wff ph $.
	f1_nfs1f $f set x $.
	f2_nfs1f $f set y $.
	e0_nfs1f $e |- F/ x ph $.
	p_nfs1f $p |- F/ x [ y / x ] ph $= e0_nfs1f f0_nfs1f f1_nfs1f f2_nfs1f p_sbf e0_nfs1f f0_nfs1f f1_nfs1f f2_nfs1f a_wsb f0_nfs1f f1_nfs1f p_nfxfr $.
$}

$(Substitution does not change an identical variable specifier.
     (Contributed by NM, 5-Aug-1993.) $)

${
	$v x y z w  $.
	f0_sbequ5 $f set x $.
	f1_sbequ5 $f set y $.
	f2_sbequ5 $f set z $.
	f3_sbequ5 $f set w $.
	p_sbequ5 $p |- ( [ w / z ] A. x x = y <-> A. x x = y ) $= f0_sbequ5 f1_sbequ5 f2_sbequ5 p_nfae f0_sbequ5 a_sup_set_class f1_sbequ5 a_sup_set_class a_wceq f0_sbequ5 a_wal f2_sbequ5 f3_sbequ5 p_sbf $.
$}

$(Substitution does not change a distinctor.  (Contributed by NM,
     5-Aug-1993.) $)

${
	$v x y z w  $.
	f0_sbequ6 $f set x $.
	f1_sbequ6 $f set y $.
	f2_sbequ6 $f set z $.
	f3_sbequ6 $f set w $.
	p_sbequ6 $p |- ( [ w / z ] -. A. x x = y <-> -. A. x x = y ) $= f0_sbequ6 f1_sbequ6 f2_sbequ6 p_nfnae f0_sbequ6 a_sup_set_class f1_sbequ6 a_sup_set_class a_wceq f0_sbequ6 a_wal a_wn f2_sbequ6 f3_sbequ6 p_sbf $.
$}

$(A substitution into a theorem remains true.  (See ~ chvar and ~ chvarv
       for versions using implicit substitution.)  (Contributed by NM,
       21-Jan-2004.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)

${
	$v ph x y  $.
	f0_sbt $f wff ph $.
	f1_sbt $f set x $.
	f2_sbt $f set y $.
	e0_sbt $e |- ph $.
	p_sbt $p |- [ y / x ] ph $= e0_sbt e0_sbt f0_sbt f1_sbt p_nfth f0_sbt f1_sbt f2_sbt p_sbf f0_sbt f1_sbt f2_sbt a_wsb f0_sbt p_mpbir $.
$}

$(Substitution applied to an atomic wff.  (Contributed by NM,
     5-Aug-1993.) $)

${
	$v x y  $.
	f0_equsb1 $f set x $.
	f1_equsb1 $f set y $.
	p_equsb1 $p |- [ y / x ] x = y $= f0_equsb1 a_sup_set_class f1_equsb1 a_sup_set_class a_wceq f0_equsb1 f1_equsb1 p_sb2 f0_equsb1 a_sup_set_class f1_equsb1 a_sup_set_class a_wceq p_id f0_equsb1 a_sup_set_class f1_equsb1 a_sup_set_class a_wceq f0_equsb1 a_sup_set_class f1_equsb1 a_sup_set_class a_wceq a_wi f0_equsb1 a_sup_set_class f1_equsb1 a_sup_set_class a_wceq f0_equsb1 f1_equsb1 a_wsb f0_equsb1 p_mpg $.
$}

$(Substitution applied to an atomic wff.  (Contributed by NM,
     5-Aug-1993.) $)

${
	$v x y  $.
	f0_equsb2 $f set x $.
	f1_equsb2 $f set y $.
	p_equsb2 $p |- [ y / x ] y = x $= f1_equsb2 a_sup_set_class f0_equsb2 a_sup_set_class a_wceq f0_equsb2 f1_equsb2 p_sb2 f0_equsb2 f1_equsb2 p_equcomi f0_equsb2 a_sup_set_class f1_equsb2 a_sup_set_class a_wceq f1_equsb2 a_sup_set_class f0_equsb2 a_sup_set_class a_wceq a_wi f1_equsb2 a_sup_set_class f0_equsb2 a_sup_set_class a_wceq f0_equsb2 f1_equsb2 a_wsb f0_equsb2 p_mpg $.
$}

$(Conversion of implicit substitution to explicit substitution (deduction
       version of ~ sbie ).  (Contributed by NM, 30-Jun-1994.)  (Revised by
       Mario Carneiro, 4-Oct-2016.) $)

${
	$v ph ps ch x y  $.
	f0_sbied $f wff ph $.
	f1_sbied $f wff ps $.
	f2_sbied $f wff ch $.
	f3_sbied $f set x $.
	f4_sbied $f set y $.
	e0_sbied $e |- F/ x ph $.
	e1_sbied $e |- ( ph -> F/ x ch ) $.
	e2_sbied $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
	p_sbied $p |- ( ph -> ( [ y / x ] ps <-> ch ) ) $= f1_sbied f3_sbied f4_sbied p_sb1 e0_sbied e2_sbied f1_sbied f2_sbied p_bi1 f0_sbied f3_sbied a_sup_set_class f4_sbied a_sup_set_class a_wceq f1_sbied f2_sbied a_wb f1_sbied f2_sbied a_wi p_syl6 f0_sbied f3_sbied a_sup_set_class f4_sbied a_sup_set_class a_wceq f1_sbied f2_sbied p_imp3a f0_sbied f3_sbied a_sup_set_class f4_sbied a_sup_set_class a_wceq f1_sbied a_wa f2_sbied f3_sbied p_eximd f1_sbied f3_sbied f4_sbied a_wsb f3_sbied a_sup_set_class f4_sbied a_sup_set_class a_wceq f1_sbied a_wa f3_sbied a_wex f0_sbied f2_sbied f3_sbied a_wex p_syl5 e1_sbied f2_sbied f0_sbied f3_sbied p_19.9d f0_sbied f1_sbied f3_sbied f4_sbied a_wsb f2_sbied f3_sbied a_wex f2_sbied p_syld e1_sbied f0_sbied f2_sbied f3_sbied p_nfrd e0_sbied e2_sbied f1_sbied f2_sbied p_bi2 f0_sbied f3_sbied a_sup_set_class f4_sbied a_sup_set_class a_wceq f1_sbied f2_sbied a_wb f2_sbied f1_sbied a_wi p_syl6 f0_sbied f3_sbied a_sup_set_class f4_sbied a_sup_set_class a_wceq f2_sbied f1_sbied p_com23 f0_sbied f2_sbied f3_sbied a_sup_set_class f4_sbied a_sup_set_class a_wceq f1_sbied a_wi f3_sbied p_alimd f1_sbied f3_sbied f4_sbied p_sb2 f0_sbied f2_sbied f3_sbied a_wal f3_sbied a_sup_set_class f4_sbied a_sup_set_class a_wceq f1_sbied a_wi f3_sbied a_wal f1_sbied f3_sbied f4_sbied a_wsb p_syl6 f0_sbied f2_sbied f2_sbied f3_sbied a_wal f1_sbied f3_sbied f4_sbied a_wsb p_syld f0_sbied f1_sbied f3_sbied f4_sbied a_wsb f2_sbied p_impbid $.
$}

$(Conversion of implicit substitution to explicit substitution (deduction
       version of ~ sbie ).  (Contributed by NM, 7-Jan-2017.) $)

${
	$v ph ps ch x y  $.
	$d x ph  $.
	$d x ch  $.
	f0_sbiedv $f wff ph $.
	f1_sbiedv $f wff ps $.
	f2_sbiedv $f wff ch $.
	f3_sbiedv $f set x $.
	f4_sbiedv $f set y $.
	e0_sbiedv $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
	p_sbiedv $p |- ( ph -> ( [ y / x ] ps <-> ch ) ) $= f0_sbiedv f3_sbiedv p_nfv f0_sbiedv f2_sbiedv f3_sbiedv p_nfvd e0_sbiedv f0_sbiedv f3_sbiedv a_sup_set_class f4_sbiedv a_sup_set_class a_wceq f1_sbiedv f2_sbiedv a_wb p_ex f0_sbiedv f1_sbiedv f2_sbiedv f3_sbiedv f4_sbiedv p_sbied $.
$}

$(Conversion of implicit substitution to explicit substitution.
       (Contributed by NM, 30-Jun-1994.)  (Revised by Mario Carneiro,
       4-Oct-2016.) $)

${
	$v ph ps x y  $.
	f0_sbie $f wff ph $.
	f1_sbie $f wff ps $.
	f2_sbie $f set x $.
	f3_sbie $f set y $.
	e0_sbie $e |- F/ x ps $.
	e1_sbie $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_sbie $p |- ( [ y / x ] ph <-> ps ) $= f2_sbie p_nftru e0_sbie f1_sbie f2_sbie a_wnf a_wtru p_a1i e1_sbie f2_sbie a_sup_set_class f3_sbie a_sup_set_class a_wceq f0_sbie f1_sbie a_wb a_wi a_wtru p_a1i a_wtru f0_sbie f1_sbie f2_sbie f3_sbie p_sbied f0_sbie f2_sbie f3_sbie a_wsb f1_sbie a_wb p_trud $.
$}

$(Equivalence for substitution when ` y ` is not free in ` ph ` .
       (Contributed by NM, 5-Aug-1993.)  (Revised by Mario Carneiro,
       4-Oct-2016.) $)

${
	$v ph x y  $.
	f0_sb6f $f wff ph $.
	f1_sb6f $f set x $.
	f2_sb6f $f set y $.
	e0_sb6f $e |- F/ y ph $.
	p_sb6f $p |- ( [ y / x ] ph <-> A. x ( x = y -> ph ) ) $= e0_sb6f f0_sb6f f2_sb6f p_nfri f0_sb6f f0_sb6f f2_sb6f a_wal f1_sb6f f2_sb6f p_sbimi f0_sb6f f1_sb6f f2_sb6f p_sb4a f0_sb6f f1_sb6f f2_sb6f a_wsb f0_sb6f f2_sb6f a_wal f1_sb6f f2_sb6f a_wsb f1_sb6f a_sup_set_class f2_sb6f a_sup_set_class a_wceq f0_sb6f a_wi f1_sb6f a_wal p_syl f0_sb6f f1_sb6f f2_sb6f p_sb2 f0_sb6f f1_sb6f f2_sb6f a_wsb f1_sb6f a_sup_set_class f2_sb6f a_sup_set_class a_wceq f0_sb6f a_wi f1_sb6f a_wal p_impbii $.
$}

$(Equivalence for substitution when ` y ` is not free in ` ph ` .
       (Contributed by NM, 5-Aug-1993.)  (Revised by Mario Carneiro,
       4-Oct-2016.) $)

${
	$v ph x y  $.
	f0_sb5f $f wff ph $.
	f1_sb5f $f set x $.
	f2_sb5f $f set y $.
	e0_sb5f $e |- F/ y ph $.
	p_sb5f $p |- ( [ y / x ] ph <-> E. x ( x = y /\ ph ) ) $= e0_sb5f f0_sb5f f1_sb5f f2_sb5f p_sb6f e0_sb5f f0_sb5f f1_sb5f f2_sb5f p_equs45f f0_sb5f f1_sb5f f2_sb5f a_wsb f1_sb5f a_sup_set_class f2_sb5f a_sup_set_class a_wceq f0_sb5f a_wi f1_sb5f a_wal f1_sb5f a_sup_set_class f2_sb5f a_sup_set_class a_wceq f0_sb5f a_wa f1_sb5f a_wex p_bitr4i $.
$}

$(Special case of a bound-variable hypothesis builder for substitution.
     (Contributed by NM, 2-Feb-2007.) $)

${
	$v ph x y  $.
	f0_hbsb2a $f wff ph $.
	f1_hbsb2a $f set x $.
	f2_hbsb2a $f set y $.
	p_hbsb2a $p |- ( [ y / x ] A. y ph -> A. x [ y / x ] ph ) $= f0_hbsb2a f1_hbsb2a f2_hbsb2a p_sb4a f0_hbsb2a f1_hbsb2a f2_hbsb2a p_sb2 f1_hbsb2a a_sup_set_class f2_hbsb2a a_sup_set_class a_wceq f0_hbsb2a a_wi f0_hbsb2a f1_hbsb2a f2_hbsb2a a_wsb f1_hbsb2a p_a5i f0_hbsb2a f2_hbsb2a a_wal f1_hbsb2a f2_hbsb2a a_wsb f1_hbsb2a a_sup_set_class f2_hbsb2a a_sup_set_class a_wceq f0_hbsb2a a_wi f1_hbsb2a a_wal f0_hbsb2a f1_hbsb2a f2_hbsb2a a_wsb f1_hbsb2a a_wal p_syl $.
$}

$(Special case of a bound-variable hypothesis builder for substitution.
     (Contributed by NM, 2-Feb-2007.) $)

${
	$v ph x y  $.
	f0_hbsb2e $f wff ph $.
	f1_hbsb2e $f set x $.
	f2_hbsb2e $f set y $.
	p_hbsb2e $p |- ( [ y / x ] ph -> A. x [ y / x ] E. y ph ) $= f0_hbsb2e f1_hbsb2e f2_hbsb2e p_sb4e f0_hbsb2e f2_hbsb2e a_wex f1_hbsb2e f2_hbsb2e p_sb2 f1_hbsb2e a_sup_set_class f2_hbsb2e a_sup_set_class a_wceq f0_hbsb2e f2_hbsb2e a_wex a_wi f0_hbsb2e f2_hbsb2e a_wex f1_hbsb2e f2_hbsb2e a_wsb f1_hbsb2e p_a5i f0_hbsb2e f1_hbsb2e f2_hbsb2e a_wsb f1_hbsb2e a_sup_set_class f2_hbsb2e a_sup_set_class a_wceq f0_hbsb2e f2_hbsb2e a_wex a_wi f1_hbsb2e a_wal f0_hbsb2e f2_hbsb2e a_wex f1_hbsb2e f2_hbsb2e a_wsb f1_hbsb2e a_wal p_syl $.
$}

$(If ` y ` is not free in ` ph ` , ` x ` is not free in
       ` [ y / x ] ph ` .  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph x y  $.
	f0_hbsb3 $f wff ph $.
	f1_hbsb3 $f set x $.
	f2_hbsb3 $f set y $.
	e0_hbsb3 $e |- ( ph -> A. y ph ) $.
	p_hbsb3 $p |- ( [ y / x ] ph -> A. x [ y / x ] ph ) $= e0_hbsb3 f0_hbsb3 f0_hbsb3 f2_hbsb3 a_wal f1_hbsb3 f2_hbsb3 p_sbimi f0_hbsb3 f1_hbsb3 f2_hbsb3 p_hbsb2a f0_hbsb3 f1_hbsb3 f2_hbsb3 a_wsb f0_hbsb3 f2_hbsb3 a_wal f1_hbsb3 f2_hbsb3 a_wsb f0_hbsb3 f1_hbsb3 f2_hbsb3 a_wsb f1_hbsb3 a_wal p_syl $.
$}

$(If ` y ` is not free in ` ph ` , ` x ` is not free in
       ` [ y / x ] ph ` .  (Contributed by Mario Carneiro, 11-Aug-2016.) $)

${
	$v ph x y  $.
	f0_nfs1 $f wff ph $.
	f1_nfs1 $f set x $.
	f2_nfs1 $f set y $.
	e0_nfs1 $e |- F/ y ph $.
	p_nfs1 $p |- F/ x [ y / x ] ph $= e0_nfs1 f0_nfs1 f2_nfs1 p_nfri f0_nfs1 f1_nfs1 f2_nfs1 p_hbsb3 f0_nfs1 f1_nfs1 f2_nfs1 a_wsb f1_nfs1 p_nfi $.
$}

$(Proof of older axiom ~ ax-16 .  (Contributed by NM, 8-Nov-2006.)
       (Revised by NM, 22-Sep-2017.) $)

${
	$v ph x y  $.
	$d x y  $.
	$d ph  $.
	f0_ax16 $f wff ph $.
	f1_ax16 $f set x $.
	f2_ax16 $f set y $.
	p_ax16 $p |- ( A. x x = y -> ( ph -> A. x ph ) ) $= f0_ax16 f1_ax16 f2_ax16 f1_ax16 p_a16g $.
$}

$(Inference with ~ ax16 as its conclusion.  (Contributed by NM,
       20-May-2008.)  (Proof modification is discouraged.) $)

${
	$v ph ps x y z  $.
	$d x y z  $.
	$d z ph  $.
	f0_ax16i $f wff ph $.
	f1_ax16i $f wff ps $.
	f2_ax16i $f set x $.
	f3_ax16i $f set y $.
	f4_ax16i $f set z $.
	e0_ax16i $e |- ( x = z -> ( ph <-> ps ) ) $.
	e1_ax16i $e |- ( ps -> A. x ps ) $.
	p_ax16i $p |- ( A. x x = y -> ( ph -> A. x ph ) ) $= f2_ax16i a_sup_set_class f3_ax16i a_sup_set_class a_wceq f4_ax16i p_nfv f4_ax16i a_sup_set_class f3_ax16i a_sup_set_class a_wceq f2_ax16i p_nfv f2_ax16i f4_ax16i f3_ax16i a_ax-8 f2_ax16i a_sup_set_class f3_ax16i a_sup_set_class a_wceq f4_ax16i a_sup_set_class f3_ax16i a_sup_set_class a_wceq f2_ax16i f4_ax16i p_cbv3 f4_ax16i f2_ax16i f3_ax16i a_ax-8 f4_ax16i a_sup_set_class f3_ax16i a_sup_set_class a_wceq f2_ax16i a_sup_set_class f3_ax16i a_sup_set_class a_wceq f4_ax16i f2_ax16i p_spimv f2_ax16i f3_ax16i p_equcomi f4_ax16i f3_ax16i p_equcomi f3_ax16i f4_ax16i f2_ax16i a_ax-8 f4_ax16i a_sup_set_class f3_ax16i a_sup_set_class a_wceq f3_ax16i a_sup_set_class f4_ax16i a_sup_set_class a_wceq f3_ax16i a_sup_set_class f2_ax16i a_sup_set_class a_wceq f4_ax16i a_sup_set_class f2_ax16i a_sup_set_class a_wceq a_wi p_syl f2_ax16i a_sup_set_class f3_ax16i a_sup_set_class a_wceq f3_ax16i a_sup_set_class f2_ax16i a_sup_set_class a_wceq f4_ax16i a_sup_set_class f3_ax16i a_sup_set_class a_wceq f4_ax16i a_sup_set_class f2_ax16i a_sup_set_class a_wceq p_syl5com f2_ax16i a_sup_set_class f3_ax16i a_sup_set_class a_wceq f4_ax16i a_sup_set_class f3_ax16i a_sup_set_class a_wceq f4_ax16i a_sup_set_class f2_ax16i a_sup_set_class a_wceq f4_ax16i p_alimdv f2_ax16i a_sup_set_class f3_ax16i a_sup_set_class a_wceq f4_ax16i a_sup_set_class f3_ax16i a_sup_set_class a_wceq f4_ax16i a_wal f4_ax16i a_sup_set_class f2_ax16i a_sup_set_class a_wceq f4_ax16i a_wal p_mpcom f4_ax16i f2_ax16i p_equcomi f4_ax16i a_sup_set_class f2_ax16i a_sup_set_class a_wceq f2_ax16i a_sup_set_class f4_ax16i a_sup_set_class a_wceq f4_ax16i p_alimi f4_ax16i a_sup_set_class f3_ax16i a_sup_set_class a_wceq f4_ax16i a_wal f4_ax16i a_sup_set_class f2_ax16i a_sup_set_class a_wceq f4_ax16i a_wal f2_ax16i a_sup_set_class f4_ax16i a_sup_set_class a_wceq f4_ax16i a_wal p_syl e0_ax16i f2_ax16i a_sup_set_class f4_ax16i a_sup_set_class a_wceq f0_ax16i f1_ax16i p_biimpcd f0_ax16i f2_ax16i a_sup_set_class f4_ax16i a_sup_set_class a_wceq f1_ax16i f4_ax16i p_alimdv e1_ax16i f1_ax16i f2_ax16i p_nfi f0_ax16i f4_ax16i p_nfv f4_ax16i f2_ax16i p_equcomi e0_ax16i f2_ax16i a_sup_set_class f4_ax16i a_sup_set_class a_wceq f0_ax16i f1_ax16i p_biimprd f4_ax16i a_sup_set_class f2_ax16i a_sup_set_class a_wceq f2_ax16i a_sup_set_class f4_ax16i a_sup_set_class a_wceq f1_ax16i f0_ax16i a_wi p_syl f1_ax16i f0_ax16i f4_ax16i f2_ax16i p_cbv3 f0_ax16i f2_ax16i a_sup_set_class f4_ax16i a_sup_set_class a_wceq f4_ax16i a_wal f1_ax16i f4_ax16i a_wal f0_ax16i f2_ax16i a_wal p_syl6com f2_ax16i a_sup_set_class f3_ax16i a_sup_set_class a_wceq f2_ax16i a_wal f4_ax16i a_sup_set_class f3_ax16i a_sup_set_class a_wceq f4_ax16i a_wal f2_ax16i a_sup_set_class f4_ax16i a_sup_set_class a_wceq f4_ax16i a_wal f0_ax16i f0_ax16i f2_ax16i a_wal a_wi p_3syl $.
$}

$(Alternate proof of ~ ax16 .  (Contributed by NM, 17-May-2008.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)

${
	$v ph x y  $.
	$d x y z  $.
	$d z ph  $.
	f0_ax16ALT $f wff ph $.
	f1_ax16ALT $f set x $.
	f2_ax16ALT $f set y $.
	i0_ax16ALT $f set z $.
	p_ax16ALT $p |- ( A. x x = y -> ( ph -> A. x ph ) ) $= f0_ax16ALT f1_ax16ALT i0_ax16ALT p_sbequ12 f0_ax16ALT i0_ax16ALT a_ax-17 f0_ax16ALT f1_ax16ALT i0_ax16ALT p_hbsb3 f0_ax16ALT f0_ax16ALT f1_ax16ALT i0_ax16ALT a_wsb f1_ax16ALT f2_ax16ALT i0_ax16ALT p_ax16i $.
$}

$(Alternate proof of ~ ax16 .  (Contributed by NM, 8-Nov-2006.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)

${
	$v ph x y  $.
	$d x y  $.
	$d z ph  $.
	f0_ax16ALT2 $f wff ph $.
	f1_ax16ALT2 $f set x $.
	f2_ax16ALT2 $f set y $.
	i0_ax16ALT2 $f set z $.
	p_ax16ALT2 $p |- ( A. x x = y -> ( ph -> A. x ph ) ) $= f1_ax16ALT2 f2_ax16ALT2 i0_ax16ALT2 f1_ax16ALT2 i0_ax16ALT2 p_aev f0_ax16ALT2 f1_ax16ALT2 i0_ax16ALT2 p_sbequ12 f1_ax16ALT2 a_sup_set_class i0_ax16ALT2 a_sup_set_class a_wceq f0_ax16ALT2 f0_ax16ALT2 f1_ax16ALT2 i0_ax16ALT2 a_wsb p_biimpcd f0_ax16ALT2 f1_ax16ALT2 a_sup_set_class i0_ax16ALT2 a_sup_set_class a_wceq f0_ax16ALT2 f1_ax16ALT2 i0_ax16ALT2 a_wsb i0_ax16ALT2 p_alimdv f0_ax16ALT2 i0_ax16ALT2 p_nfv f0_ax16ALT2 f1_ax16ALT2 i0_ax16ALT2 p_nfs1 f0_ax16ALT2 i0_ax16ALT2 p_nfv f0_ax16ALT2 i0_ax16ALT2 f1_ax16ALT2 p_stdpc7 f0_ax16ALT2 f1_ax16ALT2 i0_ax16ALT2 a_wsb f0_ax16ALT2 i0_ax16ALT2 f1_ax16ALT2 p_cbv3 f0_ax16ALT2 f1_ax16ALT2 a_sup_set_class i0_ax16ALT2 a_sup_set_class a_wceq i0_ax16ALT2 a_wal f0_ax16ALT2 f1_ax16ALT2 i0_ax16ALT2 a_wsb i0_ax16ALT2 a_wal f0_ax16ALT2 f1_ax16ALT2 a_wal p_syl6com f1_ax16ALT2 a_sup_set_class f2_ax16ALT2 a_sup_set_class a_wceq f1_ax16ALT2 a_wal f1_ax16ALT2 a_sup_set_class i0_ax16ALT2 a_sup_set_class a_wceq i0_ax16ALT2 a_wal f0_ax16ALT2 f0_ax16ALT2 f1_ax16ALT2 a_wal a_wi p_syl $.
$}

$(A generalization of axiom ~ ax-16 .  Alternate proof of ~ a16g that uses
       ~ df-sb .  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew
       Salmon, 25-May-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)

${
	$v ph x y z  $.
	$d x y  $.
	f0_a16gALT $f wff ph $.
	f1_a16gALT $f set x $.
	f2_a16gALT $f set y $.
	f3_a16gALT $f set z $.
	p_a16gALT $p |- ( A. x x = y -> ( ph -> A. z ph ) ) $= f1_a16gALT f2_a16gALT f3_a16gALT f3_a16gALT f1_a16gALT p_aev f0_a16gALT f1_a16gALT f2_a16gALT p_ax16ALT2 f3_a16gALT a_sup_set_class f1_a16gALT a_sup_set_class a_wceq f3_a16gALT a_wal f0_a16gALT p_biidd f0_a16gALT f0_a16gALT f3_a16gALT f1_a16gALT p_dral1 f3_a16gALT a_sup_set_class f1_a16gALT a_sup_set_class a_wceq f3_a16gALT a_wal f0_a16gALT f3_a16gALT a_wal f0_a16gALT f1_a16gALT a_wal p_biimprd f1_a16gALT a_sup_set_class f2_a16gALT a_sup_set_class a_wceq f1_a16gALT a_wal f3_a16gALT a_sup_set_class f1_a16gALT a_sup_set_class a_wceq f3_a16gALT a_wal f0_a16gALT f0_a16gALT f1_a16gALT a_wal f0_a16gALT f3_a16gALT a_wal p_sylsyld $.
$}

$(A generalization of axiom ~ ax-16 .  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph x y z  $.
	$d x y  $.
	f0_a16gb $f wff ph $.
	f1_a16gb $f set x $.
	f2_a16gb $f set y $.
	f3_a16gb $f set z $.
	p_a16gb $p |- ( A. x x = y -> ( ph <-> A. z ph ) ) $= f0_a16gb f1_a16gb f2_a16gb f3_a16gb p_a16g f0_a16gb f3_a16gb p_sp f1_a16gb a_sup_set_class f2_a16gb a_sup_set_class a_wceq f1_a16gb a_wal f0_a16gb f0_a16gb f3_a16gb a_wal p_impbid1 $.
$}

$(If ~ dtru is false, then there is only one element in the universe, so
       everything satisfies ` F/ ` .  (Contributed by Mario Carneiro,
       7-Oct-2016.) $)

${
	$v ph x y z  $.
	$d x y  $.
	f0_a16nf $f wff ph $.
	f1_a16nf $f set x $.
	f2_a16nf $f set y $.
	f3_a16nf $f set z $.
	p_a16nf $p |- ( A. x x = y -> F/ z ph ) $= f1_a16nf f2_a16nf f3_a16nf p_nfae f0_a16nf f1_a16nf f2_a16nf f3_a16nf p_a16g f1_a16nf a_sup_set_class f2_a16nf a_sup_set_class a_wceq f1_a16nf a_wal f0_a16nf f3_a16nf p_nfd $.
$}

$(One direction of a simplified definition of substitution when variables
     are distinct.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph x y  $.
	f0_sb3 $f wff ph $.
	f1_sb3 $f set x $.
	f2_sb3 $f set y $.
	p_sb3 $p |- ( -. A. x x = y -> ( E. x ( x = y /\ ph ) -> [ y / x ] ph ) ) $= f0_sb3 f1_sb3 f2_sb3 p_equs5 f0_sb3 f1_sb3 f2_sb3 p_sb2 f1_sb3 a_sup_set_class f2_sb3 a_sup_set_class a_wceq f1_sb3 a_wal a_wn f1_sb3 a_sup_set_class f2_sb3 a_sup_set_class a_wceq f0_sb3 a_wa f1_sb3 a_wex f1_sb3 a_sup_set_class f2_sb3 a_sup_set_class a_wceq f0_sb3 a_wi f1_sb3 a_wal f0_sb3 f1_sb3 f2_sb3 a_wsb p_syl6 $.
$}

$(One direction of a simplified definition of substitution when variables
     are distinct.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph x y  $.
	f0_sb4 $f wff ph $.
	f1_sb4 $f set x $.
	f2_sb4 $f set y $.
	p_sb4 $p |- ( -. A. x x = y -> ( [ y / x ] ph -> A. x ( x = y -> ph ) ) ) $= f0_sb4 f1_sb4 f2_sb4 p_sb1 f0_sb4 f1_sb4 f2_sb4 p_equs5 f0_sb4 f1_sb4 f2_sb4 a_wsb f1_sb4 a_sup_set_class f2_sb4 a_sup_set_class a_wceq f0_sb4 a_wa f1_sb4 a_wex f1_sb4 a_sup_set_class f2_sb4 a_sup_set_class a_wceq f1_sb4 a_wal a_wn f1_sb4 a_sup_set_class f2_sb4 a_sup_set_class a_wceq f0_sb4 a_wi f1_sb4 a_wal p_syl5 $.
$}

$(Simplified definition of substitution when variables are distinct.
     (Contributed by NM, 27-May-1997.) $)

${
	$v ph x y  $.
	f0_sb4b $f wff ph $.
	f1_sb4b $f set x $.
	f2_sb4b $f set y $.
	p_sb4b $p |- ( -. A. x x = y -> ( [ y / x ] ph <-> A. x ( x = y -> ph ) ) ) $= f0_sb4b f1_sb4b f2_sb4b p_sb4 f0_sb4b f1_sb4b f2_sb4b p_sb2 f1_sb4b a_sup_set_class f2_sb4b a_sup_set_class a_wceq f1_sb4b a_wal a_wn f0_sb4b f1_sb4b f2_sb4b a_wsb f1_sb4b a_sup_set_class f2_sb4b a_sup_set_class a_wceq f0_sb4b a_wi f1_sb4b a_wal p_impbid1 $.
$}

$(An alternate definition of proper substitution that, like ~ df-sb , mixes
     free and bound variables to avoid distinct variable requirements.
     (Contributed by NM, 17-Feb-2005.) $)

${
	$v ph x y  $.
	f0_dfsb2 $f wff ph $.
	f1_dfsb2 $f set x $.
	f2_dfsb2 $f set y $.
	p_dfsb2 $p |- ( [ y / x ] ph <-> ( ( x = y /\ ph ) \/ A. x ( x = y -> ph ) ) ) $= f1_dfsb2 a_sup_set_class f2_dfsb2 a_sup_set_class a_wceq f1_dfsb2 p_sp f0_dfsb2 f1_dfsb2 f2_dfsb2 p_sbequ2 f1_dfsb2 a_sup_set_class f2_dfsb2 a_sup_set_class a_wceq f0_dfsb2 f1_dfsb2 f2_dfsb2 a_wsb f0_dfsb2 a_wi f1_dfsb2 p_sps f1_dfsb2 a_sup_set_class f2_dfsb2 a_sup_set_class a_wceq f0_dfsb2 a_wa f1_dfsb2 a_sup_set_class f2_dfsb2 a_sup_set_class a_wceq f0_dfsb2 a_wi f1_dfsb2 a_wal p_orc f1_dfsb2 a_sup_set_class f2_dfsb2 a_sup_set_class a_wceq f1_dfsb2 a_wal f1_dfsb2 a_sup_set_class f2_dfsb2 a_sup_set_class a_wceq f0_dfsb2 f1_dfsb2 f2_dfsb2 a_wsb f0_dfsb2 f1_dfsb2 a_sup_set_class f2_dfsb2 a_sup_set_class a_wceq f0_dfsb2 a_wa f1_dfsb2 a_sup_set_class f2_dfsb2 a_sup_set_class a_wceq f0_dfsb2 a_wi f1_dfsb2 a_wal a_wo p_ee12an f0_dfsb2 f1_dfsb2 f2_dfsb2 p_sb4 f1_dfsb2 a_sup_set_class f2_dfsb2 a_sup_set_class a_wceq f0_dfsb2 a_wi f1_dfsb2 a_wal f1_dfsb2 a_sup_set_class f2_dfsb2 a_sup_set_class a_wceq f0_dfsb2 a_wa p_olc f1_dfsb2 a_sup_set_class f2_dfsb2 a_sup_set_class a_wceq f1_dfsb2 a_wal a_wn f0_dfsb2 f1_dfsb2 f2_dfsb2 a_wsb f1_dfsb2 a_sup_set_class f2_dfsb2 a_sup_set_class a_wceq f0_dfsb2 a_wi f1_dfsb2 a_wal f1_dfsb2 a_sup_set_class f2_dfsb2 a_sup_set_class a_wceq f0_dfsb2 a_wa f1_dfsb2 a_sup_set_class f2_dfsb2 a_sup_set_class a_wceq f0_dfsb2 a_wi f1_dfsb2 a_wal a_wo p_syl6 f1_dfsb2 a_sup_set_class f2_dfsb2 a_sup_set_class a_wceq f1_dfsb2 a_wal f0_dfsb2 f1_dfsb2 f2_dfsb2 a_wsb f1_dfsb2 a_sup_set_class f2_dfsb2 a_sup_set_class a_wceq f0_dfsb2 a_wa f1_dfsb2 a_sup_set_class f2_dfsb2 a_sup_set_class a_wceq f0_dfsb2 a_wi f1_dfsb2 a_wal a_wo a_wi p_pm2.61i f0_dfsb2 f1_dfsb2 f2_dfsb2 p_sbequ1 f1_dfsb2 a_sup_set_class f2_dfsb2 a_sup_set_class a_wceq f0_dfsb2 f0_dfsb2 f1_dfsb2 f2_dfsb2 a_wsb p_imp f0_dfsb2 f1_dfsb2 f2_dfsb2 p_sb2 f1_dfsb2 a_sup_set_class f2_dfsb2 a_sup_set_class a_wceq f0_dfsb2 a_wa f0_dfsb2 f1_dfsb2 f2_dfsb2 a_wsb f1_dfsb2 a_sup_set_class f2_dfsb2 a_sup_set_class a_wceq f0_dfsb2 a_wi f1_dfsb2 a_wal p_jaoi f0_dfsb2 f1_dfsb2 f2_dfsb2 a_wsb f1_dfsb2 a_sup_set_class f2_dfsb2 a_sup_set_class a_wceq f0_dfsb2 a_wa f1_dfsb2 a_sup_set_class f2_dfsb2 a_sup_set_class a_wceq f0_dfsb2 a_wi f1_dfsb2 a_wal a_wo p_impbii $.
$}

$(An alternate definition of proper substitution ~ df-sb that uses only
     primitive connectives (no defined terms) on the right-hand side.
     (Contributed by NM, 6-Mar-2007.) $)

${
	$v ph x y  $.
	f0_dfsb3 $f wff ph $.
	f1_dfsb3 $f set x $.
	f2_dfsb3 $f set y $.
	p_dfsb3 $p |- ( [ y / x ] ph <-> ( ( x = y -> -. ph ) -> A. x ( x = y -> ph ) ) ) $= f1_dfsb3 a_sup_set_class f2_dfsb3 a_sup_set_class a_wceq f0_dfsb3 a_wa f1_dfsb3 a_sup_set_class f2_dfsb3 a_sup_set_class a_wceq f0_dfsb3 a_wi f1_dfsb3 a_wal a_df-or f0_dfsb3 f1_dfsb3 f2_dfsb3 p_dfsb2 f1_dfsb3 a_sup_set_class f2_dfsb3 a_sup_set_class a_wceq f0_dfsb3 p_imnan f1_dfsb3 a_sup_set_class f2_dfsb3 a_sup_set_class a_wceq f0_dfsb3 a_wn a_wi f1_dfsb3 a_sup_set_class f2_dfsb3 a_sup_set_class a_wceq f0_dfsb3 a_wa a_wn f1_dfsb3 a_sup_set_class f2_dfsb3 a_sup_set_class a_wceq f0_dfsb3 a_wi f1_dfsb3 a_wal p_imbi1i f1_dfsb3 a_sup_set_class f2_dfsb3 a_sup_set_class a_wceq f0_dfsb3 a_wa f1_dfsb3 a_sup_set_class f2_dfsb3 a_sup_set_class a_wceq f0_dfsb3 a_wi f1_dfsb3 a_wal a_wo f1_dfsb3 a_sup_set_class f2_dfsb3 a_sup_set_class a_wceq f0_dfsb3 a_wa a_wn f1_dfsb3 a_sup_set_class f2_dfsb3 a_sup_set_class a_wceq f0_dfsb3 a_wi f1_dfsb3 a_wal a_wi f0_dfsb3 f1_dfsb3 f2_dfsb3 a_wsb f1_dfsb3 a_sup_set_class f2_dfsb3 a_sup_set_class a_wceq f0_dfsb3 a_wn a_wi f1_dfsb3 a_sup_set_class f2_dfsb3 a_sup_set_class a_wceq f0_dfsb3 a_wi f1_dfsb3 a_wal a_wi p_3bitr4i $.
$}

$(Bound-variable hypothesis builder for substitution.  (Contributed by NM,
     5-Aug-1993.) $)

${
	$v ph x y  $.
	f0_hbsb2 $f wff ph $.
	f1_hbsb2 $f set x $.
	f2_hbsb2 $f set y $.
	p_hbsb2 $p |- ( -. A. x x = y -> ( [ y / x ] ph -> A. x [ y / x ] ph ) ) $= f0_hbsb2 f1_hbsb2 f2_hbsb2 p_sb4 f0_hbsb2 f1_hbsb2 f2_hbsb2 p_sb2 f1_hbsb2 a_sup_set_class f2_hbsb2 a_sup_set_class a_wceq f0_hbsb2 a_wi f0_hbsb2 f1_hbsb2 f2_hbsb2 a_wsb f1_hbsb2 p_a5i f1_hbsb2 a_sup_set_class f2_hbsb2 a_sup_set_class a_wceq f1_hbsb2 a_wal a_wn f0_hbsb2 f1_hbsb2 f2_hbsb2 a_wsb f1_hbsb2 a_sup_set_class f2_hbsb2 a_sup_set_class a_wceq f0_hbsb2 a_wi f1_hbsb2 a_wal f0_hbsb2 f1_hbsb2 f2_hbsb2 a_wsb f1_hbsb2 a_wal p_syl6 $.
$}

$(Bound-variable hypothesis builder for substitution.  (Contributed by Mario
     Carneiro, 4-Oct-2016.) $)

${
	$v ph x y  $.
	f0_nfsb2 $f wff ph $.
	f1_nfsb2 $f set x $.
	f2_nfsb2 $f set y $.
	p_nfsb2 $p |- ( -. A. x x = y -> F/ x [ y / x ] ph ) $= f1_nfsb2 f2_nfsb2 f1_nfsb2 p_nfnae f0_nfsb2 f1_nfsb2 f2_nfsb2 p_hbsb2 f1_nfsb2 a_sup_set_class f2_nfsb2 a_sup_set_class a_wceq f1_nfsb2 a_wal a_wn f0_nfsb2 f1_nfsb2 f2_nfsb2 a_wsb f1_nfsb2 p_nfd $.
$}

$(An equality theorem for substitution.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph x y z  $.
	f0_sbequi $f wff ph $.
	f1_sbequi $f set x $.
	f2_sbequi $f set y $.
	f3_sbequi $f set z $.
	p_sbequi $p |- ( x = y -> ( [ x / z ] ph -> [ y / z ] ph ) ) $= f0_sbequi f3_sbequi f1_sbequi p_hbsb2 f1_sbequi f2_sbequi f3_sbequi p_equvini f0_sbequi f1_sbequi f3_sbequi p_stdpc7 f0_sbequi f3_sbequi f2_sbequi p_sbequ1 f1_sbequi a_sup_set_class f3_sbequi a_sup_set_class a_wceq f0_sbequi f3_sbequi f1_sbequi a_wsb f0_sbequi f3_sbequi a_sup_set_class f2_sbequi a_sup_set_class a_wceq f0_sbequi f3_sbequi f2_sbequi a_wsb p_sylan9 f1_sbequi a_sup_set_class f3_sbequi a_sup_set_class a_wceq f3_sbequi a_sup_set_class f2_sbequi a_sup_set_class a_wceq a_wa f0_sbequi f3_sbequi f1_sbequi a_wsb f0_sbequi f3_sbequi f2_sbequi a_wsb a_wi f3_sbequi p_eximi f1_sbequi a_sup_set_class f2_sbequi a_sup_set_class a_wceq f1_sbequi a_sup_set_class f3_sbequi a_sup_set_class a_wceq f3_sbequi a_sup_set_class f2_sbequi a_sup_set_class a_wceq a_wa f3_sbequi a_wex f0_sbequi f3_sbequi f1_sbequi a_wsb f0_sbequi f3_sbequi f2_sbequi a_wsb a_wi f3_sbequi a_wex p_syl f0_sbequi f3_sbequi f1_sbequi a_wsb f0_sbequi f3_sbequi f2_sbequi a_wsb f3_sbequi p_19.35 f1_sbequi a_sup_set_class f2_sbequi a_sup_set_class a_wceq f0_sbequi f3_sbequi f1_sbequi a_wsb f0_sbequi f3_sbequi f2_sbequi a_wsb a_wi f3_sbequi a_wex f0_sbequi f3_sbequi f1_sbequi a_wsb f3_sbequi a_wal f0_sbequi f3_sbequi f2_sbequi a_wsb f3_sbequi a_wex a_wi p_sylib f3_sbequi a_sup_set_class f1_sbequi a_sup_set_class a_wceq f3_sbequi a_wal a_wn f0_sbequi f3_sbequi f1_sbequi a_wsb f0_sbequi f3_sbequi f1_sbequi a_wsb f3_sbequi a_wal f1_sbequi a_sup_set_class f2_sbequi a_sup_set_class a_wceq f0_sbequi f3_sbequi f2_sbequi a_wsb f3_sbequi a_wex p_sylan9 f0_sbequi f3_sbequi f2_sbequi p_nfsb2 f0_sbequi f3_sbequi f2_sbequi a_wsb f3_sbequi a_sup_set_class f2_sbequi a_sup_set_class a_wceq f3_sbequi a_wal a_wn f3_sbequi p_19.9d f3_sbequi a_sup_set_class f1_sbequi a_sup_set_class a_wceq f3_sbequi a_wal a_wn f1_sbequi a_sup_set_class f2_sbequi a_sup_set_class a_wceq a_wa f0_sbequi f3_sbequi f1_sbequi a_wsb f0_sbequi f3_sbequi f2_sbequi a_wsb f3_sbequi a_wex f3_sbequi a_sup_set_class f2_sbequi a_sup_set_class a_wceq f3_sbequi a_wal a_wn f0_sbequi f3_sbequi f2_sbequi a_wsb p_syl9 f3_sbequi a_sup_set_class f1_sbequi a_sup_set_class a_wceq f3_sbequi a_wal a_wn f1_sbequi a_sup_set_class f2_sbequi a_sup_set_class a_wceq f3_sbequi a_sup_set_class f2_sbequi a_sup_set_class a_wceq f3_sbequi a_wal a_wn f0_sbequi f3_sbequi f1_sbequi a_wsb f0_sbequi f3_sbequi f2_sbequi a_wsb a_wi a_wi p_ex f3_sbequi a_sup_set_class f1_sbequi a_sup_set_class a_wceq f3_sbequi a_wal a_wn f1_sbequi a_sup_set_class f2_sbequi a_sup_set_class a_wceq f3_sbequi a_sup_set_class f2_sbequi a_sup_set_class a_wceq f3_sbequi a_wal a_wn f0_sbequi f3_sbequi f1_sbequi a_wsb f0_sbequi f3_sbequi f2_sbequi a_wsb a_wi p_com23 f0_sbequi f3_sbequi f1_sbequi p_sbequ2 f3_sbequi a_sup_set_class f1_sbequi a_sup_set_class a_wceq f0_sbequi f3_sbequi f1_sbequi a_wsb f0_sbequi a_wi f3_sbequi p_sps f3_sbequi a_sup_set_class f1_sbequi a_sup_set_class a_wceq f3_sbequi a_wal f0_sbequi f3_sbequi f1_sbequi a_wsb f0_sbequi a_wi f1_sbequi a_sup_set_class f2_sbequi a_sup_set_class a_wceq p_adantr f0_sbequi f1_sbequi f2_sbequi p_sbequ1 f0_sbequi f3_sbequi f1_sbequi f2_sbequi p_drsb1 f3_sbequi a_sup_set_class f1_sbequi a_sup_set_class a_wceq f3_sbequi a_wal f0_sbequi f3_sbequi f2_sbequi a_wsb f0_sbequi f1_sbequi f2_sbequi a_wsb p_biimprd f1_sbequi a_sup_set_class f2_sbequi a_sup_set_class a_wceq f0_sbequi f0_sbequi f1_sbequi f2_sbequi a_wsb f3_sbequi a_sup_set_class f1_sbequi a_sup_set_class a_wceq f3_sbequi a_wal f0_sbequi f3_sbequi f2_sbequi a_wsb p_sylan9r f3_sbequi a_sup_set_class f1_sbequi a_sup_set_class a_wceq f3_sbequi a_wal f1_sbequi a_sup_set_class f2_sbequi a_sup_set_class a_wceq a_wa f0_sbequi f3_sbequi f1_sbequi a_wsb f0_sbequi f0_sbequi f3_sbequi f2_sbequi a_wsb p_syld f3_sbequi a_sup_set_class f1_sbequi a_sup_set_class a_wceq f3_sbequi a_wal f1_sbequi a_sup_set_class f2_sbequi a_sup_set_class a_wceq f0_sbequi f3_sbequi f1_sbequi a_wsb f0_sbequi f3_sbequi f2_sbequi a_wsb a_wi p_ex f0_sbequi f3_sbequi f2_sbequi f1_sbequi p_drsb1 f3_sbequi a_sup_set_class f2_sbequi a_sup_set_class a_wceq f3_sbequi a_wal f0_sbequi f3_sbequi f1_sbequi a_wsb f0_sbequi f2_sbequi f1_sbequi a_wsb p_biimpd f0_sbequi f1_sbequi f2_sbequi p_stdpc7 f3_sbequi a_sup_set_class f2_sbequi a_sup_set_class a_wceq f3_sbequi a_wal f0_sbequi f3_sbequi f1_sbequi a_wsb f0_sbequi f2_sbequi f1_sbequi a_wsb f1_sbequi a_sup_set_class f2_sbequi a_sup_set_class a_wceq f0_sbequi p_sylan9 f0_sbequi f3_sbequi f2_sbequi p_sbequ1 f3_sbequi a_sup_set_class f2_sbequi a_sup_set_class a_wceq f0_sbequi f0_sbequi f3_sbequi f2_sbequi a_wsb a_wi f3_sbequi p_sps f3_sbequi a_sup_set_class f2_sbequi a_sup_set_class a_wceq f3_sbequi a_wal f0_sbequi f0_sbequi f3_sbequi f2_sbequi a_wsb a_wi f1_sbequi a_sup_set_class f2_sbequi a_sup_set_class a_wceq p_adantr f3_sbequi a_sup_set_class f2_sbequi a_sup_set_class a_wceq f3_sbequi a_wal f1_sbequi a_sup_set_class f2_sbequi a_sup_set_class a_wceq a_wa f0_sbequi f3_sbequi f1_sbequi a_wsb f0_sbequi f0_sbequi f3_sbequi f2_sbequi a_wsb p_syld f3_sbequi a_sup_set_class f2_sbequi a_sup_set_class a_wceq f3_sbequi a_wal f1_sbequi a_sup_set_class f2_sbequi a_sup_set_class a_wceq f0_sbequi f3_sbequi f1_sbequi a_wsb f0_sbequi f3_sbequi f2_sbequi a_wsb a_wi p_ex f3_sbequi a_sup_set_class f1_sbequi a_sup_set_class a_wceq f3_sbequi a_wal f3_sbequi a_sup_set_class f2_sbequi a_sup_set_class a_wceq f3_sbequi a_wal f1_sbequi a_sup_set_class f2_sbequi a_sup_set_class a_wceq f0_sbequi f3_sbequi f1_sbequi a_wsb f0_sbequi f3_sbequi f2_sbequi a_wsb a_wi a_wi p_pm2.61ii $.
$}

$(An equality theorem for substitution.  Used in proof of Theorem 9.7 in
     [Megill] p. 449 (p. 16 of the preprint).  (Contributed by NM,
     5-Aug-1993.) $)

${
	$v ph x y z  $.
	f0_sbequ $f wff ph $.
	f1_sbequ $f set x $.
	f2_sbequ $f set y $.
	f3_sbequ $f set z $.
	p_sbequ $p |- ( x = y -> ( [ x / z ] ph <-> [ y / z ] ph ) ) $= f0_sbequ f1_sbequ f2_sbequ f3_sbequ p_sbequi f0_sbequ f2_sbequ f1_sbequ f3_sbequ p_sbequi f0_sbequ f3_sbequ f2_sbequ a_wsb f0_sbequ f3_sbequ f1_sbequ a_wsb a_wi f2_sbequ f1_sbequ p_equcoms f1_sbequ a_sup_set_class f2_sbequ a_sup_set_class a_wceq f0_sbequ f3_sbequ f1_sbequ a_wsb f0_sbequ f3_sbequ f2_sbequ a_wsb p_impbid $.
$}

$(Formula-building lemma for use with the Distinctor Reduction Theorem.
     Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).  (Contributed
     by NM, 27-Feb-2005.) $)

${
	$v ph x y z  $.
	f0_drsb2 $f wff ph $.
	f1_drsb2 $f set x $.
	f2_drsb2 $f set y $.
	f3_drsb2 $f set z $.
	p_drsb2 $p |- ( A. x x = y -> ( [ x / z ] ph <-> [ y / z ] ph ) ) $= f0_drsb2 f1_drsb2 f2_drsb2 f3_drsb2 p_sbequ f1_drsb2 a_sup_set_class f2_drsb2 a_sup_set_class a_wceq f0_drsb2 f3_drsb2 f1_drsb2 a_wsb f0_drsb2 f3_drsb2 f2_drsb2 a_wsb a_wb f1_drsb2 p_sps $.
$}

$(Negation inside and outside of substitution are equivalent.  (Contributed
     by NM, 5-Aug-1993.) $)

${
	$v ph x y  $.
	f0_sbn $f wff ph $.
	f1_sbn $f set x $.
	f2_sbn $f set y $.
	p_sbn $p |- ( [ y / x ] -. ph <-> -. [ y / x ] ph ) $= f0_sbn a_wn f1_sbn f2_sbn p_sbequ2 f0_sbn f1_sbn f2_sbn p_sbequ2 f1_sbn a_sup_set_class f2_sbn a_sup_set_class a_wceq f0_sbn a_wn f1_sbn f2_sbn a_wsb f0_sbn f0_sbn f1_sbn f2_sbn a_wsb p_nsyld f1_sbn a_sup_set_class f2_sbn a_sup_set_class a_wceq f0_sbn a_wn f1_sbn f2_sbn a_wsb f0_sbn f1_sbn f2_sbn a_wsb a_wn a_wi f1_sbn p_sps f0_sbn a_wn f1_sbn f2_sbn p_sb4 f0_sbn f1_sbn f2_sbn p_sb1 f0_sbn f1_sbn f2_sbn p_equs3 f0_sbn f1_sbn f2_sbn a_wsb f1_sbn a_sup_set_class f2_sbn a_sup_set_class a_wceq f0_sbn a_wa f1_sbn a_wex f1_sbn a_sup_set_class f2_sbn a_sup_set_class a_wceq f0_sbn a_wn a_wi f1_sbn a_wal a_wn p_sylib f0_sbn f1_sbn f2_sbn a_wsb f1_sbn a_sup_set_class f2_sbn a_sup_set_class a_wceq f0_sbn a_wn a_wi f1_sbn a_wal p_con2i f1_sbn a_sup_set_class f2_sbn a_sup_set_class a_wceq f1_sbn a_wal a_wn f0_sbn a_wn f1_sbn f2_sbn a_wsb f1_sbn a_sup_set_class f2_sbn a_sup_set_class a_wceq f0_sbn a_wn a_wi f1_sbn a_wal f0_sbn f1_sbn f2_sbn a_wsb a_wn p_syl6 f1_sbn a_sup_set_class f2_sbn a_sup_set_class a_wceq f1_sbn a_wal f0_sbn a_wn f1_sbn f2_sbn a_wsb f0_sbn f1_sbn f2_sbn a_wsb a_wn a_wi p_pm2.61i f0_sbn f1_sbn f2_sbn p_sbequ1 f1_sbn a_sup_set_class f2_sbn a_sup_set_class a_wceq f0_sbn f0_sbn f1_sbn f2_sbn a_wsb p_con3rr3 f0_sbn a_wn a_wn f1_sbn f2_sbn p_sb2 f0_sbn p_notnot f0_sbn f0_sbn a_wn a_wn f1_sbn f2_sbn p_sbbii f1_sbn a_sup_set_class f2_sbn a_sup_set_class a_wceq f0_sbn a_wn a_wn a_wi f1_sbn a_wal f0_sbn a_wn a_wn f1_sbn f2_sbn a_wsb f0_sbn f1_sbn f2_sbn a_wsb p_sylibr f1_sbn a_sup_set_class f2_sbn a_sup_set_class a_wceq f0_sbn a_wn a_wn a_wi f1_sbn a_wal f0_sbn f1_sbn f2_sbn a_wsb p_con3i f0_sbn a_wn f1_sbn f2_sbn p_equs3 f0_sbn f1_sbn f2_sbn a_wsb a_wn f1_sbn a_sup_set_class f2_sbn a_sup_set_class a_wceq f0_sbn a_wn a_wn a_wi f1_sbn a_wal a_wn f1_sbn a_sup_set_class f2_sbn a_sup_set_class a_wceq f0_sbn a_wn a_wa f1_sbn a_wex p_sylibr f0_sbn a_wn f1_sbn f2_sbn a_df-sb f0_sbn f1_sbn f2_sbn a_wsb a_wn f1_sbn a_sup_set_class f2_sbn a_sup_set_class a_wceq f0_sbn a_wn a_wi f1_sbn a_sup_set_class f2_sbn a_sup_set_class a_wceq f0_sbn a_wn a_wa f1_sbn a_wex f0_sbn a_wn f1_sbn f2_sbn a_wsb p_sylanbrc f0_sbn a_wn f1_sbn f2_sbn a_wsb f0_sbn f1_sbn f2_sbn a_wsb a_wn p_impbii $.
$}

$(Removal of implication from substitution.  (Contributed by NM,
     5-Aug-1993.) $)

${
	$v ph ps x y  $.
	f0_sbi1 $f wff ph $.
	f1_sbi1 $f wff ps $.
	f2_sbi1 $f set x $.
	f3_sbi1 $f set y $.
	p_sbi1 $p |- ( [ y / x ] ( ph -> ps ) -> ( [ y / x ] ph -> [ y / x ] ps ) ) $= f0_sbi1 f2_sbi1 f3_sbi1 p_sbequ2 f0_sbi1 f1_sbi1 a_wi f2_sbi1 f3_sbi1 p_sbequ2 f2_sbi1 a_sup_set_class f3_sbi1 a_sup_set_class a_wceq f0_sbi1 f2_sbi1 f3_sbi1 a_wsb f0_sbi1 f0_sbi1 f1_sbi1 a_wi f2_sbi1 f3_sbi1 a_wsb f1_sbi1 p_syl5d f1_sbi1 f2_sbi1 f3_sbi1 p_sbequ1 f2_sbi1 a_sup_set_class f3_sbi1 a_sup_set_class a_wceq f0_sbi1 f1_sbi1 a_wi f2_sbi1 f3_sbi1 a_wsb f0_sbi1 f2_sbi1 f3_sbi1 a_wsb f1_sbi1 f1_sbi1 f2_sbi1 f3_sbi1 a_wsb p_syl6d f2_sbi1 a_sup_set_class f3_sbi1 a_sup_set_class a_wceq f0_sbi1 f1_sbi1 a_wi f2_sbi1 f3_sbi1 a_wsb f0_sbi1 f2_sbi1 f3_sbi1 a_wsb f1_sbi1 f2_sbi1 f3_sbi1 a_wsb a_wi a_wi f2_sbi1 p_sps f0_sbi1 f2_sbi1 f3_sbi1 p_sb4 f0_sbi1 f1_sbi1 a_wi f2_sbi1 f3_sbi1 p_sb4 f2_sbi1 a_sup_set_class f3_sbi1 a_sup_set_class a_wceq f0_sbi1 f1_sbi1 a_ax-2 f2_sbi1 a_sup_set_class f3_sbi1 a_sup_set_class a_wceq f0_sbi1 f1_sbi1 a_wi a_wi f2_sbi1 a_sup_set_class f3_sbi1 a_sup_set_class a_wceq f0_sbi1 a_wi f2_sbi1 a_sup_set_class f3_sbi1 a_sup_set_class a_wceq f1_sbi1 a_wi f2_sbi1 p_al2imi f1_sbi1 f2_sbi1 f3_sbi1 p_sb2 f2_sbi1 a_sup_set_class f3_sbi1 a_sup_set_class a_wceq f0_sbi1 f1_sbi1 a_wi a_wi f2_sbi1 a_wal f2_sbi1 a_sup_set_class f3_sbi1 a_sup_set_class a_wceq f0_sbi1 a_wi f2_sbi1 a_wal f2_sbi1 a_sup_set_class f3_sbi1 a_sup_set_class a_wceq f1_sbi1 a_wi f2_sbi1 a_wal f1_sbi1 f2_sbi1 f3_sbi1 a_wsb p_syl6 f2_sbi1 a_sup_set_class f3_sbi1 a_sup_set_class a_wceq f2_sbi1 a_wal a_wn f0_sbi1 f1_sbi1 a_wi f2_sbi1 f3_sbi1 a_wsb f2_sbi1 a_sup_set_class f3_sbi1 a_sup_set_class a_wceq f0_sbi1 f1_sbi1 a_wi a_wi f2_sbi1 a_wal f2_sbi1 a_sup_set_class f3_sbi1 a_sup_set_class a_wceq f0_sbi1 a_wi f2_sbi1 a_wal f1_sbi1 f2_sbi1 f3_sbi1 a_wsb a_wi p_syl6 f2_sbi1 a_sup_set_class f3_sbi1 a_sup_set_class a_wceq f2_sbi1 a_wal a_wn f0_sbi1 f2_sbi1 f3_sbi1 a_wsb f2_sbi1 a_sup_set_class f3_sbi1 a_sup_set_class a_wceq f0_sbi1 a_wi f2_sbi1 a_wal f0_sbi1 f1_sbi1 a_wi f2_sbi1 f3_sbi1 a_wsb f1_sbi1 f2_sbi1 f3_sbi1 a_wsb p_syl5d f2_sbi1 a_sup_set_class f3_sbi1 a_sup_set_class a_wceq f2_sbi1 a_wal f0_sbi1 f1_sbi1 a_wi f2_sbi1 f3_sbi1 a_wsb f0_sbi1 f2_sbi1 f3_sbi1 a_wsb f1_sbi1 f2_sbi1 f3_sbi1 a_wsb a_wi a_wi p_pm2.61i $.
$}

$(Introduction of implication into substitution.  (Contributed by NM,
     5-Aug-1993.) $)

${
	$v ph ps x y  $.
	f0_sbi2 $f wff ph $.
	f1_sbi2 $f wff ps $.
	f2_sbi2 $f set x $.
	f3_sbi2 $f set y $.
	p_sbi2 $p |- ( ( [ y / x ] ph -> [ y / x ] ps ) -> [ y / x ] ( ph -> ps ) ) $= f0_sbi2 f2_sbi2 f3_sbi2 p_sbn f0_sbi2 f1_sbi2 p_pm2.21 f0_sbi2 a_wn f0_sbi2 f1_sbi2 a_wi f2_sbi2 f3_sbi2 p_sbimi f0_sbi2 f2_sbi2 f3_sbi2 a_wsb a_wn f0_sbi2 a_wn f2_sbi2 f3_sbi2 a_wsb f0_sbi2 f1_sbi2 a_wi f2_sbi2 f3_sbi2 a_wsb p_sylbir f1_sbi2 f0_sbi2 a_ax-1 f1_sbi2 f0_sbi2 f1_sbi2 a_wi f2_sbi2 f3_sbi2 p_sbimi f0_sbi2 f2_sbi2 f3_sbi2 a_wsb f1_sbi2 f2_sbi2 f3_sbi2 a_wsb f0_sbi2 f1_sbi2 a_wi f2_sbi2 f3_sbi2 a_wsb p_ja $.
$}

$(Implication inside and outside of substitution are equivalent.
     (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps x y  $.
	f0_sbim $f wff ph $.
	f1_sbim $f wff ps $.
	f2_sbim $f set x $.
	f3_sbim $f set y $.
	p_sbim $p |- ( [ y / x ] ( ph -> ps ) <-> ( [ y / x ] ph -> [ y / x ] ps ) ) $= f0_sbim f1_sbim f2_sbim f3_sbim p_sbi1 f0_sbim f1_sbim f2_sbim f3_sbim p_sbi2 f0_sbim f1_sbim a_wi f2_sbim f3_sbim a_wsb f0_sbim f2_sbim f3_sbim a_wsb f1_sbim f2_sbim f3_sbim a_wsb a_wi p_impbii $.
$}

$(Logical OR inside and outside of substitution are equivalent.
     (Contributed by NM, 29-Sep-2002.) $)

${
	$v ph ps x y  $.
	f0_sbor $f wff ph $.
	f1_sbor $f wff ps $.
	f2_sbor $f set x $.
	f3_sbor $f set y $.
	p_sbor $p |- ( [ y / x ] ( ph \/ ps ) <-> ( [ y / x ] ph \/ [ y / x ] ps ) ) $= f0_sbor a_wn f1_sbor f2_sbor f3_sbor p_sbim f0_sbor f2_sbor f3_sbor p_sbn f0_sbor a_wn f2_sbor f3_sbor a_wsb f0_sbor f2_sbor f3_sbor a_wsb a_wn f1_sbor f2_sbor f3_sbor a_wsb p_imbi1i f0_sbor a_wn f1_sbor a_wi f2_sbor f3_sbor a_wsb f0_sbor a_wn f2_sbor f3_sbor a_wsb f1_sbor f2_sbor f3_sbor a_wsb a_wi f0_sbor f2_sbor f3_sbor a_wsb a_wn f1_sbor f2_sbor f3_sbor a_wsb a_wi p_bitri f0_sbor f1_sbor a_df-or f0_sbor f1_sbor a_wo f0_sbor a_wn f1_sbor a_wi f2_sbor f3_sbor p_sbbii f0_sbor f2_sbor f3_sbor a_wsb f1_sbor f2_sbor f3_sbor a_wsb a_df-or f0_sbor a_wn f1_sbor a_wi f2_sbor f3_sbor a_wsb f0_sbor f2_sbor f3_sbor a_wsb a_wn f1_sbor f2_sbor f3_sbor a_wsb a_wi f0_sbor f1_sbor a_wo f2_sbor f3_sbor a_wsb f0_sbor f2_sbor f3_sbor a_wsb f1_sbor f2_sbor f3_sbor a_wsb a_wo p_3bitr4i $.
$}

$(Substitution with a variable not free in antecedent affects only the
       consequent.  (Contributed by NM, 5-Aug-1993.)  (Revised by Mario
       Carneiro, 4-Oct-2016.) $)

${
	$v ph ps x y  $.
	f0_sbrim $f wff ph $.
	f1_sbrim $f wff ps $.
	f2_sbrim $f set x $.
	f3_sbrim $f set y $.
	e0_sbrim $e |- F/ x ph $.
	p_sbrim $p |- ( [ y / x ] ( ph -> ps ) <-> ( ph -> [ y / x ] ps ) ) $= f0_sbrim f1_sbrim f2_sbrim f3_sbrim p_sbim e0_sbrim f0_sbrim f2_sbrim f3_sbrim p_sbf f0_sbrim f2_sbrim f3_sbrim a_wsb f0_sbrim f1_sbrim f2_sbrim f3_sbrim a_wsb p_imbi1i f0_sbrim f1_sbrim a_wi f2_sbrim f3_sbrim a_wsb f0_sbrim f2_sbrim f3_sbrim a_wsb f1_sbrim f2_sbrim f3_sbrim a_wsb a_wi f0_sbrim f1_sbrim f2_sbrim f3_sbrim a_wsb a_wi p_bitri $.
$}

$(Substitution with a variable not free in consequent affects only the
       antecedent.  (Contributed by NM, 14-Nov-2013.)  (Revised by Mario
       Carneiro, 4-Oct-2016.) $)

${
	$v ph ps x y  $.
	f0_sblim $f wff ph $.
	f1_sblim $f wff ps $.
	f2_sblim $f set x $.
	f3_sblim $f set y $.
	e0_sblim $e |- F/ x ps $.
	p_sblim $p |- ( [ y / x ] ( ph -> ps ) <-> ( [ y / x ] ph -> ps ) ) $= f0_sblim f1_sblim f2_sblim f3_sblim p_sbim e0_sblim f1_sblim f2_sblim f3_sblim p_sbf f1_sblim f2_sblim f3_sblim a_wsb f1_sblim f0_sblim f2_sblim f3_sblim a_wsb p_imbi2i f0_sblim f1_sblim a_wi f2_sblim f3_sblim a_wsb f0_sblim f2_sblim f3_sblim a_wsb f1_sblim f2_sblim f3_sblim a_wsb a_wi f0_sblim f2_sblim f3_sblim a_wsb f1_sblim a_wi p_bitri $.
$}

$(Conjunction inside and outside of a substitution are equivalent.
     (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps x y  $.
	f0_sban $f wff ph $.
	f1_sban $f wff ps $.
	f2_sban $f set x $.
	f3_sban $f set y $.
	p_sban $p |- ( [ y / x ] ( ph /\ ps ) <-> ( [ y / x ] ph /\ [ y / x ] ps ) ) $= f0_sban f1_sban a_wn a_wi f2_sban f3_sban p_sbn f0_sban f1_sban a_wn f2_sban f3_sban p_sbim f1_sban f2_sban f3_sban p_sbn f1_sban a_wn f2_sban f3_sban a_wsb f1_sban f2_sban f3_sban a_wsb a_wn f0_sban f2_sban f3_sban a_wsb p_imbi2i f0_sban f1_sban a_wn a_wi f2_sban f3_sban a_wsb f0_sban f2_sban f3_sban a_wsb f1_sban a_wn f2_sban f3_sban a_wsb a_wi f0_sban f2_sban f3_sban a_wsb f1_sban f2_sban f3_sban a_wsb a_wn a_wi p_bitri f0_sban f1_sban a_wn a_wi a_wn f2_sban f3_sban a_wsb f0_sban f1_sban a_wn a_wi f2_sban f3_sban a_wsb f0_sban f2_sban f3_sban a_wsb f1_sban f2_sban f3_sban a_wsb a_wn a_wi p_xchbinx f0_sban f1_sban a_df-an f0_sban f1_sban a_wa f0_sban f1_sban a_wn a_wi a_wn f2_sban f3_sban p_sbbii f0_sban f2_sban f3_sban a_wsb f1_sban f2_sban f3_sban a_wsb a_df-an f0_sban f1_sban a_wn a_wi a_wn f2_sban f3_sban a_wsb f0_sban f2_sban f3_sban a_wsb f1_sban f2_sban f3_sban a_wsb a_wn a_wi a_wn f0_sban f1_sban a_wa f2_sban f3_sban a_wsb f0_sban f2_sban f3_sban a_wsb f1_sban f2_sban f3_sban a_wsb a_wa p_3bitr4i $.
$}

$(Conjunction inside and outside of a substitution are equivalent.
     (Contributed by NM, 14-Dec-2006.) $)

${
	$v ph ps ch x y  $.
	f0_sb3an $f wff ph $.
	f1_sb3an $f wff ps $.
	f2_sb3an $f wff ch $.
	f3_sb3an $f set x $.
	f4_sb3an $f set y $.
	p_sb3an $p |- ( [ y / x ] ( ph /\ ps /\ ch ) <-> ( [ y / x ] ph /\ [ y / x ] ps /\ [ y / x ] ch ) ) $= f0_sb3an f1_sb3an f2_sb3an a_df-3an f0_sb3an f1_sb3an f2_sb3an a_w3a f0_sb3an f1_sb3an a_wa f2_sb3an a_wa f3_sb3an f4_sb3an p_sbbii f0_sb3an f1_sb3an a_wa f2_sb3an f3_sb3an f4_sb3an p_sban f0_sb3an f1_sb3an f3_sb3an f4_sb3an p_sban f0_sb3an f1_sb3an a_wa f3_sb3an f4_sb3an a_wsb f0_sb3an f3_sb3an f4_sb3an a_wsb f1_sb3an f3_sb3an f4_sb3an a_wsb a_wa f2_sb3an f3_sb3an f4_sb3an a_wsb p_anbi1i f0_sb3an f3_sb3an f4_sb3an a_wsb f1_sb3an f3_sb3an f4_sb3an a_wsb f2_sb3an f3_sb3an f4_sb3an a_wsb a_df-3an f0_sb3an f1_sb3an a_wa f3_sb3an f4_sb3an a_wsb f2_sb3an f3_sb3an f4_sb3an a_wsb a_wa f0_sb3an f3_sb3an f4_sb3an a_wsb f1_sb3an f3_sb3an f4_sb3an a_wsb a_wa f2_sb3an f3_sb3an f4_sb3an a_wsb a_wa f0_sb3an f3_sb3an f4_sb3an a_wsb f1_sb3an f3_sb3an f4_sb3an a_wsb f2_sb3an f3_sb3an f4_sb3an a_wsb a_w3a p_bitr4i f0_sb3an f1_sb3an f2_sb3an a_w3a f3_sb3an f4_sb3an a_wsb f0_sb3an f1_sb3an a_wa f2_sb3an a_wa f3_sb3an f4_sb3an a_wsb f0_sb3an f1_sb3an a_wa f3_sb3an f4_sb3an a_wsb f2_sb3an f3_sb3an f4_sb3an a_wsb a_wa f0_sb3an f3_sb3an f4_sb3an a_wsb f1_sb3an f3_sb3an f4_sb3an a_wsb f2_sb3an f3_sb3an f4_sb3an a_wsb a_w3a p_3bitri $.
$}

$(Equivalence inside and outside of a substitution are equivalent.
     (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps x y  $.
	f0_sbbi $f wff ph $.
	f1_sbbi $f wff ps $.
	f2_sbbi $f set x $.
	f3_sbbi $f set y $.
	p_sbbi $p |- ( [ y / x ] ( ph <-> ps ) <-> ( [ y / x ] ph <-> [ y / x ] ps ) ) $= f0_sbbi f1_sbbi p_dfbi2 f0_sbbi f1_sbbi a_wb f0_sbbi f1_sbbi a_wi f1_sbbi f0_sbbi a_wi a_wa f2_sbbi f3_sbbi p_sbbii f0_sbbi f1_sbbi f2_sbbi f3_sbbi p_sbim f1_sbbi f0_sbbi f2_sbbi f3_sbbi p_sbim f0_sbbi f1_sbbi a_wi f2_sbbi f3_sbbi a_wsb f0_sbbi f2_sbbi f3_sbbi a_wsb f1_sbbi f2_sbbi f3_sbbi a_wsb a_wi f1_sbbi f0_sbbi a_wi f2_sbbi f3_sbbi a_wsb f1_sbbi f2_sbbi f3_sbbi a_wsb f0_sbbi f2_sbbi f3_sbbi a_wsb a_wi p_anbi12i f0_sbbi f1_sbbi a_wi f1_sbbi f0_sbbi a_wi f2_sbbi f3_sbbi p_sban f0_sbbi f2_sbbi f3_sbbi a_wsb f1_sbbi f2_sbbi f3_sbbi a_wsb p_dfbi2 f0_sbbi f1_sbbi a_wi f2_sbbi f3_sbbi a_wsb f1_sbbi f0_sbbi a_wi f2_sbbi f3_sbbi a_wsb a_wa f0_sbbi f2_sbbi f3_sbbi a_wsb f1_sbbi f2_sbbi f3_sbbi a_wsb a_wi f1_sbbi f2_sbbi f3_sbbi a_wsb f0_sbbi f2_sbbi f3_sbbi a_wsb a_wi a_wa f0_sbbi f1_sbbi a_wi f1_sbbi f0_sbbi a_wi a_wa f2_sbbi f3_sbbi a_wsb f0_sbbi f2_sbbi f3_sbbi a_wsb f1_sbbi f2_sbbi f3_sbbi a_wsb a_wb p_3bitr4i f0_sbbi f1_sbbi a_wb f2_sbbi f3_sbbi a_wsb f0_sbbi f1_sbbi a_wi f1_sbbi f0_sbbi a_wi a_wa f2_sbbi f3_sbbi a_wsb f0_sbbi f2_sbbi f3_sbbi a_wsb f1_sbbi f2_sbbi f3_sbbi a_wsb a_wb p_bitri $.
$}

$(Introduce left biconditional inside of a substitution.  (Contributed by
       NM, 19-Aug-1993.) $)

${
	$v ph ps ch x y  $.
	f0_sblbis $f wff ph $.
	f1_sblbis $f wff ps $.
	f2_sblbis $f wff ch $.
	f3_sblbis $f set x $.
	f4_sblbis $f set y $.
	e0_sblbis $e |- ( [ y / x ] ph <-> ps ) $.
	p_sblbis $p |- ( [ y / x ] ( ch <-> ph ) <-> ( [ y / x ] ch <-> ps ) ) $= f2_sblbis f0_sblbis f3_sblbis f4_sblbis p_sbbi e0_sblbis f0_sblbis f3_sblbis f4_sblbis a_wsb f1_sblbis f2_sblbis f3_sblbis f4_sblbis a_wsb p_bibi2i f2_sblbis f0_sblbis a_wb f3_sblbis f4_sblbis a_wsb f2_sblbis f3_sblbis f4_sblbis a_wsb f0_sblbis f3_sblbis f4_sblbis a_wsb a_wb f2_sblbis f3_sblbis f4_sblbis a_wsb f1_sblbis a_wb p_bitri $.
$}

$(Introduce right biconditional inside of a substitution.  (Contributed by
       NM, 18-Aug-1993.) $)

${
	$v ph ps ch x y  $.
	f0_sbrbis $f wff ph $.
	f1_sbrbis $f wff ps $.
	f2_sbrbis $f wff ch $.
	f3_sbrbis $f set x $.
	f4_sbrbis $f set y $.
	e0_sbrbis $e |- ( [ y / x ] ph <-> ps ) $.
	p_sbrbis $p |- ( [ y / x ] ( ph <-> ch ) <-> ( ps <-> [ y / x ] ch ) ) $= f0_sbrbis f2_sbrbis f3_sbrbis f4_sbrbis p_sbbi e0_sbrbis f0_sbrbis f3_sbrbis f4_sbrbis a_wsb f1_sbrbis f2_sbrbis f3_sbrbis f4_sbrbis a_wsb p_bibi1i f0_sbrbis f2_sbrbis a_wb f3_sbrbis f4_sbrbis a_wsb f0_sbrbis f3_sbrbis f4_sbrbis a_wsb f2_sbrbis f3_sbrbis f4_sbrbis a_wsb a_wb f1_sbrbis f2_sbrbis f3_sbrbis f4_sbrbis a_wsb a_wb p_bitri $.
$}

$(Introduce right biconditional inside of a substitution.  (Contributed by
       NM, 18-Aug-1993.)  (Revised by Mario Carneiro, 4-Oct-2016.) $)

${
	$v ph ps ch x y  $.
	f0_sbrbif $f wff ph $.
	f1_sbrbif $f wff ps $.
	f2_sbrbif $f wff ch $.
	f3_sbrbif $f set x $.
	f4_sbrbif $f set y $.
	e0_sbrbif $e |- F/ x ch $.
	e1_sbrbif $e |- ( [ y / x ] ph <-> ps ) $.
	p_sbrbif $p |- ( [ y / x ] ( ph <-> ch ) <-> ( ps <-> ch ) ) $= e1_sbrbif f0_sbrbif f1_sbrbif f2_sbrbif f3_sbrbif f4_sbrbif p_sbrbis e0_sbrbif f2_sbrbif f3_sbrbif f4_sbrbif p_sbf f2_sbrbif f3_sbrbif f4_sbrbif a_wsb f2_sbrbif f1_sbrbif p_bibi2i f0_sbrbif f2_sbrbif a_wb f3_sbrbif f4_sbrbif a_wsb f1_sbrbif f2_sbrbif f3_sbrbif f4_sbrbif a_wsb a_wb f1_sbrbif f2_sbrbif a_wb p_bitri $.
$}

$(A specialization theorem.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph x y  $.
	f0_spsbe $f wff ph $.
	f1_spsbe $f set x $.
	f2_spsbe $f set y $.
	p_spsbe $p |- ( [ y / x ] ph -> E. x ph ) $= f0_spsbe a_wn f1_spsbe f2_spsbe p_stdpc4 f0_spsbe f1_spsbe f2_spsbe p_sbn f0_spsbe a_wn f1_spsbe a_wal f0_spsbe a_wn f1_spsbe f2_spsbe a_wsb f0_spsbe f1_spsbe f2_spsbe a_wsb a_wn p_sylib f0_spsbe a_wn f1_spsbe a_wal f0_spsbe f1_spsbe f2_spsbe a_wsb p_con2i f0_spsbe f1_spsbe a_df-ex f0_spsbe f1_spsbe f2_spsbe a_wsb f0_spsbe a_wn f1_spsbe a_wal a_wn f0_spsbe f1_spsbe a_wex p_sylibr $.
$}

$(Specialization of implication.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Andrew Salmon, 25-May-2011.) $)

${
	$v ph ps x y  $.
	f0_spsbim $f wff ph $.
	f1_spsbim $f wff ps $.
	f2_spsbim $f set x $.
	f3_spsbim $f set y $.
	p_spsbim $p |- ( A. x ( ph -> ps ) -> ( [ y / x ] ph -> [ y / x ] ps ) ) $= f0_spsbim f1_spsbim a_wi f2_spsbim f3_spsbim p_stdpc4 f0_spsbim f1_spsbim f2_spsbim f3_spsbim p_sbi1 f0_spsbim f1_spsbim a_wi f2_spsbim a_wal f0_spsbim f1_spsbim a_wi f2_spsbim f3_spsbim a_wsb f0_spsbim f2_spsbim f3_spsbim a_wsb f1_spsbim f2_spsbim f3_spsbim a_wsb a_wi p_syl $.
$}

$(Specialization of biconditional.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps x y  $.
	f0_spsbbi $f wff ph $.
	f1_spsbbi $f wff ps $.
	f2_spsbbi $f set x $.
	f3_spsbbi $f set y $.
	p_spsbbi $p |- ( A. x ( ph <-> ps ) -> ( [ y / x ] ph <-> [ y / x ] ps ) ) $= f0_spsbbi f1_spsbbi a_wb f2_spsbbi f3_spsbbi p_stdpc4 f0_spsbbi f1_spsbbi f2_spsbbi f3_spsbbi p_sbbi f0_spsbbi f1_spsbbi a_wb f2_spsbbi a_wal f0_spsbbi f1_spsbbi a_wb f2_spsbbi f3_spsbbi a_wsb f0_spsbbi f2_spsbbi f3_spsbbi a_wsb f1_spsbbi f2_spsbbi f3_spsbbi a_wsb a_wb p_sylib $.
$}

$(Deduction substituting both sides of a biconditional.  (Contributed by
       NM, 5-Aug-1993.) $)

${
	$v ph ps ch x y  $.
	f0_sbbid $f wff ph $.
	f1_sbbid $f wff ps $.
	f2_sbbid $f wff ch $.
	f3_sbbid $f set x $.
	f4_sbbid $f set y $.
	e0_sbbid $e |- F/ x ph $.
	e1_sbbid $e |- ( ph -> ( ps <-> ch ) ) $.
	p_sbbid $p |- ( ph -> ( [ y / x ] ps <-> [ y / x ] ch ) ) $= e0_sbbid e1_sbbid f0_sbbid f1_sbbid f2_sbbid a_wb f3_sbbid p_alrimi f1_sbbid f2_sbbid f3_sbbid f4_sbbid p_spsbbi f0_sbbid f1_sbbid f2_sbbid a_wb f3_sbbid a_wal f1_sbbid f3_sbbid f4_sbbid a_wsb f2_sbbid f3_sbbid f4_sbbid a_wsb a_wb p_syl $.
$}

$(Elimination of equality from antecedent after substitution.  (Contributed
     by NM, 5-Aug-1993.) $)

${
	$v ph x y  $.
	f0_sbequ8 $f wff ph $.
	f1_sbequ8 $f set x $.
	f2_sbequ8 $f set y $.
	p_sbequ8 $p |- ( [ y / x ] ph <-> [ y / x ] ( x = y -> ph ) ) $= f1_sbequ8 f2_sbequ8 p_equsb1 f1_sbequ8 a_sup_set_class f2_sbequ8 a_sup_set_class a_wceq f1_sbequ8 f2_sbequ8 a_wsb f0_sbequ8 f1_sbequ8 f2_sbequ8 a_wsb p_a1bi f1_sbequ8 a_sup_set_class f2_sbequ8 a_sup_set_class a_wceq f0_sbequ8 f1_sbequ8 f2_sbequ8 p_sbim f0_sbequ8 f1_sbequ8 f2_sbequ8 a_wsb f1_sbequ8 a_sup_set_class f2_sbequ8 a_sup_set_class a_wceq f1_sbequ8 f2_sbequ8 a_wsb f0_sbequ8 f1_sbequ8 f2_sbequ8 a_wsb a_wi f1_sbequ8 a_sup_set_class f2_sbequ8 a_sup_set_class a_wceq f0_sbequ8 a_wi f1_sbequ8 f2_sbequ8 a_wsb p_bitr4i $.
$}

$(A variable not free remains so after substitution with a distinct variable
     (closed form of ~ nfsb4 ).  (Contributed by NM, 7-Apr-2004.)  (Revised by
     Mario Carneiro, 4-Oct-2016.) $)

${
	$v ph x y z  $.
	f0_nfsb4t $f wff ph $.
	f1_nfsb4t $f set x $.
	f2_nfsb4t $f set y $.
	f3_nfsb4t $f set z $.
	p_nfsb4t $p |- ( A. x F/ z ph -> ( -. A. z z = y -> F/ z [ y / x ] ph ) ) $= f0_nfsb4t f1_nfsb4t f2_nfsb4t p_sbequ12 f1_nfsb4t a_sup_set_class f2_nfsb4t a_sup_set_class a_wceq f0_nfsb4t f0_nfsb4t f1_nfsb4t f2_nfsb4t a_wsb a_wb f1_nfsb4t p_sps f0_nfsb4t f0_nfsb4t f1_nfsb4t f2_nfsb4t a_wsb f1_nfsb4t f2_nfsb4t f3_nfsb4t p_drnf2 f1_nfsb4t a_sup_set_class f2_nfsb4t a_sup_set_class a_wceq f1_nfsb4t a_wal f0_nfsb4t f3_nfsb4t a_wnf f0_nfsb4t f1_nfsb4t f2_nfsb4t a_wsb f3_nfsb4t a_wnf p_biimpcd f0_nfsb4t f3_nfsb4t a_wnf f1_nfsb4t a_sup_set_class f2_nfsb4t a_sup_set_class a_wceq f1_nfsb4t a_wal f0_nfsb4t f1_nfsb4t f2_nfsb4t a_wsb f3_nfsb4t a_wnf a_wi f1_nfsb4t p_sps f0_nfsb4t f3_nfsb4t a_wnf f1_nfsb4t a_wal f1_nfsb4t a_sup_set_class f2_nfsb4t a_sup_set_class a_wceq f1_nfsb4t a_wal f0_nfsb4t f1_nfsb4t f2_nfsb4t a_wsb f3_nfsb4t a_wnf f3_nfsb4t a_sup_set_class f1_nfsb4t a_sup_set_class a_wceq f3_nfsb4t a_wal a_wn f3_nfsb4t a_sup_set_class f2_nfsb4t a_sup_set_class a_wceq f3_nfsb4t a_wal a_wn a_wa p_a1dd f0_nfsb4t f3_nfsb4t a_wnf f1_nfsb4t p_nfa1 f3_nfsb4t f1_nfsb4t f1_nfsb4t p_nfnae f3_nfsb4t f2_nfsb4t f1_nfsb4t p_nfnae f3_nfsb4t a_sup_set_class f1_nfsb4t a_sup_set_class a_wceq f3_nfsb4t a_wal a_wn f3_nfsb4t a_sup_set_class f2_nfsb4t a_sup_set_class a_wceq f3_nfsb4t a_wal a_wn f1_nfsb4t p_nfan f0_nfsb4t f3_nfsb4t a_wnf f1_nfsb4t a_wal f3_nfsb4t a_sup_set_class f1_nfsb4t a_sup_set_class a_wceq f3_nfsb4t a_wal a_wn f3_nfsb4t a_sup_set_class f2_nfsb4t a_sup_set_class a_wceq f3_nfsb4t a_wal a_wn a_wa f1_nfsb4t p_nfan f1_nfsb4t f2_nfsb4t f3_nfsb4t p_nfeqf f3_nfsb4t a_sup_set_class f1_nfsb4t a_sup_set_class a_wceq f3_nfsb4t a_wal a_wn f3_nfsb4t a_sup_set_class f2_nfsb4t a_sup_set_class a_wceq f3_nfsb4t a_wal a_wn a_wa f1_nfsb4t a_sup_set_class f2_nfsb4t a_sup_set_class a_wceq f3_nfsb4t a_wnf f0_nfsb4t f3_nfsb4t a_wnf f1_nfsb4t a_wal p_adantl f0_nfsb4t f3_nfsb4t a_wnf f1_nfsb4t p_sp f0_nfsb4t f3_nfsb4t a_wnf f1_nfsb4t a_wal f0_nfsb4t f3_nfsb4t a_wnf f3_nfsb4t a_sup_set_class f1_nfsb4t a_sup_set_class a_wceq f3_nfsb4t a_wal a_wn f3_nfsb4t a_sup_set_class f2_nfsb4t a_sup_set_class a_wceq f3_nfsb4t a_wal a_wn a_wa p_adantr f0_nfsb4t f3_nfsb4t a_wnf f1_nfsb4t a_wal f3_nfsb4t a_sup_set_class f1_nfsb4t a_sup_set_class a_wceq f3_nfsb4t a_wal a_wn f3_nfsb4t a_sup_set_class f2_nfsb4t a_sup_set_class a_wceq f3_nfsb4t a_wal a_wn a_wa a_wa f1_nfsb4t a_sup_set_class f2_nfsb4t a_sup_set_class a_wceq f0_nfsb4t f3_nfsb4t p_nfimd f0_nfsb4t f3_nfsb4t a_wnf f1_nfsb4t a_wal f3_nfsb4t a_sup_set_class f1_nfsb4t a_sup_set_class a_wceq f3_nfsb4t a_wal a_wn f3_nfsb4t a_sup_set_class f2_nfsb4t a_sup_set_class a_wceq f3_nfsb4t a_wal a_wn a_wa a_wa f1_nfsb4t a_sup_set_class f2_nfsb4t a_sup_set_class a_wceq f0_nfsb4t a_wi f3_nfsb4t f1_nfsb4t p_nfald f0_nfsb4t f3_nfsb4t a_wnf f1_nfsb4t a_wal f3_nfsb4t a_sup_set_class f1_nfsb4t a_sup_set_class a_wceq f3_nfsb4t a_wal a_wn f3_nfsb4t a_sup_set_class f2_nfsb4t a_sup_set_class a_wceq f3_nfsb4t a_wal a_wn a_wa f1_nfsb4t a_sup_set_class f2_nfsb4t a_sup_set_class a_wceq f0_nfsb4t a_wi f1_nfsb4t a_wal f3_nfsb4t a_wnf p_ex f1_nfsb4t f2_nfsb4t f3_nfsb4t p_nfnae f0_nfsb4t f1_nfsb4t f2_nfsb4t p_sb4b f1_nfsb4t a_sup_set_class f2_nfsb4t a_sup_set_class a_wceq f1_nfsb4t a_wal a_wn f0_nfsb4t f1_nfsb4t f2_nfsb4t a_wsb f1_nfsb4t a_sup_set_class f2_nfsb4t a_sup_set_class a_wceq f0_nfsb4t a_wi f1_nfsb4t a_wal f3_nfsb4t p_nfbidf f1_nfsb4t a_sup_set_class f2_nfsb4t a_sup_set_class a_wceq f1_nfsb4t a_wal a_wn f0_nfsb4t f1_nfsb4t f2_nfsb4t a_wsb f3_nfsb4t a_wnf f1_nfsb4t a_sup_set_class f2_nfsb4t a_sup_set_class a_wceq f0_nfsb4t a_wi f1_nfsb4t a_wal f3_nfsb4t a_wnf f3_nfsb4t a_sup_set_class f1_nfsb4t a_sup_set_class a_wceq f3_nfsb4t a_wal a_wn f3_nfsb4t a_sup_set_class f2_nfsb4t a_sup_set_class a_wceq f3_nfsb4t a_wal a_wn a_wa p_imbi2d f0_nfsb4t f3_nfsb4t a_wnf f1_nfsb4t a_wal f3_nfsb4t a_sup_set_class f1_nfsb4t a_sup_set_class a_wceq f3_nfsb4t a_wal a_wn f3_nfsb4t a_sup_set_class f2_nfsb4t a_sup_set_class a_wceq f3_nfsb4t a_wal a_wn a_wa f0_nfsb4t f1_nfsb4t f2_nfsb4t a_wsb f3_nfsb4t a_wnf a_wi f1_nfsb4t a_sup_set_class f2_nfsb4t a_sup_set_class a_wceq f1_nfsb4t a_wal a_wn f3_nfsb4t a_sup_set_class f1_nfsb4t a_sup_set_class a_wceq f3_nfsb4t a_wal a_wn f3_nfsb4t a_sup_set_class f2_nfsb4t a_sup_set_class a_wceq f3_nfsb4t a_wal a_wn a_wa f1_nfsb4t a_sup_set_class f2_nfsb4t a_sup_set_class a_wceq f0_nfsb4t a_wi f1_nfsb4t a_wal f3_nfsb4t a_wnf a_wi p_syl5ibrcom f0_nfsb4t f3_nfsb4t a_wnf f1_nfsb4t a_wal f1_nfsb4t a_sup_set_class f2_nfsb4t a_sup_set_class a_wceq f1_nfsb4t a_wal f3_nfsb4t a_sup_set_class f1_nfsb4t a_sup_set_class a_wceq f3_nfsb4t a_wal a_wn f3_nfsb4t a_sup_set_class f2_nfsb4t a_sup_set_class a_wceq f3_nfsb4t a_wal a_wn a_wa f0_nfsb4t f1_nfsb4t f2_nfsb4t a_wsb f3_nfsb4t a_wnf a_wi p_pm2.61d f0_nfsb4t f3_nfsb4t a_wnf f1_nfsb4t a_wal f3_nfsb4t a_sup_set_class f1_nfsb4t a_sup_set_class a_wceq f3_nfsb4t a_wal a_wn f3_nfsb4t a_sup_set_class f2_nfsb4t a_sup_set_class a_wceq f3_nfsb4t a_wal a_wn f0_nfsb4t f1_nfsb4t f2_nfsb4t a_wsb f3_nfsb4t a_wnf p_exp3a f0_nfsb4t f3_nfsb4t f2_nfsb4t p_nfsb2 f0_nfsb4t f3_nfsb4t f1_nfsb4t f2_nfsb4t p_drsb1 f0_nfsb4t f3_nfsb4t f2_nfsb4t a_wsb f0_nfsb4t f1_nfsb4t f2_nfsb4t a_wsb f3_nfsb4t f1_nfsb4t f3_nfsb4t p_drnf2 f3_nfsb4t a_sup_set_class f2_nfsb4t a_sup_set_class a_wceq f3_nfsb4t a_wal a_wn f0_nfsb4t f3_nfsb4t f2_nfsb4t a_wsb f3_nfsb4t a_wnf f3_nfsb4t a_sup_set_class f1_nfsb4t a_sup_set_class a_wceq f3_nfsb4t a_wal f0_nfsb4t f1_nfsb4t f2_nfsb4t a_wsb f3_nfsb4t a_wnf p_syl5ib f0_nfsb4t f3_nfsb4t a_wnf f1_nfsb4t a_wal f3_nfsb4t a_sup_set_class f1_nfsb4t a_sup_set_class a_wceq f3_nfsb4t a_wal f3_nfsb4t a_sup_set_class f2_nfsb4t a_sup_set_class a_wceq f3_nfsb4t a_wal a_wn f0_nfsb4t f1_nfsb4t f2_nfsb4t a_wsb f3_nfsb4t a_wnf a_wi p_pm2.61d2 $.
$}

$(A variable not free remains so after substitution with a distinct
       variable.  (Contributed by NM, 5-Aug-1993.)  (Revised by Mario Carneiro,
       4-Oct-2016.) $)

${
	$v ph x y z  $.
	f0_nfsb4 $f wff ph $.
	f1_nfsb4 $f set x $.
	f2_nfsb4 $f set y $.
	f3_nfsb4 $f set z $.
	e0_nfsb4 $e |- F/ z ph $.
	p_nfsb4 $p |- ( -. A. z z = y -> F/ z [ y / x ] ph ) $= f0_nfsb4 f1_nfsb4 f2_nfsb4 f3_nfsb4 p_nfsb4t e0_nfsb4 f0_nfsb4 f3_nfsb4 a_wnf f3_nfsb4 a_sup_set_class f2_nfsb4 a_sup_set_class a_wceq f3_nfsb4 a_wal a_wn f0_nfsb4 f1_nfsb4 f2_nfsb4 a_wsb f3_nfsb4 a_wnf a_wi f1_nfsb4 p_mpg $.
$}

$(Deduction form of ~ dvelimf .  This version may be useful if we want to
       avoid ~ ax-17 and use ~ ax-16 instead.  (Contributed by NM,
       7-Apr-2004.)  (Revised by Mario Carneiro, 6-Oct-2016.) $)

${
	$v ph ps ch x y z  $.
	f0_dvelimdf $f wff ph $.
	f1_dvelimdf $f wff ps $.
	f2_dvelimdf $f wff ch $.
	f3_dvelimdf $f set x $.
	f4_dvelimdf $f set y $.
	f5_dvelimdf $f set z $.
	e0_dvelimdf $e |- F/ x ph $.
	e1_dvelimdf $e |- F/ z ph $.
	e2_dvelimdf $e |- ( ph -> F/ x ps ) $.
	e3_dvelimdf $e |- ( ph -> F/ z ch ) $.
	e4_dvelimdf $e |- ( ph -> ( z = y -> ( ps <-> ch ) ) ) $.
	p_dvelimdf $p |- ( ph -> ( -. A. x x = y -> F/ x ch ) ) $= e1_dvelimdf e2_dvelimdf f0_dvelimdf f1_dvelimdf f3_dvelimdf a_wnf f5_dvelimdf p_alrimi f1_dvelimdf f5_dvelimdf f4_dvelimdf f3_dvelimdf p_nfsb4t f0_dvelimdf f1_dvelimdf f3_dvelimdf a_wnf f5_dvelimdf a_wal f3_dvelimdf a_sup_set_class f4_dvelimdf a_sup_set_class a_wceq f3_dvelimdf a_wal a_wn f1_dvelimdf f5_dvelimdf f4_dvelimdf a_wsb f3_dvelimdf a_wnf a_wi p_syl f0_dvelimdf f3_dvelimdf a_sup_set_class f4_dvelimdf a_sup_set_class a_wceq f3_dvelimdf a_wal a_wn f1_dvelimdf f5_dvelimdf f4_dvelimdf a_wsb f3_dvelimdf a_wnf p_imp e0_dvelimdf f3_dvelimdf f4_dvelimdf f3_dvelimdf p_nfnae f0_dvelimdf f3_dvelimdf a_sup_set_class f4_dvelimdf a_sup_set_class a_wceq f3_dvelimdf a_wal a_wn f3_dvelimdf p_nfan e1_dvelimdf e3_dvelimdf e4_dvelimdf f0_dvelimdf f1_dvelimdf f2_dvelimdf f5_dvelimdf f4_dvelimdf p_sbied f0_dvelimdf f1_dvelimdf f5_dvelimdf f4_dvelimdf a_wsb f2_dvelimdf a_wb f3_dvelimdf a_sup_set_class f4_dvelimdf a_sup_set_class a_wceq f3_dvelimdf a_wal a_wn p_adantr f0_dvelimdf f3_dvelimdf a_sup_set_class f4_dvelimdf a_sup_set_class a_wceq f3_dvelimdf a_wal a_wn a_wa f1_dvelimdf f5_dvelimdf f4_dvelimdf a_wsb f2_dvelimdf f3_dvelimdf p_nfbidf f0_dvelimdf f3_dvelimdf a_sup_set_class f4_dvelimdf a_sup_set_class a_wceq f3_dvelimdf a_wal a_wn a_wa f1_dvelimdf f5_dvelimdf f4_dvelimdf a_wsb f3_dvelimdf a_wnf f2_dvelimdf f3_dvelimdf a_wnf p_mpbid f0_dvelimdf f3_dvelimdf a_sup_set_class f4_dvelimdf a_sup_set_class a_wceq f3_dvelimdf a_wal a_wn f2_dvelimdf f3_dvelimdf a_wnf p_ex $.
$}

$(A composition law for substitution.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph x y  $.
	f0_sbco $f wff ph $.
	f1_sbco $f set x $.
	f2_sbco $f set y $.
	p_sbco $p |- ( [ y / x ] [ x / y ] ph <-> [ y / x ] ph ) $= f1_sbco f2_sbco p_equsb2 f0_sbco f2_sbco f1_sbco p_sbequ12 f2_sbco a_sup_set_class f1_sbco a_sup_set_class a_wceq f0_sbco f0_sbco f2_sbco f1_sbco a_wsb p_bicomd f2_sbco a_sup_set_class f1_sbco a_sup_set_class a_wceq f0_sbco f2_sbco f1_sbco a_wsb f0_sbco a_wb f1_sbco f2_sbco p_sbimi f2_sbco a_sup_set_class f1_sbco a_sup_set_class a_wceq f1_sbco f2_sbco a_wsb f0_sbco f2_sbco f1_sbco a_wsb f0_sbco a_wb f1_sbco f2_sbco a_wsb a_ax-mp f0_sbco f2_sbco f1_sbco a_wsb f0_sbco f1_sbco f2_sbco p_sbbi f0_sbco f2_sbco f1_sbco a_wsb f0_sbco a_wb f1_sbco f2_sbco a_wsb f0_sbco f2_sbco f1_sbco a_wsb f1_sbco f2_sbco a_wsb f0_sbco f1_sbco f2_sbco a_wsb a_wb p_mpbi $.
$}

$(An identity law for substitution.  (Contributed by NM, 5-Aug-1993.)
       (Revised by Mario Carneiro, 6-Oct-2016.) $)

${
	$v ph x y  $.
	f0_sbid2 $f wff ph $.
	f1_sbid2 $f set x $.
	f2_sbid2 $f set y $.
	e0_sbid2 $e |- F/ x ph $.
	p_sbid2 $p |- ( [ y / x ] [ x / y ] ph <-> ph ) $= f0_sbid2 f1_sbid2 f2_sbid2 p_sbco e0_sbid2 f0_sbid2 f1_sbid2 f2_sbid2 p_sbf f0_sbid2 f2_sbid2 f1_sbid2 a_wsb f1_sbid2 f2_sbid2 a_wsb f0_sbid2 f1_sbid2 f2_sbid2 a_wsb f0_sbid2 p_bitri $.
$}

$(An idempotent law for substitution.  (Contributed by NM, 30-Jun-1994.)
     (Proof shortened by Andrew Salmon, 25-May-2011.) $)

${
	$v ph x y  $.
	f0_sbidm $f wff ph $.
	f1_sbidm $f set x $.
	f2_sbidm $f set y $.
	p_sbidm $p |- ( [ y / x ] [ y / x ] ph <-> [ y / x ] ph ) $= f1_sbidm f2_sbidm p_equsb2 f0_sbidm f2_sbidm f1_sbidm p_sbequ12r f2_sbidm a_sup_set_class f1_sbidm a_sup_set_class a_wceq f0_sbidm f1_sbidm f2_sbidm a_wsb f0_sbidm a_wb f1_sbidm f2_sbidm p_sbimi f2_sbidm a_sup_set_class f1_sbidm a_sup_set_class a_wceq f1_sbidm f2_sbidm a_wsb f0_sbidm f1_sbidm f2_sbidm a_wsb f0_sbidm a_wb f1_sbidm f2_sbidm a_wsb a_ax-mp f0_sbidm f1_sbidm f2_sbidm a_wsb f0_sbidm f1_sbidm f2_sbidm p_sbbi f0_sbidm f1_sbidm f2_sbidm a_wsb f0_sbidm a_wb f1_sbidm f2_sbidm a_wsb f0_sbidm f1_sbidm f2_sbidm a_wsb f1_sbidm f2_sbidm a_wsb f0_sbidm f1_sbidm f2_sbidm a_wsb a_wb p_mpbi $.
$}

$(A composition law for substitution.  (Contributed by NM, 30-Jun-1994.)
       (Revised by Mario Carneiro, 6-Oct-2016.) $)

${
	$v ph x y z  $.
	f0_sbco2 $f wff ph $.
	f1_sbco2 $f set x $.
	f2_sbco2 $f set y $.
	f3_sbco2 $f set z $.
	e0_sbco2 $e |- F/ z ph $.
	p_sbco2 $p |- ( [ y / z ] [ z / x ] ph <-> [ y / x ] ph ) $= e0_sbco2 f0_sbco2 f3_sbco2 f1_sbco2 p_sbid2 f0_sbco2 f1_sbco2 f3_sbco2 a_wsb f1_sbco2 f2_sbco2 f3_sbco2 p_sbequ f0_sbco2 f0_sbco2 f1_sbco2 f3_sbco2 a_wsb f3_sbco2 f1_sbco2 a_wsb f1_sbco2 a_sup_set_class f2_sbco2 a_sup_set_class a_wceq f0_sbco2 f1_sbco2 f3_sbco2 a_wsb f3_sbco2 f2_sbco2 a_wsb p_syl5bbr f0_sbco2 f1_sbco2 f2_sbco2 p_sbequ12 f1_sbco2 a_sup_set_class f2_sbco2 a_sup_set_class a_wceq f0_sbco2 f0_sbco2 f1_sbco2 f3_sbco2 a_wsb f3_sbco2 f2_sbco2 a_wsb f0_sbco2 f1_sbco2 f2_sbco2 a_wsb p_bitr3d f1_sbco2 a_sup_set_class f2_sbco2 a_sup_set_class a_wceq f0_sbco2 f1_sbco2 f3_sbco2 a_wsb f3_sbco2 f2_sbco2 a_wsb f0_sbco2 f1_sbco2 f2_sbco2 a_wsb a_wb f1_sbco2 p_sps f1_sbco2 f2_sbco2 f1_sbco2 p_nfnae e0_sbco2 f0_sbco2 f1_sbco2 f3_sbco2 p_nfs1 f0_sbco2 f1_sbco2 f3_sbco2 a_wsb f3_sbco2 f2_sbco2 f1_sbco2 p_nfsb4 e0_sbco2 f0_sbco2 f3_sbco2 f1_sbco2 p_sbid2 f0_sbco2 f1_sbco2 f3_sbco2 a_wsb f1_sbco2 f2_sbco2 f3_sbco2 p_sbequ f0_sbco2 f0_sbco2 f1_sbco2 f3_sbco2 a_wsb f3_sbco2 f1_sbco2 a_wsb f1_sbco2 a_sup_set_class f2_sbco2 a_sup_set_class a_wceq f0_sbco2 f1_sbco2 f3_sbco2 a_wsb f3_sbco2 f2_sbco2 a_wsb p_syl5bbr f1_sbco2 a_sup_set_class f2_sbco2 a_sup_set_class a_wceq f0_sbco2 f0_sbco2 f1_sbco2 f3_sbco2 a_wsb f3_sbco2 f2_sbco2 a_wsb a_wb a_wi f1_sbco2 a_sup_set_class f2_sbco2 a_sup_set_class a_wceq f1_sbco2 a_wal a_wn p_a1i f1_sbco2 a_sup_set_class f2_sbco2 a_sup_set_class a_wceq f1_sbco2 a_wal a_wn f0_sbco2 f0_sbco2 f1_sbco2 f3_sbco2 a_wsb f3_sbco2 f2_sbco2 a_wsb f1_sbco2 f2_sbco2 p_sbied f1_sbco2 a_sup_set_class f2_sbco2 a_sup_set_class a_wceq f1_sbco2 a_wal a_wn f0_sbco2 f1_sbco2 f2_sbco2 a_wsb f0_sbco2 f1_sbco2 f3_sbco2 a_wsb f3_sbco2 f2_sbco2 a_wsb p_bicomd f1_sbco2 a_sup_set_class f2_sbco2 a_sup_set_class a_wceq f1_sbco2 a_wal f0_sbco2 f1_sbco2 f3_sbco2 a_wsb f3_sbco2 f2_sbco2 a_wsb f0_sbco2 f1_sbco2 f2_sbco2 a_wsb a_wb p_pm2.61i $.
$}

$(A composition law for substitution.  (Contributed by NM, 5-Aug-1993.)
       (Revised by Mario Carneiro, 6-Oct-2016.) $)

${
	$v ph ps x y z  $.
	f0_sbco2d $f wff ph $.
	f1_sbco2d $f wff ps $.
	f2_sbco2d $f set x $.
	f3_sbco2d $f set y $.
	f4_sbco2d $f set z $.
	e0_sbco2d $e |- F/ x ph $.
	e1_sbco2d $e |- F/ z ph $.
	e2_sbco2d $e |- ( ph -> F/ z ps ) $.
	p_sbco2d $p |- ( ph -> ( [ y / z ] [ z / x ] ps <-> [ y / x ] ps ) ) $= e1_sbco2d e2_sbco2d f0_sbco2d f1_sbco2d f4_sbco2d p_nfim1 f0_sbco2d f1_sbco2d a_wi f2_sbco2d f3_sbco2d f4_sbco2d p_sbco2 e0_sbco2d f0_sbco2d f1_sbco2d f2_sbco2d f4_sbco2d p_sbrim f0_sbco2d f1_sbco2d a_wi f2_sbco2d f4_sbco2d a_wsb f0_sbco2d f1_sbco2d f2_sbco2d f4_sbco2d a_wsb a_wi f4_sbco2d f3_sbco2d p_sbbii e1_sbco2d f0_sbco2d f1_sbco2d f2_sbco2d f4_sbco2d a_wsb f4_sbco2d f3_sbco2d p_sbrim f0_sbco2d f1_sbco2d a_wi f2_sbco2d f4_sbco2d a_wsb f4_sbco2d f3_sbco2d a_wsb f0_sbco2d f1_sbco2d f2_sbco2d f4_sbco2d a_wsb a_wi f4_sbco2d f3_sbco2d a_wsb f0_sbco2d f1_sbco2d f2_sbco2d f4_sbco2d a_wsb f4_sbco2d f3_sbco2d a_wsb a_wi p_bitri e0_sbco2d f0_sbco2d f1_sbco2d f2_sbco2d f3_sbco2d p_sbrim f0_sbco2d f1_sbco2d a_wi f2_sbco2d f4_sbco2d a_wsb f4_sbco2d f3_sbco2d a_wsb f0_sbco2d f1_sbco2d a_wi f2_sbco2d f3_sbco2d a_wsb f0_sbco2d f1_sbco2d f2_sbco2d f4_sbco2d a_wsb f4_sbco2d f3_sbco2d a_wsb a_wi f0_sbco2d f1_sbco2d f2_sbco2d f3_sbco2d a_wsb a_wi p_3bitr3i f0_sbco2d f1_sbco2d f2_sbco2d f4_sbco2d a_wsb f4_sbco2d f3_sbco2d a_wsb f1_sbco2d f2_sbco2d f3_sbco2d a_wsb p_pm5.74ri $.
$}

$(A composition law for substitution.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph x y z  $.
	f0_sbco3 $f wff ph $.
	f1_sbco3 $f set x $.
	f2_sbco3 $f set y $.
	f3_sbco3 $f set z $.
	p_sbco3 $p |- ( [ z / y ] [ y / x ] ph <-> [ z / x ] [ x / y ] ph ) $= f0_sbco3 f1_sbco3 f2_sbco3 a_wsb f1_sbco3 f2_sbco3 f3_sbco3 p_drsb1 f0_sbco3 f1_sbco3 f2_sbco3 p_sbequ12a f1_sbco3 a_sup_set_class f2_sbco3 a_sup_set_class a_wceq f0_sbco3 f1_sbco3 f2_sbco3 a_wsb f0_sbco3 f2_sbco3 f1_sbco3 a_wsb a_wb f1_sbco3 p_alimi f0_sbco3 f1_sbco3 f2_sbco3 a_wsb f0_sbco3 f2_sbco3 f1_sbco3 a_wsb f1_sbco3 f3_sbco3 p_spsbbi f1_sbco3 a_sup_set_class f2_sbco3 a_sup_set_class a_wceq f1_sbco3 a_wal f0_sbco3 f1_sbco3 f2_sbco3 a_wsb f0_sbco3 f2_sbco3 f1_sbco3 a_wsb a_wb f1_sbco3 a_wal f0_sbco3 f1_sbco3 f2_sbco3 a_wsb f1_sbco3 f3_sbco3 a_wsb f0_sbco3 f2_sbco3 f1_sbco3 a_wsb f1_sbco3 f3_sbco3 a_wsb a_wb p_syl f1_sbco3 a_sup_set_class f2_sbco3 a_sup_set_class a_wceq f1_sbco3 a_wal f0_sbco3 f1_sbco3 f2_sbco3 a_wsb f1_sbco3 f3_sbco3 a_wsb f0_sbco3 f1_sbco3 f2_sbco3 a_wsb f2_sbco3 f3_sbco3 a_wsb f0_sbco3 f2_sbco3 f1_sbco3 a_wsb f1_sbco3 f3_sbco3 a_wsb p_bitr3d f0_sbco3 f2_sbco3 f1_sbco3 p_sbco f0_sbco3 f1_sbco3 f2_sbco3 a_wsb f2_sbco3 f1_sbco3 a_wsb f0_sbco3 f2_sbco3 f1_sbco3 a_wsb f1_sbco3 f3_sbco3 p_sbbii f1_sbco3 f2_sbco3 f2_sbco3 p_nfnae f1_sbco3 f2_sbco3 f1_sbco3 p_nfnae f0_sbco3 f1_sbco3 f2_sbco3 p_nfsb2 f1_sbco3 a_sup_set_class f2_sbco3 a_sup_set_class a_wceq f1_sbco3 a_wal a_wn f0_sbco3 f1_sbco3 f2_sbco3 a_wsb f2_sbco3 f3_sbco3 f1_sbco3 p_sbco2d f0_sbco3 f2_sbco3 f1_sbco3 a_wsb f1_sbco3 f3_sbco3 a_wsb f0_sbco3 f1_sbco3 f2_sbco3 a_wsb f2_sbco3 f1_sbco3 a_wsb f1_sbco3 f3_sbco3 a_wsb f1_sbco3 a_sup_set_class f2_sbco3 a_sup_set_class a_wceq f1_sbco3 a_wal a_wn f0_sbco3 f1_sbco3 f2_sbco3 a_wsb f2_sbco3 f3_sbco3 a_wsb p_syl5rbbr f1_sbco3 a_sup_set_class f2_sbco3 a_sup_set_class a_wceq f1_sbco3 a_wal f0_sbco3 f1_sbco3 f2_sbco3 a_wsb f2_sbco3 f3_sbco3 a_wsb f0_sbco3 f2_sbco3 f1_sbco3 a_wsb f1_sbco3 f3_sbco3 a_wsb a_wb p_pm2.61i $.
$}

$(A commutativity law for substitution.  (Contributed by NM,
     27-May-1997.) $)

${
	$v ph x y z  $.
	f0_sbcom $f wff ph $.
	f1_sbcom $f set x $.
	f2_sbcom $f set y $.
	f3_sbcom $f set z $.
	p_sbcom $p |- ( [ y / z ] [ y / x ] ph <-> [ y / x ] [ y / z ] ph ) $= f0_sbcom f1_sbcom f2_sbcom a_wsb f1_sbcom f3_sbcom f2_sbcom p_drsb1 f1_sbcom f3_sbcom f1_sbcom p_nfae f0_sbcom f1_sbcom f3_sbcom f2_sbcom p_drsb1 f1_sbcom a_sup_set_class f3_sbcom a_sup_set_class a_wceq f1_sbcom a_wal f0_sbcom f1_sbcom f2_sbcom a_wsb f0_sbcom f3_sbcom f2_sbcom a_wsb f1_sbcom f2_sbcom p_sbbid f1_sbcom a_sup_set_class f3_sbcom a_sup_set_class a_wceq f1_sbcom a_wal f0_sbcom f1_sbcom f2_sbcom a_wsb f1_sbcom f2_sbcom a_wsb f0_sbcom f1_sbcom f2_sbcom a_wsb f3_sbcom f2_sbcom a_wsb f0_sbcom f3_sbcom f2_sbcom a_wsb f1_sbcom f2_sbcom a_wsb p_bitr3d f1_sbcom a_sup_set_class f3_sbcom a_sup_set_class a_wceq f1_sbcom a_wal f0_sbcom f1_sbcom f2_sbcom a_wsb f3_sbcom f2_sbcom a_wsb f0_sbcom f3_sbcom f2_sbcom a_wsb f1_sbcom f2_sbcom a_wsb a_wb f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f1_sbcom a_wal a_wn f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f3_sbcom a_wal a_wn a_wa p_adantr f1_sbcom f3_sbcom f3_sbcom p_nfnae f1_sbcom f2_sbcom f3_sbcom p_nfnae f1_sbcom a_sup_set_class f3_sbcom a_sup_set_class a_wceq f1_sbcom a_wal a_wn f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f1_sbcom a_wal a_wn f3_sbcom p_nfan f3_sbcom f2_sbcom f1_sbcom p_nfeqf f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f0_sbcom a_wi f1_sbcom p_19.21t f1_sbcom a_sup_set_class f3_sbcom a_sup_set_class a_wceq f1_sbcom a_wal a_wn f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f1_sbcom a_wal a_wn a_wa f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f1_sbcom a_wnf f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f0_sbcom a_wi a_wi f1_sbcom a_wal f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f0_sbcom a_wi f1_sbcom a_wal a_wi a_wb p_syl f1_sbcom a_sup_set_class f3_sbcom a_sup_set_class a_wceq f1_sbcom a_wal a_wn f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f1_sbcom a_wal a_wn a_wa f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f0_sbcom a_wi a_wi f1_sbcom a_wal f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f0_sbcom a_wi f1_sbcom a_wal a_wi f3_sbcom p_albid f1_sbcom a_sup_set_class f3_sbcom a_sup_set_class a_wceq f1_sbcom a_wal a_wn f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f1_sbcom a_wal a_wn f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f0_sbcom a_wi a_wi f1_sbcom a_wal f3_sbcom a_wal f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f0_sbcom a_wi f1_sbcom a_wal a_wi f3_sbcom a_wal a_wb f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f3_sbcom a_wal a_wn p_adantrr f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f0_sbcom a_wi a_wi f3_sbcom f1_sbcom p_alcom f1_sbcom f3_sbcom f1_sbcom p_nfnae f3_sbcom f2_sbcom f1_sbcom p_nfnae f1_sbcom a_sup_set_class f3_sbcom a_sup_set_class a_wceq f1_sbcom a_wal a_wn f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f3_sbcom a_wal a_wn f1_sbcom p_nfan f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f0_sbcom p_bi2.04 f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f0_sbcom a_wi a_wi f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f0_sbcom a_wi a_wi f3_sbcom p_albii f3_sbcom f1_sbcom p_aecom f3_sbcom a_sup_set_class f1_sbcom a_sup_set_class a_wceq f3_sbcom a_wal f1_sbcom a_sup_set_class f3_sbcom a_sup_set_class a_wceq f1_sbcom a_wal p_con3i f1_sbcom f2_sbcom f3_sbcom p_nfeqf f1_sbcom a_sup_set_class f3_sbcom a_sup_set_class a_wceq f1_sbcom a_wal a_wn f3_sbcom a_sup_set_class f1_sbcom a_sup_set_class a_wceq f3_sbcom a_wal a_wn f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f3_sbcom a_wal a_wn f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f3_sbcom a_wnf p_sylan f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f0_sbcom a_wi f3_sbcom p_19.21t f1_sbcom a_sup_set_class f3_sbcom a_sup_set_class a_wceq f1_sbcom a_wal a_wn f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f3_sbcom a_wal a_wn a_wa f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f3_sbcom a_wnf f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f0_sbcom a_wi a_wi f3_sbcom a_wal f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f0_sbcom a_wi f3_sbcom a_wal a_wi a_wb p_syl f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f0_sbcom a_wi a_wi f3_sbcom a_wal f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f0_sbcom a_wi a_wi f3_sbcom a_wal f1_sbcom a_sup_set_class f3_sbcom a_sup_set_class a_wceq f1_sbcom a_wal a_wn f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f3_sbcom a_wal a_wn a_wa f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f0_sbcom a_wi f3_sbcom a_wal a_wi p_syl5bb f1_sbcom a_sup_set_class f3_sbcom a_sup_set_class a_wceq f1_sbcom a_wal a_wn f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f3_sbcom a_wal a_wn a_wa f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f0_sbcom a_wi a_wi f3_sbcom a_wal f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f0_sbcom a_wi f3_sbcom a_wal a_wi f1_sbcom p_albid f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f0_sbcom a_wi a_wi f1_sbcom a_wal f3_sbcom a_wal f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f0_sbcom a_wi a_wi f3_sbcom a_wal f1_sbcom a_wal f1_sbcom a_sup_set_class f3_sbcom a_sup_set_class a_wceq f1_sbcom a_wal a_wn f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f3_sbcom a_wal a_wn a_wa f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f0_sbcom a_wi f3_sbcom a_wal a_wi f1_sbcom a_wal p_syl5bb f1_sbcom a_sup_set_class f3_sbcom a_sup_set_class a_wceq f1_sbcom a_wal a_wn f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f3_sbcom a_wal a_wn f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f0_sbcom a_wi a_wi f1_sbcom a_wal f3_sbcom a_wal f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f0_sbcom a_wi f3_sbcom a_wal a_wi f1_sbcom a_wal a_wb f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f1_sbcom a_wal a_wn p_adantrl f1_sbcom a_sup_set_class f3_sbcom a_sup_set_class a_wceq f1_sbcom a_wal a_wn f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f1_sbcom a_wal a_wn f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f3_sbcom a_wal a_wn a_wa a_wa f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f0_sbcom a_wi a_wi f1_sbcom a_wal f3_sbcom a_wal f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f0_sbcom a_wi f1_sbcom a_wal a_wi f3_sbcom a_wal f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f0_sbcom a_wi f3_sbcom a_wal a_wi f1_sbcom a_wal p_bitr3d f0_sbcom f1_sbcom f2_sbcom a_wsb f3_sbcom f2_sbcom p_sb4b f1_sbcom f2_sbcom f3_sbcom p_nfnae f0_sbcom f1_sbcom f2_sbcom p_sb4b f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f1_sbcom a_wal a_wn f0_sbcom f1_sbcom f2_sbcom a_wsb f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f0_sbcom a_wi f1_sbcom a_wal f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq p_imbi2d f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f1_sbcom a_wal a_wn f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f0_sbcom f1_sbcom f2_sbcom a_wsb a_wi f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f0_sbcom a_wi f1_sbcom a_wal a_wi f3_sbcom p_albid f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f3_sbcom a_wal a_wn f0_sbcom f1_sbcom f2_sbcom a_wsb f3_sbcom f2_sbcom a_wsb f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f0_sbcom f1_sbcom f2_sbcom a_wsb a_wi f3_sbcom a_wal f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f1_sbcom a_wal a_wn f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f0_sbcom a_wi f1_sbcom a_wal a_wi f3_sbcom a_wal p_sylan9bbr f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f1_sbcom a_wal a_wn f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f3_sbcom a_wal a_wn a_wa f0_sbcom f1_sbcom f2_sbcom a_wsb f3_sbcom f2_sbcom a_wsb f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f0_sbcom a_wi f1_sbcom a_wal a_wi f3_sbcom a_wal a_wb f1_sbcom a_sup_set_class f3_sbcom a_sup_set_class a_wceq f1_sbcom a_wal a_wn p_adantl f0_sbcom f3_sbcom f2_sbcom a_wsb f1_sbcom f2_sbcom p_sb4b f3_sbcom f2_sbcom f1_sbcom p_nfnae f0_sbcom f3_sbcom f2_sbcom p_sb4b f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f3_sbcom a_wal a_wn f0_sbcom f3_sbcom f2_sbcom a_wsb f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f0_sbcom a_wi f3_sbcom a_wal f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq p_imbi2d f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f3_sbcom a_wal a_wn f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f0_sbcom f3_sbcom f2_sbcom a_wsb a_wi f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f0_sbcom a_wi f3_sbcom a_wal a_wi f1_sbcom p_albid f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f1_sbcom a_wal a_wn f0_sbcom f3_sbcom f2_sbcom a_wsb f1_sbcom f2_sbcom a_wsb f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f0_sbcom f3_sbcom f2_sbcom a_wsb a_wi f1_sbcom a_wal f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f3_sbcom a_wal a_wn f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f0_sbcom a_wi f3_sbcom a_wal a_wi f1_sbcom a_wal p_sylan9bb f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f1_sbcom a_wal a_wn f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f3_sbcom a_wal a_wn a_wa f0_sbcom f3_sbcom f2_sbcom a_wsb f1_sbcom f2_sbcom a_wsb f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f0_sbcom a_wi f3_sbcom a_wal a_wi f1_sbcom a_wal a_wb f1_sbcom a_sup_set_class f3_sbcom a_sup_set_class a_wceq f1_sbcom a_wal a_wn p_adantl f1_sbcom a_sup_set_class f3_sbcom a_sup_set_class a_wceq f1_sbcom a_wal a_wn f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f1_sbcom a_wal a_wn f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f3_sbcom a_wal a_wn a_wa a_wa f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f0_sbcom a_wi f1_sbcom a_wal a_wi f3_sbcom a_wal f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f0_sbcom a_wi f3_sbcom a_wal a_wi f1_sbcom a_wal f0_sbcom f1_sbcom f2_sbcom a_wsb f3_sbcom f2_sbcom a_wsb f0_sbcom f3_sbcom f2_sbcom a_wsb f1_sbcom f2_sbcom a_wsb p_3bitr4d f1_sbcom a_sup_set_class f3_sbcom a_sup_set_class a_wceq f1_sbcom a_wal f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f1_sbcom a_wal a_wn f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f3_sbcom a_wal a_wn a_wa f0_sbcom f1_sbcom f2_sbcom a_wsb f3_sbcom f2_sbcom a_wsb f0_sbcom f3_sbcom f2_sbcom a_wsb f1_sbcom f2_sbcom a_wsb a_wb p_pm2.61ian f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f1_sbcom a_wal a_wn f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f3_sbcom a_wal a_wn f0_sbcom f1_sbcom f2_sbcom a_wsb f3_sbcom f2_sbcom a_wsb f0_sbcom f3_sbcom f2_sbcom a_wsb f1_sbcom f2_sbcom a_wsb a_wb p_ex f1_sbcom f2_sbcom f3_sbcom p_nfae f0_sbcom f1_sbcom f2_sbcom p_sbequ12 f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f0_sbcom f0_sbcom f1_sbcom f2_sbcom a_wsb a_wb f1_sbcom p_sps f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f1_sbcom a_wal f0_sbcom f0_sbcom f1_sbcom f2_sbcom a_wsb f3_sbcom f2_sbcom p_sbbid f0_sbcom f3_sbcom f2_sbcom a_wsb f1_sbcom f2_sbcom p_sbequ12 f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f0_sbcom f3_sbcom f2_sbcom a_wsb f0_sbcom f3_sbcom f2_sbcom a_wsb f1_sbcom f2_sbcom a_wsb a_wb f1_sbcom p_sps f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f1_sbcom a_wal f0_sbcom f3_sbcom f2_sbcom a_wsb f0_sbcom f1_sbcom f2_sbcom a_wsb f3_sbcom f2_sbcom a_wsb f0_sbcom f3_sbcom f2_sbcom a_wsb f1_sbcom f2_sbcom a_wsb p_bitr3d f0_sbcom f1_sbcom f2_sbcom a_wsb f3_sbcom f2_sbcom p_sbequ12 f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f0_sbcom f1_sbcom f2_sbcom a_wsb f0_sbcom f1_sbcom f2_sbcom a_wsb f3_sbcom f2_sbcom a_wsb a_wb f3_sbcom p_sps f3_sbcom f2_sbcom f1_sbcom p_nfae f0_sbcom f3_sbcom f2_sbcom p_sbequ12 f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f0_sbcom f0_sbcom f3_sbcom f2_sbcom a_wsb a_wb f3_sbcom p_sps f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f3_sbcom a_wal f0_sbcom f0_sbcom f3_sbcom f2_sbcom a_wsb f1_sbcom f2_sbcom p_sbbid f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f3_sbcom a_wal f0_sbcom f1_sbcom f2_sbcom a_wsb f0_sbcom f1_sbcom f2_sbcom a_wsb f3_sbcom f2_sbcom a_wsb f0_sbcom f3_sbcom f2_sbcom a_wsb f1_sbcom f2_sbcom a_wsb p_bitr3d f1_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f1_sbcom a_wal f3_sbcom a_sup_set_class f2_sbcom a_sup_set_class a_wceq f3_sbcom a_wal f0_sbcom f1_sbcom f2_sbcom a_wsb f3_sbcom f2_sbcom a_wsb f0_sbcom f3_sbcom f2_sbcom a_wsb f1_sbcom f2_sbcom a_wsb a_wb p_pm2.61ii $.
$}

$(Reversed substitution.  (Contributed by NM, 3-Feb-2005.)  (Revised by
       Mario Carneiro, 6-Oct-2016.) $)

${
	$v ph x y  $.
	f0_sb5rf $f wff ph $.
	f1_sb5rf $f set x $.
	f2_sb5rf $f set y $.
	e0_sb5rf $e |- F/ y ph $.
	p_sb5rf $p |- ( ph <-> E. y ( y = x /\ [ y / x ] ph ) ) $= e0_sb5rf f0_sb5rf f2_sb5rf f1_sb5rf p_sbid2 f0_sb5rf f1_sb5rf f2_sb5rf a_wsb f2_sb5rf f1_sb5rf p_sb1 f0_sb5rf f0_sb5rf f1_sb5rf f2_sb5rf a_wsb f2_sb5rf f1_sb5rf a_wsb f2_sb5rf a_sup_set_class f1_sb5rf a_sup_set_class a_wceq f0_sb5rf f1_sb5rf f2_sb5rf a_wsb a_wa f2_sb5rf a_wex p_sylbir e0_sb5rf f0_sb5rf f2_sb5rf f1_sb5rf p_stdpc7 f2_sb5rf a_sup_set_class f1_sb5rf a_sup_set_class a_wceq f0_sb5rf f1_sb5rf f2_sb5rf a_wsb f0_sb5rf p_imp f2_sb5rf a_sup_set_class f1_sb5rf a_sup_set_class a_wceq f0_sb5rf f1_sb5rf f2_sb5rf a_wsb a_wa f0_sb5rf f2_sb5rf p_exlimi f0_sb5rf f2_sb5rf a_sup_set_class f1_sb5rf a_sup_set_class a_wceq f0_sb5rf f1_sb5rf f2_sb5rf a_wsb a_wa f2_sb5rf a_wex p_impbii $.
$}

$(Reversed substitution.  (Contributed by NM, 5-Aug-1993.)  (Revised by
       Mario Carneiro, 6-Oct-2016.) $)

${
	$v ph x y  $.
	f0_sb6rf $f wff ph $.
	f1_sb6rf $f set x $.
	f2_sb6rf $f set y $.
	e0_sb6rf $e |- F/ y ph $.
	p_sb6rf $p |- ( ph <-> A. y ( y = x -> [ y / x ] ph ) ) $= e0_sb6rf f0_sb6rf f1_sb6rf f2_sb6rf p_sbequ1 f0_sb6rf f0_sb6rf f1_sb6rf f2_sb6rf a_wsb a_wi f1_sb6rf f2_sb6rf p_equcoms f2_sb6rf a_sup_set_class f1_sb6rf a_sup_set_class a_wceq f0_sb6rf f0_sb6rf f1_sb6rf f2_sb6rf a_wsb p_com12 f0_sb6rf f2_sb6rf a_sup_set_class f1_sb6rf a_sup_set_class a_wceq f0_sb6rf f1_sb6rf f2_sb6rf a_wsb a_wi f2_sb6rf p_alrimi f0_sb6rf f1_sb6rf f2_sb6rf a_wsb f2_sb6rf f1_sb6rf p_sb2 e0_sb6rf f0_sb6rf f2_sb6rf f1_sb6rf p_sbid2 f2_sb6rf a_sup_set_class f1_sb6rf a_sup_set_class a_wceq f0_sb6rf f1_sb6rf f2_sb6rf a_wsb a_wi f2_sb6rf a_wal f0_sb6rf f1_sb6rf f2_sb6rf a_wsb f2_sb6rf f1_sb6rf a_wsb f0_sb6rf p_sylib f0_sb6rf f2_sb6rf a_sup_set_class f1_sb6rf a_sup_set_class a_wceq f0_sb6rf f1_sb6rf f2_sb6rf a_wsb a_wi f2_sb6rf a_wal p_impbii $.
$}

$(Substitution of variable in universal quantifier.  (Contributed by NM,
       5-Aug-1993.)  (Revised by Mario Carneiro, 6-Oct-2016.) $)

${
	$v ph x y  $.
	f0_sb8 $f wff ph $.
	f1_sb8 $f set x $.
	f2_sb8 $f set y $.
	e0_sb8 $e |- F/ y ph $.
	p_sb8 $p |- ( A. x ph <-> A. y [ y / x ] ph ) $= e0_sb8 f0_sb8 f2_sb8 f1_sb8 p_nfal f0_sb8 f1_sb8 f2_sb8 p_stdpc4 f0_sb8 f1_sb8 a_wal f0_sb8 f1_sb8 f2_sb8 a_wsb f2_sb8 p_alrimi e0_sb8 f0_sb8 f1_sb8 f2_sb8 p_nfs1 e0_sb8 f0_sb8 f2_sb8 f1_sb8 p_stdpc7 f0_sb8 f1_sb8 f2_sb8 a_wsb f0_sb8 f2_sb8 f1_sb8 p_cbv3 f0_sb8 f1_sb8 a_wal f0_sb8 f1_sb8 f2_sb8 a_wsb f2_sb8 a_wal p_impbii $.
$}

$(Substitution of variable in existential quantifier.  (Contributed by NM,
       12-Aug-1993.)  (Revised by Mario Carneiro, 6-Oct-2016.) $)

${
	$v ph x y  $.
	f0_sb8e $f wff ph $.
	f1_sb8e $f set x $.
	f2_sb8e $f set y $.
	e0_sb8e $e |- F/ y ph $.
	p_sb8e $p |- ( E. x ph <-> E. y [ y / x ] ph ) $= e0_sb8e f0_sb8e f2_sb8e p_nfn f0_sb8e a_wn f1_sb8e f2_sb8e p_sb8 f0_sb8e f1_sb8e f2_sb8e p_sbn f0_sb8e a_wn f1_sb8e f2_sb8e a_wsb f0_sb8e f1_sb8e f2_sb8e a_wsb a_wn f2_sb8e p_albii f0_sb8e a_wn f1_sb8e a_wal f0_sb8e a_wn f1_sb8e f2_sb8e a_wsb f2_sb8e a_wal f0_sb8e f1_sb8e f2_sb8e a_wsb a_wn f2_sb8e a_wal p_bitri f0_sb8e a_wn f1_sb8e a_wal f0_sb8e f1_sb8e f2_sb8e a_wsb a_wn f2_sb8e a_wal p_notbii f0_sb8e f1_sb8e a_df-ex f0_sb8e f1_sb8e f2_sb8e a_wsb f2_sb8e a_df-ex f0_sb8e a_wn f1_sb8e a_wal a_wn f0_sb8e f1_sb8e f2_sb8e a_wsb a_wn f2_sb8e a_wal a_wn f0_sb8e f1_sb8e a_wex f0_sb8e f1_sb8e f2_sb8e a_wsb f2_sb8e a_wex p_3bitr4i $.
$}

$(Commutation of quantification and substitution variables.  (Contributed by
     NM, 5-Aug-1993.) $)

${
	$v ph x y  $.
	f0_sb9i $f wff ph $.
	f1_sb9i $f set x $.
	f2_sb9i $f set y $.
	p_sb9i $p |- ( A. x [ x / y ] ph -> A. y [ y / x ] ph ) $= f0_sb9i f2_sb9i f1_sb9i f2_sb9i p_drsb1 f0_sb9i f2_sb9i f1_sb9i f2_sb9i p_drsb2 f2_sb9i a_sup_set_class f1_sb9i a_sup_set_class a_wceq f2_sb9i a_wal f0_sb9i f2_sb9i f2_sb9i a_wsb f0_sb9i f1_sb9i f2_sb9i a_wsb f0_sb9i f2_sb9i f1_sb9i a_wsb p_bitr3d f0_sb9i f1_sb9i f2_sb9i a_wsb f0_sb9i f2_sb9i f1_sb9i a_wsb f2_sb9i f1_sb9i p_dral1 f2_sb9i a_sup_set_class f1_sb9i a_sup_set_class a_wceq f2_sb9i a_wal f0_sb9i f1_sb9i f2_sb9i a_wsb f2_sb9i a_wal f0_sb9i f2_sb9i f1_sb9i a_wsb f1_sb9i a_wal p_biimprd f2_sb9i f1_sb9i f1_sb9i p_nfnae f0_sb9i f2_sb9i f1_sb9i p_hbsb2 f2_sb9i a_sup_set_class f1_sb9i a_sup_set_class a_wceq f2_sb9i a_wal a_wn f0_sb9i f2_sb9i f1_sb9i a_wsb f0_sb9i f2_sb9i f1_sb9i a_wsb f2_sb9i a_wal f1_sb9i p_alimd f0_sb9i f2_sb9i f1_sb9i a_wsb f1_sb9i f2_sb9i p_stdpc4 f0_sb9i f1_sb9i f2_sb9i p_sbco f0_sb9i f2_sb9i f1_sb9i a_wsb f1_sb9i a_wal f0_sb9i f2_sb9i f1_sb9i a_wsb f1_sb9i f2_sb9i a_wsb f0_sb9i f1_sb9i f2_sb9i a_wsb p_sylib f0_sb9i f2_sb9i f1_sb9i a_wsb f1_sb9i a_wal f0_sb9i f1_sb9i f2_sb9i a_wsb f2_sb9i p_alimi f0_sb9i f2_sb9i f1_sb9i a_wsb f0_sb9i f1_sb9i f2_sb9i a_wsb f2_sb9i a_wal f2_sb9i f1_sb9i p_a7s f2_sb9i a_sup_set_class f1_sb9i a_sup_set_class a_wceq f2_sb9i a_wal a_wn f0_sb9i f2_sb9i f1_sb9i a_wsb f1_sb9i a_wal f0_sb9i f2_sb9i f1_sb9i a_wsb f2_sb9i a_wal f1_sb9i a_wal f0_sb9i f1_sb9i f2_sb9i a_wsb f2_sb9i a_wal p_syl6 f2_sb9i a_sup_set_class f1_sb9i a_sup_set_class a_wceq f2_sb9i a_wal f0_sb9i f2_sb9i f1_sb9i a_wsb f1_sb9i a_wal f0_sb9i f1_sb9i f2_sb9i a_wsb f2_sb9i a_wal a_wi p_pm2.61i $.
$}

$(Commutation of quantification and substitution variables.  (Contributed by
     NM, 5-Aug-1993.) $)

${
	$v ph x y  $.
	f0_sb9 $f wff ph $.
	f1_sb9 $f set x $.
	f2_sb9 $f set y $.
	p_sb9 $p |- ( A. x [ x / y ] ph <-> A. y [ y / x ] ph ) $= f0_sb9 f1_sb9 f2_sb9 p_sb9i f0_sb9 f2_sb9 f1_sb9 p_sb9i f0_sb9 f2_sb9 f1_sb9 a_wsb f1_sb9 a_wal f0_sb9 f1_sb9 f2_sb9 a_wsb f2_sb9 a_wal p_impbii $.
$}

$(This is a version of ~ ax-11o when the variables are distinct.  Axiom
       (C8) of [Monk2] p. 105.  See theorem ~ ax11v2 for the rederivation of
       ~ ax-11o from this theorem.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph x y  $.
	$d x y  $.
	f0_ax11v $f wff ph $.
	f1_ax11v $f set x $.
	f2_ax11v $f set y $.
	p_ax11v $p |- ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) $= f0_ax11v f1_ax11v a_sup_set_class f2_ax11v a_sup_set_class a_wceq a_ax-1 f1_ax11v a_sup_set_class f2_ax11v a_sup_set_class a_wceq f0_ax11v a_wi f1_ax11v f2_ax11v p_ax16 f0_ax11v f1_ax11v a_sup_set_class f2_ax11v a_sup_set_class a_wceq f0_ax11v a_wi f1_ax11v a_sup_set_class f2_ax11v a_sup_set_class a_wceq f1_ax11v a_wal f1_ax11v a_sup_set_class f2_ax11v a_sup_set_class a_wceq f0_ax11v a_wi f1_ax11v a_wal p_syl5 f1_ax11v a_sup_set_class f2_ax11v a_sup_set_class a_wceq f1_ax11v a_wal f0_ax11v f1_ax11v a_sup_set_class f2_ax11v a_sup_set_class a_wceq f0_ax11v a_wi f1_ax11v a_wal a_wi f1_ax11v a_sup_set_class f2_ax11v a_sup_set_class a_wceq p_a1d f0_ax11v f1_ax11v f2_ax11v p_ax11o f1_ax11v a_sup_set_class f2_ax11v a_sup_set_class a_wceq f1_ax11v a_wal f1_ax11v a_sup_set_class f2_ax11v a_sup_set_class a_wceq f0_ax11v f1_ax11v a_sup_set_class f2_ax11v a_sup_set_class a_wceq f0_ax11v a_wi f1_ax11v a_wal a_wi a_wi p_pm2.61i $.
$}

$(Two equivalent ways of expressing the proper substitution of ` y ` for
       ` x ` in ` ph ` , when ` x ` and ` y ` are distinct.  Theorem 6.2 of
       [Quine] p. 40.  The proof does not involve ~ df-sb .  (Contributed by
       NM, 14-Apr-2008.) $)

${
	$v ph x y  $.
	$d x y  $.
	f0_sb56 $f wff ph $.
	f1_sb56 $f set x $.
	f2_sb56 $f set y $.
	p_sb56 $p |- ( E. x ( x = y /\ ph ) <-> A. x ( x = y -> ph ) ) $= f1_sb56 a_sup_set_class f2_sb56 a_sup_set_class a_wceq f0_sb56 a_wi f1_sb56 p_nfa1 f0_sb56 f1_sb56 f2_sb56 p_ax11v f1_sb56 a_sup_set_class f2_sb56 a_sup_set_class a_wceq f0_sb56 a_wi f1_sb56 p_sp f1_sb56 a_sup_set_class f2_sb56 a_sup_set_class a_wceq f0_sb56 a_wi f1_sb56 a_wal f1_sb56 a_sup_set_class f2_sb56 a_sup_set_class a_wceq f0_sb56 p_com12 f1_sb56 a_sup_set_class f2_sb56 a_sup_set_class a_wceq f0_sb56 f1_sb56 a_sup_set_class f2_sb56 a_sup_set_class a_wceq f0_sb56 a_wi f1_sb56 a_wal p_impbid f0_sb56 f1_sb56 a_sup_set_class f2_sb56 a_sup_set_class a_wceq f0_sb56 a_wi f1_sb56 a_wal f1_sb56 f2_sb56 p_equsex $.
$}

$(Equivalence for substitution.  Compare Theorem 6.2 of [Quine] p. 40.
       Also proved as Lemmas 16 and 17 of [Tarski] p. 70.  (Contributed by NM,
       18-Aug-1993.) $)

${
	$v ph x y  $.
	$d x y  $.
	f0_sb6 $f wff ph $.
	f1_sb6 $f set x $.
	f2_sb6 $f set y $.
	p_sb6 $p |- ( [ y / x ] ph <-> A. x ( x = y -> ph ) ) $= f0_sb6 f1_sb6 f2_sb6 p_sb56 f1_sb6 a_sup_set_class f2_sb6 a_sup_set_class a_wceq f0_sb6 a_wa f1_sb6 a_wex f1_sb6 a_sup_set_class f2_sb6 a_sup_set_class a_wceq f0_sb6 a_wi f1_sb6 a_wal f1_sb6 a_sup_set_class f2_sb6 a_sup_set_class a_wceq f0_sb6 a_wi p_anbi2i f0_sb6 f1_sb6 f2_sb6 a_df-sb f1_sb6 a_sup_set_class f2_sb6 a_sup_set_class a_wceq f0_sb6 a_wi f1_sb6 p_sp f1_sb6 a_sup_set_class f2_sb6 a_sup_set_class a_wceq f0_sb6 a_wi f1_sb6 a_wal f1_sb6 a_sup_set_class f2_sb6 a_sup_set_class a_wceq f0_sb6 a_wi p_pm4.71ri f1_sb6 a_sup_set_class f2_sb6 a_sup_set_class a_wceq f0_sb6 a_wi f1_sb6 a_sup_set_class f2_sb6 a_sup_set_class a_wceq f0_sb6 a_wa f1_sb6 a_wex a_wa f1_sb6 a_sup_set_class f2_sb6 a_sup_set_class a_wceq f0_sb6 a_wi f1_sb6 a_sup_set_class f2_sb6 a_sup_set_class a_wceq f0_sb6 a_wi f1_sb6 a_wal a_wa f0_sb6 f1_sb6 f2_sb6 a_wsb f1_sb6 a_sup_set_class f2_sb6 a_sup_set_class a_wceq f0_sb6 a_wi f1_sb6 a_wal p_3bitr4i $.
$}

$(Equivalence for substitution.  Similar to Theorem 6.1 of [Quine] p. 40.
       (Contributed by NM, 18-Aug-1993.) $)

${
	$v ph x y  $.
	$d x y  $.
	f0_sb5 $f wff ph $.
	f1_sb5 $f set x $.
	f2_sb5 $f set y $.
	p_sb5 $p |- ( [ y / x ] ph <-> E. x ( x = y /\ ph ) ) $= f0_sb5 f1_sb5 f2_sb5 p_sb6 f0_sb5 f1_sb5 f2_sb5 p_sb56 f0_sb5 f1_sb5 f2_sb5 a_wsb f1_sb5 a_sup_set_class f2_sb5 a_sup_set_class a_wceq f0_sb5 a_wi f1_sb5 a_wal f1_sb5 a_sup_set_class f2_sb5 a_sup_set_class a_wceq f0_sb5 a_wa f1_sb5 a_wex p_bitr4i $.
$}

$(Lemma for ~ equsb3 .  (Contributed by Raph Levien and FL, 4-Dec-2005.)
       (Proof shortened by Andrew Salmon, 14-Jun-2011.) $)

${
	$v x y z  $.
	$d y z  $.
	$d x y  $.
	f0_equsb3lem $f set x $.
	f1_equsb3lem $f set y $.
	f2_equsb3lem $f set z $.
	p_equsb3lem $p |- ( [ x / y ] y = z <-> x = z ) $= f0_equsb3lem a_sup_set_class f2_equsb3lem a_sup_set_class a_wceq f1_equsb3lem p_nfv f1_equsb3lem f0_equsb3lem f2_equsb3lem p_equequ1 f1_equsb3lem a_sup_set_class f2_equsb3lem a_sup_set_class a_wceq f0_equsb3lem a_sup_set_class f2_equsb3lem a_sup_set_class a_wceq f1_equsb3lem f0_equsb3lem p_sbie $.
$}

$(Substitution applied to an atomic wff.  (Contributed by Raph Levien and
       FL, 4-Dec-2005.) $)

${
	$v x y z  $.
	$d w y z  $.
	$d w x  $.
	f0_equsb3 $f set x $.
	f1_equsb3 $f set y $.
	f2_equsb3 $f set z $.
	i0_equsb3 $f set w $.
	p_equsb3 $p |- ( [ x / y ] y = z <-> x = z ) $= i0_equsb3 f1_equsb3 f2_equsb3 p_equsb3lem f1_equsb3 a_sup_set_class f2_equsb3 a_sup_set_class a_wceq f1_equsb3 i0_equsb3 a_wsb i0_equsb3 a_sup_set_class f2_equsb3 a_sup_set_class a_wceq i0_equsb3 f0_equsb3 p_sbbii f1_equsb3 a_sup_set_class f2_equsb3 a_sup_set_class a_wceq i0_equsb3 p_nfv f1_equsb3 a_sup_set_class f2_equsb3 a_sup_set_class a_wceq f1_equsb3 f0_equsb3 i0_equsb3 p_sbco2 f0_equsb3 i0_equsb3 f2_equsb3 p_equsb3lem f1_equsb3 a_sup_set_class f2_equsb3 a_sup_set_class a_wceq f1_equsb3 i0_equsb3 a_wsb i0_equsb3 f0_equsb3 a_wsb i0_equsb3 a_sup_set_class f2_equsb3 a_sup_set_class a_wceq i0_equsb3 f0_equsb3 a_wsb f1_equsb3 a_sup_set_class f2_equsb3 a_sup_set_class a_wceq f1_equsb3 f0_equsb3 a_wsb f0_equsb3 a_sup_set_class f2_equsb3 a_sup_set_class a_wceq p_3bitr3i $.
$}

$(Substitution applied to an atomic membership wff.  (Contributed by NM,
       7-Nov-2006.)  (Proof shortened by Andrew Salmon, 14-Jun-2011.) $)

${
	$v x y z  $.
	$d w y z  $.
	$d w x  $.
	f0_elsb3 $f set x $.
	f1_elsb3 $f set y $.
	f2_elsb3 $f set z $.
	i0_elsb3 $f set w $.
	p_elsb3 $p |- ( [ x / y ] y e. z <-> x e. z ) $= i0_elsb3 a_sup_set_class f2_elsb3 a_sup_set_class a_wcel f1_elsb3 p_nfv i0_elsb3 a_sup_set_class f2_elsb3 a_sup_set_class a_wcel i0_elsb3 f0_elsb3 f1_elsb3 p_sbco2 f1_elsb3 a_sup_set_class f2_elsb3 a_sup_set_class a_wcel i0_elsb3 p_nfv i0_elsb3 f1_elsb3 f2_elsb3 p_elequ1 i0_elsb3 a_sup_set_class f2_elsb3 a_sup_set_class a_wcel f1_elsb3 a_sup_set_class f2_elsb3 a_sup_set_class a_wcel i0_elsb3 f1_elsb3 p_sbie i0_elsb3 a_sup_set_class f2_elsb3 a_sup_set_class a_wcel i0_elsb3 f1_elsb3 a_wsb f1_elsb3 a_sup_set_class f2_elsb3 a_sup_set_class a_wcel f1_elsb3 f0_elsb3 p_sbbii f0_elsb3 a_sup_set_class f2_elsb3 a_sup_set_class a_wcel i0_elsb3 p_nfv i0_elsb3 f0_elsb3 f2_elsb3 p_elequ1 i0_elsb3 a_sup_set_class f2_elsb3 a_sup_set_class a_wcel f0_elsb3 a_sup_set_class f2_elsb3 a_sup_set_class a_wcel i0_elsb3 f0_elsb3 p_sbie i0_elsb3 a_sup_set_class f2_elsb3 a_sup_set_class a_wcel i0_elsb3 f1_elsb3 a_wsb f1_elsb3 f0_elsb3 a_wsb i0_elsb3 a_sup_set_class f2_elsb3 a_sup_set_class a_wcel i0_elsb3 f0_elsb3 a_wsb f1_elsb3 a_sup_set_class f2_elsb3 a_sup_set_class a_wcel f1_elsb3 f0_elsb3 a_wsb f0_elsb3 a_sup_set_class f2_elsb3 a_sup_set_class a_wcel p_3bitr3i $.
$}

$(Substitution applied to an atomic membership wff.  (Contributed by
       Rodolfo Medina, 3-Apr-2010.)  (Proof shortened by Andrew Salmon,
       14-Jun-2011.) $)

${
	$v x y z  $.
	$d w y z  $.
	$d w x  $.
	f0_elsb4 $f set x $.
	f1_elsb4 $f set y $.
	f2_elsb4 $f set z $.
	i0_elsb4 $f set w $.
	p_elsb4 $p |- ( [ x / y ] z e. y <-> z e. x ) $= f2_elsb4 a_sup_set_class i0_elsb4 a_sup_set_class a_wcel f1_elsb4 p_nfv f2_elsb4 a_sup_set_class i0_elsb4 a_sup_set_class a_wcel i0_elsb4 f0_elsb4 f1_elsb4 p_sbco2 f2_elsb4 a_sup_set_class f1_elsb4 a_sup_set_class a_wcel i0_elsb4 p_nfv i0_elsb4 f1_elsb4 f2_elsb4 p_elequ2 f2_elsb4 a_sup_set_class i0_elsb4 a_sup_set_class a_wcel f2_elsb4 a_sup_set_class f1_elsb4 a_sup_set_class a_wcel i0_elsb4 f1_elsb4 p_sbie f2_elsb4 a_sup_set_class i0_elsb4 a_sup_set_class a_wcel i0_elsb4 f1_elsb4 a_wsb f2_elsb4 a_sup_set_class f1_elsb4 a_sup_set_class a_wcel f1_elsb4 f0_elsb4 p_sbbii f2_elsb4 a_sup_set_class f0_elsb4 a_sup_set_class a_wcel i0_elsb4 p_nfv i0_elsb4 f0_elsb4 f2_elsb4 p_elequ2 f2_elsb4 a_sup_set_class i0_elsb4 a_sup_set_class a_wcel f2_elsb4 a_sup_set_class f0_elsb4 a_sup_set_class a_wcel i0_elsb4 f0_elsb4 p_sbie f2_elsb4 a_sup_set_class i0_elsb4 a_sup_set_class a_wcel i0_elsb4 f1_elsb4 a_wsb f1_elsb4 f0_elsb4 a_wsb f2_elsb4 a_sup_set_class i0_elsb4 a_sup_set_class a_wcel i0_elsb4 f0_elsb4 a_wsb f2_elsb4 a_sup_set_class f1_elsb4 a_sup_set_class a_wcel f1_elsb4 f0_elsb4 a_wsb f2_elsb4 a_sup_set_class f0_elsb4 a_sup_set_class a_wcel p_3bitr3i $.
$}

$(` x ` is not free in ` [ y / x ] ph ` when ` x ` and ` y ` are
       distinct.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph x y  $.
	$d x y  $.
	f0_hbs1 $f wff ph $.
	f1_hbs1 $f set x $.
	f2_hbs1 $f set y $.
	p_hbs1 $p |- ( [ y / x ] ph -> A. x [ y / x ] ph ) $= f0_hbs1 f1_hbs1 f2_hbs1 a_wsb f1_hbs1 f2_hbs1 p_ax16 f0_hbs1 f1_hbs1 f2_hbs1 p_hbsb2 f1_hbs1 a_sup_set_class f2_hbs1 a_sup_set_class a_wceq f1_hbs1 a_wal f0_hbs1 f1_hbs1 f2_hbs1 a_wsb f0_hbs1 f1_hbs1 f2_hbs1 a_wsb f1_hbs1 a_wal a_wi p_pm2.61i $.
$}

$(` x ` is not free in ` [ y / x ] ph ` when ` x ` and ` y ` are
       distinct.  (Contributed by Mario Carneiro, 11-Aug-2016.) $)

${
	$v ph x y  $.
	$d x y  $.
	f0_nfs1v $f wff ph $.
	f1_nfs1v $f set x $.
	f2_nfs1v $f set y $.
	p_nfs1v $p |- F/ x [ y / x ] ph $= f0_nfs1v f1_nfs1v f2_nfs1v p_hbs1 f0_nfs1v f1_nfs1v f2_nfs1v a_wsb f1_nfs1v p_nfi $.
$}

$(Two ways of expressing " ` x ` is (effectively) not free in ` ph ` ."
       (Contributed by NM, 29-May-2009.) $)

${
	$v ph x y  $.
	$d y ph  $.
	f0_sbhb $f wff ph $.
	f1_sbhb $f set x $.
	f2_sbhb $f set y $.
	p_sbhb $p |- ( ( ph -> A. x ph ) <-> A. y ( ph -> [ y / x ] ph ) ) $= f0_sbhb f2_sbhb p_nfv f0_sbhb f1_sbhb f2_sbhb p_sb8 f0_sbhb f1_sbhb a_wal f0_sbhb f1_sbhb f2_sbhb a_wsb f2_sbhb a_wal f0_sbhb p_imbi2i f0_sbhb f0_sbhb f1_sbhb f2_sbhb a_wsb f2_sbhb p_19.21v f0_sbhb f0_sbhb f1_sbhb a_wal a_wi f0_sbhb f0_sbhb f1_sbhb f2_sbhb a_wsb f2_sbhb a_wal a_wi f0_sbhb f0_sbhb f1_sbhb f2_sbhb a_wsb a_wi f2_sbhb a_wal p_bitr4i $.
$}

$(Two ways of expressing " ` x ` is (effectively) not free in ` ph ` ."
       (Contributed by G&eacute;rard Lang, 14-Nov-2013.)  (Revised by Mario
       Carneiro, 6-Oct-2016.) $)

${
	$v ph x y z  $.
	$d x y z  $.
	$d y z ph  $.
	f0_sbnf2 $f wff ph $.
	f1_sbnf2 $f set x $.
	f2_sbnf2 $f set y $.
	f3_sbnf2 $f set z $.
	p_sbnf2 $p |- ( F/ x ph <-> A. y A. z ( [ y / x ] ph <-> [ z / x ] ph ) ) $= f0_sbnf2 f1_sbnf2 f2_sbnf2 a_wsb f0_sbnf2 f1_sbnf2 f3_sbnf2 a_wsb f2_sbnf2 f3_sbnf2 p_2albiim f0_sbnf2 f1_sbnf2 a_df-nf f0_sbnf2 f1_sbnf2 f3_sbnf2 p_sbhb f0_sbnf2 f0_sbnf2 f1_sbnf2 a_wal a_wi f0_sbnf2 f0_sbnf2 f1_sbnf2 f3_sbnf2 a_wsb a_wi f3_sbnf2 a_wal f1_sbnf2 p_albii f0_sbnf2 f0_sbnf2 f1_sbnf2 f3_sbnf2 a_wsb a_wi f1_sbnf2 f3_sbnf2 p_alcom f0_sbnf2 f1_sbnf2 a_wnf f0_sbnf2 f0_sbnf2 f1_sbnf2 a_wal a_wi f1_sbnf2 a_wal f0_sbnf2 f0_sbnf2 f1_sbnf2 f3_sbnf2 a_wsb a_wi f3_sbnf2 a_wal f1_sbnf2 a_wal f0_sbnf2 f0_sbnf2 f1_sbnf2 f3_sbnf2 a_wsb a_wi f1_sbnf2 a_wal f3_sbnf2 a_wal p_3bitri f0_sbnf2 f0_sbnf2 f1_sbnf2 f3_sbnf2 a_wsb a_wi f2_sbnf2 p_nfv f0_sbnf2 f0_sbnf2 f1_sbnf2 f3_sbnf2 a_wsb a_wi f1_sbnf2 f2_sbnf2 p_sb8 f0_sbnf2 f1_sbnf2 f3_sbnf2 p_nfs1v f0_sbnf2 f0_sbnf2 f1_sbnf2 f3_sbnf2 a_wsb f1_sbnf2 f2_sbnf2 p_sblim f0_sbnf2 f0_sbnf2 f1_sbnf2 f3_sbnf2 a_wsb a_wi f1_sbnf2 f2_sbnf2 a_wsb f0_sbnf2 f1_sbnf2 f2_sbnf2 a_wsb f0_sbnf2 f1_sbnf2 f3_sbnf2 a_wsb a_wi f2_sbnf2 p_albii f0_sbnf2 f0_sbnf2 f1_sbnf2 f3_sbnf2 a_wsb a_wi f1_sbnf2 a_wal f0_sbnf2 f0_sbnf2 f1_sbnf2 f3_sbnf2 a_wsb a_wi f1_sbnf2 f2_sbnf2 a_wsb f2_sbnf2 a_wal f0_sbnf2 f1_sbnf2 f2_sbnf2 a_wsb f0_sbnf2 f1_sbnf2 f3_sbnf2 a_wsb a_wi f2_sbnf2 a_wal p_bitri f0_sbnf2 f0_sbnf2 f1_sbnf2 f3_sbnf2 a_wsb a_wi f1_sbnf2 a_wal f0_sbnf2 f1_sbnf2 f2_sbnf2 a_wsb f0_sbnf2 f1_sbnf2 f3_sbnf2 a_wsb a_wi f2_sbnf2 a_wal f3_sbnf2 p_albii f0_sbnf2 f1_sbnf2 f2_sbnf2 a_wsb f0_sbnf2 f1_sbnf2 f3_sbnf2 a_wsb a_wi f3_sbnf2 f2_sbnf2 p_alcom f0_sbnf2 f1_sbnf2 a_wnf f0_sbnf2 f0_sbnf2 f1_sbnf2 f3_sbnf2 a_wsb a_wi f1_sbnf2 a_wal f3_sbnf2 a_wal f0_sbnf2 f1_sbnf2 f2_sbnf2 a_wsb f0_sbnf2 f1_sbnf2 f3_sbnf2 a_wsb a_wi f2_sbnf2 a_wal f3_sbnf2 a_wal f0_sbnf2 f1_sbnf2 f2_sbnf2 a_wsb f0_sbnf2 f1_sbnf2 f3_sbnf2 a_wsb a_wi f3_sbnf2 a_wal f2_sbnf2 a_wal p_3bitri f0_sbnf2 f1_sbnf2 a_df-nf f0_sbnf2 f1_sbnf2 f2_sbnf2 p_sbhb f0_sbnf2 f0_sbnf2 f1_sbnf2 a_wal a_wi f0_sbnf2 f0_sbnf2 f1_sbnf2 f2_sbnf2 a_wsb a_wi f2_sbnf2 a_wal f1_sbnf2 p_albii f0_sbnf2 f0_sbnf2 f1_sbnf2 f2_sbnf2 a_wsb a_wi f1_sbnf2 f2_sbnf2 p_alcom f0_sbnf2 f1_sbnf2 a_wnf f0_sbnf2 f0_sbnf2 f1_sbnf2 a_wal a_wi f1_sbnf2 a_wal f0_sbnf2 f0_sbnf2 f1_sbnf2 f2_sbnf2 a_wsb a_wi f2_sbnf2 a_wal f1_sbnf2 a_wal f0_sbnf2 f0_sbnf2 f1_sbnf2 f2_sbnf2 a_wsb a_wi f1_sbnf2 a_wal f2_sbnf2 a_wal p_3bitri f0_sbnf2 f0_sbnf2 f1_sbnf2 f2_sbnf2 a_wsb a_wi f3_sbnf2 p_nfv f0_sbnf2 f0_sbnf2 f1_sbnf2 f2_sbnf2 a_wsb a_wi f1_sbnf2 f3_sbnf2 p_sb8 f0_sbnf2 f1_sbnf2 f2_sbnf2 p_nfs1v f0_sbnf2 f0_sbnf2 f1_sbnf2 f2_sbnf2 a_wsb f1_sbnf2 f3_sbnf2 p_sblim f0_sbnf2 f0_sbnf2 f1_sbnf2 f2_sbnf2 a_wsb a_wi f1_sbnf2 f3_sbnf2 a_wsb f0_sbnf2 f1_sbnf2 f3_sbnf2 a_wsb f0_sbnf2 f1_sbnf2 f2_sbnf2 a_wsb a_wi f3_sbnf2 p_albii f0_sbnf2 f0_sbnf2 f1_sbnf2 f2_sbnf2 a_wsb a_wi f1_sbnf2 a_wal f0_sbnf2 f0_sbnf2 f1_sbnf2 f2_sbnf2 a_wsb a_wi f1_sbnf2 f3_sbnf2 a_wsb f3_sbnf2 a_wal f0_sbnf2 f1_sbnf2 f3_sbnf2 a_wsb f0_sbnf2 f1_sbnf2 f2_sbnf2 a_wsb a_wi f3_sbnf2 a_wal p_bitri f0_sbnf2 f0_sbnf2 f1_sbnf2 f2_sbnf2 a_wsb a_wi f1_sbnf2 a_wal f0_sbnf2 f1_sbnf2 f3_sbnf2 a_wsb f0_sbnf2 f1_sbnf2 f2_sbnf2 a_wsb a_wi f3_sbnf2 a_wal f2_sbnf2 p_albii f0_sbnf2 f1_sbnf2 a_wnf f0_sbnf2 f0_sbnf2 f1_sbnf2 f2_sbnf2 a_wsb a_wi f1_sbnf2 a_wal f2_sbnf2 a_wal f0_sbnf2 f1_sbnf2 f3_sbnf2 a_wsb f0_sbnf2 f1_sbnf2 f2_sbnf2 a_wsb a_wi f3_sbnf2 a_wal f2_sbnf2 a_wal p_bitri f0_sbnf2 f1_sbnf2 a_wnf f0_sbnf2 f1_sbnf2 f2_sbnf2 a_wsb f0_sbnf2 f1_sbnf2 f3_sbnf2 a_wsb a_wi f3_sbnf2 a_wal f2_sbnf2 a_wal f0_sbnf2 f1_sbnf2 a_wnf f0_sbnf2 f1_sbnf2 f3_sbnf2 a_wsb f0_sbnf2 f1_sbnf2 f2_sbnf2 a_wsb a_wi f3_sbnf2 a_wal f2_sbnf2 a_wal p_anbi12i f0_sbnf2 f1_sbnf2 a_wnf p_anidm f0_sbnf2 f1_sbnf2 f2_sbnf2 a_wsb f0_sbnf2 f1_sbnf2 f3_sbnf2 a_wsb a_wb f3_sbnf2 a_wal f2_sbnf2 a_wal f0_sbnf2 f1_sbnf2 f2_sbnf2 a_wsb f0_sbnf2 f1_sbnf2 f3_sbnf2 a_wsb a_wi f3_sbnf2 a_wal f2_sbnf2 a_wal f0_sbnf2 f1_sbnf2 f3_sbnf2 a_wsb f0_sbnf2 f1_sbnf2 f2_sbnf2 a_wsb a_wi f3_sbnf2 a_wal f2_sbnf2 a_wal a_wa f0_sbnf2 f1_sbnf2 a_wnf f0_sbnf2 f1_sbnf2 a_wnf a_wa f0_sbnf2 f1_sbnf2 a_wnf p_3bitr2ri $.
$}

$(If ` z ` is not free in ` ph ` , it is not free in ` [ y / x ] ph ` when
       ` y ` and ` z ` are distinct.  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)

${
	$v ph x y z  $.
	$d y z  $.
	f0_nfsb $f wff ph $.
	f1_nfsb $f set x $.
	f2_nfsb $f set y $.
	f3_nfsb $f set z $.
	e0_nfsb $e |- F/ z ph $.
	p_nfsb $p |- F/ z [ y / x ] ph $= f0_nfsb f1_nfsb f2_nfsb a_wsb f3_nfsb f2_nfsb f3_nfsb p_a16nf e0_nfsb f0_nfsb f1_nfsb f2_nfsb f3_nfsb p_nfsb4 f3_nfsb a_sup_set_class f2_nfsb a_sup_set_class a_wceq f3_nfsb a_wal f0_nfsb f1_nfsb f2_nfsb a_wsb f3_nfsb a_wnf p_pm2.61i $.
$}

$(If ` z ` is not free in ` ph ` , it is not free in ` [ y / x ] ph ` when
       ` y ` and ` z ` are distinct.  (Contributed by NM, 12-Aug-1993.) $)

${
	$v ph x y z  $.
	$d y z  $.
	f0_hbsb $f wff ph $.
	f1_hbsb $f set x $.
	f2_hbsb $f set y $.
	f3_hbsb $f set z $.
	e0_hbsb $e |- ( ph -> A. z ph ) $.
	p_hbsb $p |- ( [ y / x ] ph -> A. z [ y / x ] ph ) $= e0_hbsb f0_hbsb f3_hbsb p_nfi f0_hbsb f1_hbsb f2_hbsb f3_hbsb p_nfsb f0_hbsb f1_hbsb f2_hbsb a_wsb f3_hbsb p_nfri $.
$}

$(Deduction version of ~ nfsb .  (Contributed by NM, 15-Feb-2013.) $)

${
	$v ph ps x y z  $.
	$d y z  $.
	f0_nfsbd $f wff ph $.
	f1_nfsbd $f wff ps $.
	f2_nfsbd $f set x $.
	f3_nfsbd $f set y $.
	f4_nfsbd $f set z $.
	e0_nfsbd $e |- F/ x ph $.
	e1_nfsbd $e |- ( ph -> F/ z ps ) $.
	p_nfsbd $p |- ( ph -> F/ z [ y / x ] ps ) $= e0_nfsbd e1_nfsbd f0_nfsbd f1_nfsbd f4_nfsbd a_wnf f2_nfsbd p_alrimi f1_nfsbd f2_nfsbd f3_nfsbd f4_nfsbd p_nfsb4t f0_nfsbd f1_nfsbd f4_nfsbd a_wnf f2_nfsbd a_wal f4_nfsbd a_sup_set_class f3_nfsbd a_sup_set_class a_wceq f4_nfsbd a_wal a_wn f1_nfsbd f2_nfsbd f3_nfsbd a_wsb f4_nfsbd a_wnf a_wi p_syl f1_nfsbd f2_nfsbd f3_nfsbd a_wsb f4_nfsbd f3_nfsbd f4_nfsbd p_a16nf f0_nfsbd f4_nfsbd a_sup_set_class f3_nfsbd a_sup_set_class a_wceq f4_nfsbd a_wal f1_nfsbd f2_nfsbd f3_nfsbd a_wsb f4_nfsbd a_wnf p_pm2.61d2 $.
$}

$(Equivalence for double substitution.  (Contributed by NM,
       3-Feb-2005.) $)

${
	$v ph x y z w  $.
	$d x y z  $.
	$d w y  $.
	f0_2sb5 $f wff ph $.
	f1_2sb5 $f set x $.
	f2_2sb5 $f set y $.
	f3_2sb5 $f set z $.
	f4_2sb5 $f set w $.
	p_2sb5 $p |- ( [ z / x ] [ w / y ] ph <-> E. x E. y ( ( x = z /\ y = w ) /\ ph ) ) $= f0_2sb5 f2_2sb5 f4_2sb5 a_wsb f1_2sb5 f3_2sb5 p_sb5 f1_2sb5 a_sup_set_class f3_2sb5 a_sup_set_class a_wceq f2_2sb5 a_sup_set_class f4_2sb5 a_sup_set_class a_wceq f0_2sb5 a_wa f2_2sb5 p_19.42v f1_2sb5 a_sup_set_class f3_2sb5 a_sup_set_class a_wceq f2_2sb5 a_sup_set_class f4_2sb5 a_sup_set_class a_wceq f0_2sb5 p_anass f1_2sb5 a_sup_set_class f3_2sb5 a_sup_set_class a_wceq f2_2sb5 a_sup_set_class f4_2sb5 a_sup_set_class a_wceq a_wa f0_2sb5 a_wa f1_2sb5 a_sup_set_class f3_2sb5 a_sup_set_class a_wceq f2_2sb5 a_sup_set_class f4_2sb5 a_sup_set_class a_wceq f0_2sb5 a_wa a_wa f2_2sb5 p_exbii f0_2sb5 f2_2sb5 f4_2sb5 p_sb5 f0_2sb5 f2_2sb5 f4_2sb5 a_wsb f2_2sb5 a_sup_set_class f4_2sb5 a_sup_set_class a_wceq f0_2sb5 a_wa f2_2sb5 a_wex f1_2sb5 a_sup_set_class f3_2sb5 a_sup_set_class a_wceq p_anbi2i f1_2sb5 a_sup_set_class f3_2sb5 a_sup_set_class a_wceq f2_2sb5 a_sup_set_class f4_2sb5 a_sup_set_class a_wceq f0_2sb5 a_wa a_wa f2_2sb5 a_wex f1_2sb5 a_sup_set_class f3_2sb5 a_sup_set_class a_wceq f2_2sb5 a_sup_set_class f4_2sb5 a_sup_set_class a_wceq f0_2sb5 a_wa f2_2sb5 a_wex a_wa f1_2sb5 a_sup_set_class f3_2sb5 a_sup_set_class a_wceq f2_2sb5 a_sup_set_class f4_2sb5 a_sup_set_class a_wceq a_wa f0_2sb5 a_wa f2_2sb5 a_wex f1_2sb5 a_sup_set_class f3_2sb5 a_sup_set_class a_wceq f0_2sb5 f2_2sb5 f4_2sb5 a_wsb a_wa p_3bitr4ri f1_2sb5 a_sup_set_class f3_2sb5 a_sup_set_class a_wceq f0_2sb5 f2_2sb5 f4_2sb5 a_wsb a_wa f1_2sb5 a_sup_set_class f3_2sb5 a_sup_set_class a_wceq f2_2sb5 a_sup_set_class f4_2sb5 a_sup_set_class a_wceq a_wa f0_2sb5 a_wa f2_2sb5 a_wex f1_2sb5 p_exbii f0_2sb5 f2_2sb5 f4_2sb5 a_wsb f1_2sb5 f3_2sb5 a_wsb f1_2sb5 a_sup_set_class f3_2sb5 a_sup_set_class a_wceq f0_2sb5 f2_2sb5 f4_2sb5 a_wsb a_wa f1_2sb5 a_wex f1_2sb5 a_sup_set_class f3_2sb5 a_sup_set_class a_wceq f2_2sb5 a_sup_set_class f4_2sb5 a_sup_set_class a_wceq a_wa f0_2sb5 a_wa f2_2sb5 a_wex f1_2sb5 a_wex p_bitri $.
$}

$(Equivalence for double substitution.  (Contributed by NM,
       3-Feb-2005.) $)

${
	$v ph x y z w  $.
	$d x y z  $.
	$d w y  $.
	f0_2sb6 $f wff ph $.
	f1_2sb6 $f set x $.
	f2_2sb6 $f set y $.
	f3_2sb6 $f set z $.
	f4_2sb6 $f set w $.
	p_2sb6 $p |- ( [ z / x ] [ w / y ] ph <-> A. x A. y ( ( x = z /\ y = w ) -> ph ) ) $= f0_2sb6 f2_2sb6 f4_2sb6 a_wsb f1_2sb6 f3_2sb6 p_sb6 f1_2sb6 a_sup_set_class f3_2sb6 a_sup_set_class a_wceq f2_2sb6 a_sup_set_class f4_2sb6 a_sup_set_class a_wceq f0_2sb6 a_wi f2_2sb6 p_19.21v f1_2sb6 a_sup_set_class f3_2sb6 a_sup_set_class a_wceq f2_2sb6 a_sup_set_class f4_2sb6 a_sup_set_class a_wceq f0_2sb6 p_impexp f1_2sb6 a_sup_set_class f3_2sb6 a_sup_set_class a_wceq f2_2sb6 a_sup_set_class f4_2sb6 a_sup_set_class a_wceq a_wa f0_2sb6 a_wi f1_2sb6 a_sup_set_class f3_2sb6 a_sup_set_class a_wceq f2_2sb6 a_sup_set_class f4_2sb6 a_sup_set_class a_wceq f0_2sb6 a_wi a_wi f2_2sb6 p_albii f0_2sb6 f2_2sb6 f4_2sb6 p_sb6 f0_2sb6 f2_2sb6 f4_2sb6 a_wsb f2_2sb6 a_sup_set_class f4_2sb6 a_sup_set_class a_wceq f0_2sb6 a_wi f2_2sb6 a_wal f1_2sb6 a_sup_set_class f3_2sb6 a_sup_set_class a_wceq p_imbi2i f1_2sb6 a_sup_set_class f3_2sb6 a_sup_set_class a_wceq f2_2sb6 a_sup_set_class f4_2sb6 a_sup_set_class a_wceq f0_2sb6 a_wi a_wi f2_2sb6 a_wal f1_2sb6 a_sup_set_class f3_2sb6 a_sup_set_class a_wceq f2_2sb6 a_sup_set_class f4_2sb6 a_sup_set_class a_wceq f0_2sb6 a_wi f2_2sb6 a_wal a_wi f1_2sb6 a_sup_set_class f3_2sb6 a_sup_set_class a_wceq f2_2sb6 a_sup_set_class f4_2sb6 a_sup_set_class a_wceq a_wa f0_2sb6 a_wi f2_2sb6 a_wal f1_2sb6 a_sup_set_class f3_2sb6 a_sup_set_class a_wceq f0_2sb6 f2_2sb6 f4_2sb6 a_wsb a_wi p_3bitr4ri f1_2sb6 a_sup_set_class f3_2sb6 a_sup_set_class a_wceq f0_2sb6 f2_2sb6 f4_2sb6 a_wsb a_wi f1_2sb6 a_sup_set_class f3_2sb6 a_sup_set_class a_wceq f2_2sb6 a_sup_set_class f4_2sb6 a_sup_set_class a_wceq a_wa f0_2sb6 a_wi f2_2sb6 a_wal f1_2sb6 p_albii f0_2sb6 f2_2sb6 f4_2sb6 a_wsb f1_2sb6 f3_2sb6 a_wsb f1_2sb6 a_sup_set_class f3_2sb6 a_sup_set_class a_wceq f0_2sb6 f2_2sb6 f4_2sb6 a_wsb a_wi f1_2sb6 a_wal f1_2sb6 a_sup_set_class f3_2sb6 a_sup_set_class a_wceq f2_2sb6 a_sup_set_class f4_2sb6 a_sup_set_class a_wceq a_wa f0_2sb6 a_wi f2_2sb6 a_wal f1_2sb6 a_wal p_bitri $.
$}

$(Commutativity law for substitution.  Used in proof of Theorem 9.7 of
       [Megill] p. 449 (p. 16 of the preprint).  (Contributed by NM,
       27-May-1997.) $)

${
	$v ph x y z w  $.
	$d x z  $.
	$d x w  $.
	$d y z  $.
	f0_sbcom2 $f wff ph $.
	f1_sbcom2 $f set x $.
	f2_sbcom2 $f set y $.
	f3_sbcom2 $f set z $.
	f4_sbcom2 $f set w $.
	p_sbcom2 $p |- ( [ w / z ] [ y / x ] ph <-> [ y / x ] [ w / z ] ph ) $= f1_sbcom2 a_sup_set_class f2_sbcom2 a_sup_set_class a_wceq f3_sbcom2 a_sup_set_class f4_sbcom2 a_sup_set_class a_wceq f0_sbcom2 a_wi a_wi f3_sbcom2 f1_sbcom2 p_alcom f1_sbcom2 a_sup_set_class f2_sbcom2 a_sup_set_class a_wceq f3_sbcom2 a_sup_set_class f4_sbcom2 a_sup_set_class a_wceq f0_sbcom2 p_bi2.04 f1_sbcom2 a_sup_set_class f2_sbcom2 a_sup_set_class a_wceq f3_sbcom2 a_sup_set_class f4_sbcom2 a_sup_set_class a_wceq f0_sbcom2 a_wi a_wi f3_sbcom2 a_sup_set_class f4_sbcom2 a_sup_set_class a_wceq f1_sbcom2 a_sup_set_class f2_sbcom2 a_sup_set_class a_wceq f0_sbcom2 a_wi a_wi f1_sbcom2 p_albii f3_sbcom2 a_sup_set_class f4_sbcom2 a_sup_set_class a_wceq f1_sbcom2 a_sup_set_class f2_sbcom2 a_sup_set_class a_wceq f0_sbcom2 a_wi f1_sbcom2 p_19.21v f1_sbcom2 a_sup_set_class f2_sbcom2 a_sup_set_class a_wceq f3_sbcom2 a_sup_set_class f4_sbcom2 a_sup_set_class a_wceq f0_sbcom2 a_wi a_wi f1_sbcom2 a_wal f3_sbcom2 a_sup_set_class f4_sbcom2 a_sup_set_class a_wceq f1_sbcom2 a_sup_set_class f2_sbcom2 a_sup_set_class a_wceq f0_sbcom2 a_wi a_wi f1_sbcom2 a_wal f3_sbcom2 a_sup_set_class f4_sbcom2 a_sup_set_class a_wceq f1_sbcom2 a_sup_set_class f2_sbcom2 a_sup_set_class a_wceq f0_sbcom2 a_wi f1_sbcom2 a_wal a_wi p_bitri f1_sbcom2 a_sup_set_class f2_sbcom2 a_sup_set_class a_wceq f3_sbcom2 a_sup_set_class f4_sbcom2 a_sup_set_class a_wceq f0_sbcom2 a_wi a_wi f1_sbcom2 a_wal f3_sbcom2 a_sup_set_class f4_sbcom2 a_sup_set_class a_wceq f1_sbcom2 a_sup_set_class f2_sbcom2 a_sup_set_class a_wceq f0_sbcom2 a_wi f1_sbcom2 a_wal a_wi f3_sbcom2 p_albii f1_sbcom2 a_sup_set_class f2_sbcom2 a_sup_set_class a_wceq f3_sbcom2 a_sup_set_class f4_sbcom2 a_sup_set_class a_wceq f0_sbcom2 a_wi f3_sbcom2 p_19.21v f1_sbcom2 a_sup_set_class f2_sbcom2 a_sup_set_class a_wceq f3_sbcom2 a_sup_set_class f4_sbcom2 a_sup_set_class a_wceq f0_sbcom2 a_wi a_wi f3_sbcom2 a_wal f1_sbcom2 a_sup_set_class f2_sbcom2 a_sup_set_class a_wceq f3_sbcom2 a_sup_set_class f4_sbcom2 a_sup_set_class a_wceq f0_sbcom2 a_wi f3_sbcom2 a_wal a_wi f1_sbcom2 p_albii f1_sbcom2 a_sup_set_class f2_sbcom2 a_sup_set_class a_wceq f3_sbcom2 a_sup_set_class f4_sbcom2 a_sup_set_class a_wceq f0_sbcom2 a_wi a_wi f1_sbcom2 a_wal f3_sbcom2 a_wal f1_sbcom2 a_sup_set_class f2_sbcom2 a_sup_set_class a_wceq f3_sbcom2 a_sup_set_class f4_sbcom2 a_sup_set_class a_wceq f0_sbcom2 a_wi a_wi f3_sbcom2 a_wal f1_sbcom2 a_wal f3_sbcom2 a_sup_set_class f4_sbcom2 a_sup_set_class a_wceq f1_sbcom2 a_sup_set_class f2_sbcom2 a_sup_set_class a_wceq f0_sbcom2 a_wi f1_sbcom2 a_wal a_wi f3_sbcom2 a_wal f1_sbcom2 a_sup_set_class f2_sbcom2 a_sup_set_class a_wceq f3_sbcom2 a_sup_set_class f4_sbcom2 a_sup_set_class a_wceq f0_sbcom2 a_wi f3_sbcom2 a_wal a_wi f1_sbcom2 a_wal p_3bitr3i f3_sbcom2 a_sup_set_class f4_sbcom2 a_sup_set_class a_wceq f1_sbcom2 a_sup_set_class f2_sbcom2 a_sup_set_class a_wceq f0_sbcom2 a_wi f1_sbcom2 a_wal a_wi f3_sbcom2 a_wal f1_sbcom2 a_sup_set_class f2_sbcom2 a_sup_set_class a_wceq f3_sbcom2 a_sup_set_class f4_sbcom2 a_sup_set_class a_wceq f0_sbcom2 a_wi f3_sbcom2 a_wal a_wi f1_sbcom2 a_wal a_wb f1_sbcom2 a_sup_set_class f2_sbcom2 a_sup_set_class a_wceq f1_sbcom2 a_wal a_wn f3_sbcom2 a_sup_set_class f4_sbcom2 a_sup_set_class a_wceq f3_sbcom2 a_wal a_wn a_wa p_a1i f0_sbcom2 f1_sbcom2 f2_sbcom2 a_wsb f3_sbcom2 f4_sbcom2 p_sb4b f0_sbcom2 f1_sbcom2 f2_sbcom2 p_sb4b f1_sbcom2 a_sup_set_class f2_sbcom2 a_sup_set_class a_wceq f1_sbcom2 a_wal a_wn f0_sbcom2 f1_sbcom2 f2_sbcom2 a_wsb f1_sbcom2 a_sup_set_class f2_sbcom2 a_sup_set_class a_wceq f0_sbcom2 a_wi f1_sbcom2 a_wal f3_sbcom2 a_sup_set_class f4_sbcom2 a_sup_set_class a_wceq p_imbi2d f1_sbcom2 a_sup_set_class f2_sbcom2 a_sup_set_class a_wceq f1_sbcom2 a_wal a_wn f3_sbcom2 a_sup_set_class f4_sbcom2 a_sup_set_class a_wceq f0_sbcom2 f1_sbcom2 f2_sbcom2 a_wsb a_wi f3_sbcom2 a_sup_set_class f4_sbcom2 a_sup_set_class a_wceq f1_sbcom2 a_sup_set_class f2_sbcom2 a_sup_set_class a_wceq f0_sbcom2 a_wi f1_sbcom2 a_wal a_wi f3_sbcom2 p_albidv f3_sbcom2 a_sup_set_class f4_sbcom2 a_sup_set_class a_wceq f3_sbcom2 a_wal a_wn f0_sbcom2 f1_sbcom2 f2_sbcom2 a_wsb f3_sbcom2 f4_sbcom2 a_wsb f3_sbcom2 a_sup_set_class f4_sbcom2 a_sup_set_class a_wceq f0_sbcom2 f1_sbcom2 f2_sbcom2 a_wsb a_wi f3_sbcom2 a_wal f1_sbcom2 a_sup_set_class f2_sbcom2 a_sup_set_class a_wceq f1_sbcom2 a_wal a_wn f3_sbcom2 a_sup_set_class f4_sbcom2 a_sup_set_class a_wceq f1_sbcom2 a_sup_set_class f2_sbcom2 a_sup_set_class a_wceq f0_sbcom2 a_wi f1_sbcom2 a_wal a_wi f3_sbcom2 a_wal p_sylan9bbr f0_sbcom2 f3_sbcom2 f4_sbcom2 a_wsb f1_sbcom2 f2_sbcom2 p_sb4b f0_sbcom2 f3_sbcom2 f4_sbcom2 p_sb4b f3_sbcom2 a_sup_set_class f4_sbcom2 a_sup_set_class a_wceq f3_sbcom2 a_wal a_wn f0_sbcom2 f3_sbcom2 f4_sbcom2 a_wsb f3_sbcom2 a_sup_set_class f4_sbcom2 a_sup_set_class a_wceq f0_sbcom2 a_wi f3_sbcom2 a_wal f1_sbcom2 a_sup_set_class f2_sbcom2 a_sup_set_class a_wceq p_imbi2d f3_sbcom2 a_sup_set_class f4_sbcom2 a_sup_set_class a_wceq f3_sbcom2 a_wal a_wn f1_sbcom2 a_sup_set_class f2_sbcom2 a_sup_set_class a_wceq f0_sbcom2 f3_sbcom2 f4_sbcom2 a_wsb a_wi f1_sbcom2 a_sup_set_class f2_sbcom2 a_sup_set_class a_wceq f3_sbcom2 a_sup_set_class f4_sbcom2 a_sup_set_class a_wceq f0_sbcom2 a_wi f3_sbcom2 a_wal a_wi f1_sbcom2 p_albidv f1_sbcom2 a_sup_set_class f2_sbcom2 a_sup_set_class a_wceq f1_sbcom2 a_wal a_wn f0_sbcom2 f3_sbcom2 f4_sbcom2 a_wsb f1_sbcom2 f2_sbcom2 a_wsb f1_sbcom2 a_sup_set_class f2_sbcom2 a_sup_set_class a_wceq f0_sbcom2 f3_sbcom2 f4_sbcom2 a_wsb a_wi f1_sbcom2 a_wal f3_sbcom2 a_sup_set_class f4_sbcom2 a_sup_set_class a_wceq f3_sbcom2 a_wal a_wn f1_sbcom2 a_sup_set_class f2_sbcom2 a_sup_set_class a_wceq f3_sbcom2 a_sup_set_class f4_sbcom2 a_sup_set_class a_wceq f0_sbcom2 a_wi f3_sbcom2 a_wal a_wi f1_sbcom2 a_wal p_sylan9bb f1_sbcom2 a_sup_set_class f2_sbcom2 a_sup_set_class a_wceq f1_sbcom2 a_wal a_wn f3_sbcom2 a_sup_set_class f4_sbcom2 a_sup_set_class a_wceq f3_sbcom2 a_wal a_wn a_wa f3_sbcom2 a_sup_set_class f4_sbcom2 a_sup_set_class a_wceq f1_sbcom2 a_sup_set_class f2_sbcom2 a_sup_set_class a_wceq f0_sbcom2 a_wi f1_sbcom2 a_wal a_wi f3_sbcom2 a_wal f1_sbcom2 a_sup_set_class f2_sbcom2 a_sup_set_class a_wceq f3_sbcom2 a_sup_set_class f4_sbcom2 a_sup_set_class a_wceq f0_sbcom2 a_wi f3_sbcom2 a_wal a_wi f1_sbcom2 a_wal f0_sbcom2 f1_sbcom2 f2_sbcom2 a_wsb f3_sbcom2 f4_sbcom2 a_wsb f0_sbcom2 f3_sbcom2 f4_sbcom2 a_wsb f1_sbcom2 f2_sbcom2 a_wsb p_3bitr4d f1_sbcom2 a_sup_set_class f2_sbcom2 a_sup_set_class a_wceq f1_sbcom2 a_wal a_wn f3_sbcom2 a_sup_set_class f4_sbcom2 a_sup_set_class a_wceq f3_sbcom2 a_wal a_wn f0_sbcom2 f1_sbcom2 f2_sbcom2 a_wsb f3_sbcom2 f4_sbcom2 a_wsb f0_sbcom2 f3_sbcom2 f4_sbcom2 a_wsb f1_sbcom2 f2_sbcom2 a_wsb a_wb p_ex f1_sbcom2 f2_sbcom2 f3_sbcom2 p_nfae f0_sbcom2 f1_sbcom2 f2_sbcom2 p_sbequ12 f1_sbcom2 a_sup_set_class f2_sbcom2 a_sup_set_class a_wceq f0_sbcom2 f0_sbcom2 f1_sbcom2 f2_sbcom2 a_wsb a_wb f1_sbcom2 p_sps f1_sbcom2 a_sup_set_class f2_sbcom2 a_sup_set_class a_wceq f1_sbcom2 a_wal f0_sbcom2 f0_sbcom2 f1_sbcom2 f2_sbcom2 a_wsb f3_sbcom2 f4_sbcom2 p_sbbid f0_sbcom2 f3_sbcom2 f4_sbcom2 a_wsb f1_sbcom2 f2_sbcom2 p_sbequ12 f1_sbcom2 a_sup_set_class f2_sbcom2 a_sup_set_class a_wceq f0_sbcom2 f3_sbcom2 f4_sbcom2 a_wsb f0_sbcom2 f3_sbcom2 f4_sbcom2 a_wsb f1_sbcom2 f2_sbcom2 a_wsb a_wb f1_sbcom2 p_sps f1_sbcom2 a_sup_set_class f2_sbcom2 a_sup_set_class a_wceq f1_sbcom2 a_wal f0_sbcom2 f3_sbcom2 f4_sbcom2 a_wsb f0_sbcom2 f1_sbcom2 f2_sbcom2 a_wsb f3_sbcom2 f4_sbcom2 a_wsb f0_sbcom2 f3_sbcom2 f4_sbcom2 a_wsb f1_sbcom2 f2_sbcom2 a_wsb p_bitr3d f0_sbcom2 f1_sbcom2 f2_sbcom2 a_wsb f3_sbcom2 f4_sbcom2 p_sbequ12 f3_sbcom2 a_sup_set_class f4_sbcom2 a_sup_set_class a_wceq f0_sbcom2 f1_sbcom2 f2_sbcom2 a_wsb f0_sbcom2 f1_sbcom2 f2_sbcom2 a_wsb f3_sbcom2 f4_sbcom2 a_wsb a_wb f3_sbcom2 p_sps f3_sbcom2 f4_sbcom2 f1_sbcom2 p_nfae f0_sbcom2 f3_sbcom2 f4_sbcom2 p_sbequ12 f3_sbcom2 a_sup_set_class f4_sbcom2 a_sup_set_class a_wceq f0_sbcom2 f0_sbcom2 f3_sbcom2 f4_sbcom2 a_wsb a_wb f3_sbcom2 p_sps f3_sbcom2 a_sup_set_class f4_sbcom2 a_sup_set_class a_wceq f3_sbcom2 a_wal f0_sbcom2 f0_sbcom2 f3_sbcom2 f4_sbcom2 a_wsb f1_sbcom2 f2_sbcom2 p_sbbid f3_sbcom2 a_sup_set_class f4_sbcom2 a_sup_set_class a_wceq f3_sbcom2 a_wal f0_sbcom2 f1_sbcom2 f2_sbcom2 a_wsb f0_sbcom2 f1_sbcom2 f2_sbcom2 a_wsb f3_sbcom2 f4_sbcom2 a_wsb f0_sbcom2 f3_sbcom2 f4_sbcom2 a_wsb f1_sbcom2 f2_sbcom2 a_wsb p_bitr3d f1_sbcom2 a_sup_set_class f2_sbcom2 a_sup_set_class a_wceq f1_sbcom2 a_wal f3_sbcom2 a_sup_set_class f4_sbcom2 a_sup_set_class a_wceq f3_sbcom2 a_wal f0_sbcom2 f1_sbcom2 f2_sbcom2 a_wsb f3_sbcom2 f4_sbcom2 a_wsb f0_sbcom2 f3_sbcom2 f4_sbcom2 a_wsb f1_sbcom2 f2_sbcom2 a_wsb a_wb p_pm2.61ii $.
$}

$(Theorem *11.07 in [WhiteheadRussell] p. 159.  (Contributed by Andrew
       Salmon, 17-Jun-2011.) $)

${
	$v ph x y z w  $.
	$d ph x y z  $.
	$d w x z  $.
	f0_pm11.07 $f wff ph $.
	f1_pm11.07 $f set x $.
	f2_pm11.07 $f set y $.
	f3_pm11.07 $f set z $.
	f4_pm11.07 $f set w $.
	p_pm11.07 $p |- ( [ w / x ] [ y / z ] ph <-> [ y / x ] [ w / z ] ph ) $= f1_pm11.07 f4_pm11.07 p_a9ev f3_pm11.07 f2_pm11.07 p_a9ev f1_pm11.07 a_sup_set_class f4_pm11.07 a_sup_set_class a_wceq f1_pm11.07 a_wex f3_pm11.07 a_sup_set_class f2_pm11.07 a_sup_set_class a_wceq f3_pm11.07 a_wex p_pm3.2i f1_pm11.07 f2_pm11.07 p_a9ev f3_pm11.07 f4_pm11.07 p_a9ev f1_pm11.07 a_sup_set_class f2_pm11.07 a_sup_set_class a_wceq f1_pm11.07 a_wex f3_pm11.07 a_sup_set_class f4_pm11.07 a_sup_set_class a_wceq f3_pm11.07 a_wex p_pm3.2i f1_pm11.07 a_sup_set_class f4_pm11.07 a_sup_set_class a_wceq f1_pm11.07 a_wex f3_pm11.07 a_sup_set_class f2_pm11.07 a_sup_set_class a_wceq f3_pm11.07 a_wex a_wa f1_pm11.07 a_sup_set_class f2_pm11.07 a_sup_set_class a_wceq f1_pm11.07 a_wex f3_pm11.07 a_sup_set_class f4_pm11.07 a_sup_set_class a_wceq f3_pm11.07 a_wex a_wa p_2th f1_pm11.07 a_sup_set_class f4_pm11.07 a_sup_set_class a_wceq f3_pm11.07 a_sup_set_class f2_pm11.07 a_sup_set_class a_wceq f1_pm11.07 f3_pm11.07 p_eeanv f1_pm11.07 a_sup_set_class f2_pm11.07 a_sup_set_class a_wceq f3_pm11.07 a_sup_set_class f4_pm11.07 a_sup_set_class a_wceq f1_pm11.07 f3_pm11.07 p_eeanv f1_pm11.07 a_sup_set_class f4_pm11.07 a_sup_set_class a_wceq f1_pm11.07 a_wex f3_pm11.07 a_sup_set_class f2_pm11.07 a_sup_set_class a_wceq f3_pm11.07 a_wex a_wa f1_pm11.07 a_sup_set_class f2_pm11.07 a_sup_set_class a_wceq f1_pm11.07 a_wex f3_pm11.07 a_sup_set_class f4_pm11.07 a_sup_set_class a_wceq f3_pm11.07 a_wex a_wa f1_pm11.07 a_sup_set_class f4_pm11.07 a_sup_set_class a_wceq f3_pm11.07 a_sup_set_class f2_pm11.07 a_sup_set_class a_wceq a_wa f3_pm11.07 a_wex f1_pm11.07 a_wex f1_pm11.07 a_sup_set_class f2_pm11.07 a_sup_set_class a_wceq f3_pm11.07 a_sup_set_class f4_pm11.07 a_sup_set_class a_wceq a_wa f3_pm11.07 a_wex f1_pm11.07 a_wex p_3bitr4i f1_pm11.07 a_sup_set_class f4_pm11.07 a_sup_set_class a_wceq f3_pm11.07 a_sup_set_class f2_pm11.07 a_sup_set_class a_wceq a_wa f3_pm11.07 a_wex f1_pm11.07 a_wex f1_pm11.07 a_sup_set_class f2_pm11.07 a_sup_set_class a_wceq f3_pm11.07 a_sup_set_class f4_pm11.07 a_sup_set_class a_wceq a_wa f3_pm11.07 a_wex f1_pm11.07 a_wex f0_pm11.07 p_anbi1i f1_pm11.07 a_sup_set_class f4_pm11.07 a_sup_set_class a_wceq f3_pm11.07 a_sup_set_class f2_pm11.07 a_sup_set_class a_wceq a_wa f0_pm11.07 f1_pm11.07 f3_pm11.07 p_19.41vv f1_pm11.07 a_sup_set_class f2_pm11.07 a_sup_set_class a_wceq f3_pm11.07 a_sup_set_class f4_pm11.07 a_sup_set_class a_wceq a_wa f0_pm11.07 f1_pm11.07 f3_pm11.07 p_19.41vv f1_pm11.07 a_sup_set_class f4_pm11.07 a_sup_set_class a_wceq f3_pm11.07 a_sup_set_class f2_pm11.07 a_sup_set_class a_wceq a_wa f3_pm11.07 a_wex f1_pm11.07 a_wex f0_pm11.07 a_wa f1_pm11.07 a_sup_set_class f2_pm11.07 a_sup_set_class a_wceq f3_pm11.07 a_sup_set_class f4_pm11.07 a_sup_set_class a_wceq a_wa f3_pm11.07 a_wex f1_pm11.07 a_wex f0_pm11.07 a_wa f1_pm11.07 a_sup_set_class f4_pm11.07 a_sup_set_class a_wceq f3_pm11.07 a_sup_set_class f2_pm11.07 a_sup_set_class a_wceq a_wa f0_pm11.07 a_wa f3_pm11.07 a_wex f1_pm11.07 a_wex f1_pm11.07 a_sup_set_class f2_pm11.07 a_sup_set_class a_wceq f3_pm11.07 a_sup_set_class f4_pm11.07 a_sup_set_class a_wceq a_wa f0_pm11.07 a_wa f3_pm11.07 a_wex f1_pm11.07 a_wex p_3bitr4i f0_pm11.07 f1_pm11.07 f3_pm11.07 f4_pm11.07 f2_pm11.07 p_2sb5 f0_pm11.07 f1_pm11.07 f3_pm11.07 f2_pm11.07 f4_pm11.07 p_2sb5 f1_pm11.07 a_sup_set_class f4_pm11.07 a_sup_set_class a_wceq f3_pm11.07 a_sup_set_class f2_pm11.07 a_sup_set_class a_wceq a_wa f0_pm11.07 a_wa f3_pm11.07 a_wex f1_pm11.07 a_wex f1_pm11.07 a_sup_set_class f2_pm11.07 a_sup_set_class a_wceq f3_pm11.07 a_sup_set_class f4_pm11.07 a_sup_set_class a_wceq a_wa f0_pm11.07 a_wa f3_pm11.07 a_wex f1_pm11.07 a_wex f0_pm11.07 f3_pm11.07 f2_pm11.07 a_wsb f1_pm11.07 f4_pm11.07 a_wsb f0_pm11.07 f3_pm11.07 f4_pm11.07 a_wsb f1_pm11.07 f2_pm11.07 a_wsb p_3bitr4i $.
$}

$(Equivalence for substitution.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph x y  $.
	$d x y  $.
	f0_sb6a $f wff ph $.
	f1_sb6a $f set x $.
	f2_sb6a $f set y $.
	p_sb6a $p |- ( [ y / x ] ph <-> A. x ( x = y -> [ x / y ] ph ) ) $= f0_sb6a f1_sb6a f2_sb6a p_sb6 f0_sb6a f2_sb6a f1_sb6a p_sbequ12 f0_sb6a f0_sb6a f2_sb6a f1_sb6a a_wsb a_wb f2_sb6a f1_sb6a p_equcoms f1_sb6a a_sup_set_class f2_sb6a a_sup_set_class a_wceq f0_sb6a f0_sb6a f2_sb6a f1_sb6a a_wsb p_pm5.74i f1_sb6a a_sup_set_class f2_sb6a a_sup_set_class a_wceq f0_sb6a a_wi f1_sb6a a_sup_set_class f2_sb6a a_sup_set_class a_wceq f0_sb6a f2_sb6a f1_sb6a a_wsb a_wi f1_sb6a p_albii f0_sb6a f1_sb6a f2_sb6a a_wsb f1_sb6a a_sup_set_class f2_sb6a a_sup_set_class a_wceq f0_sb6a a_wi f1_sb6a a_wal f1_sb6a a_sup_set_class f2_sb6a a_sup_set_class a_wceq f0_sb6a f2_sb6a f1_sb6a a_wsb a_wi f1_sb6a a_wal p_bitri $.
$}

$(Reversed double substitution.  (Contributed by NM, 3-Feb-2005.)
       (Revised by Mario Carneiro, 6-Oct-2016.) $)

${
	$v ph x y z w  $.
	$d x y  $.
	$d x w  $.
	$d y z  $.
	$d z w  $.
	f0_2sb5rf $f wff ph $.
	f1_2sb5rf $f set x $.
	f2_2sb5rf $f set y $.
	f3_2sb5rf $f set z $.
	f4_2sb5rf $f set w $.
	e0_2sb5rf $e |- F/ z ph $.
	e1_2sb5rf $e |- F/ w ph $.
	p_2sb5rf $p |- ( ph <-> E. z E. w ( ( z = x /\ w = y ) /\ [ z / x ] [ w / y ] ph ) ) $= e0_2sb5rf f0_2sb5rf f1_2sb5rf f3_2sb5rf p_sb5rf f3_2sb5rf a_sup_set_class f1_2sb5rf a_sup_set_class a_wceq f4_2sb5rf a_sup_set_class f2_2sb5rf a_sup_set_class a_wceq f0_2sb5rf f1_2sb5rf f3_2sb5rf a_wsb f2_2sb5rf f4_2sb5rf a_wsb a_wa f4_2sb5rf p_19.42v f0_2sb5rf f2_2sb5rf f4_2sb5rf f1_2sb5rf f3_2sb5rf p_sbcom2 f0_2sb5rf f2_2sb5rf f4_2sb5rf a_wsb f1_2sb5rf f3_2sb5rf a_wsb f0_2sb5rf f1_2sb5rf f3_2sb5rf a_wsb f2_2sb5rf f4_2sb5rf a_wsb f3_2sb5rf a_sup_set_class f1_2sb5rf a_sup_set_class a_wceq f4_2sb5rf a_sup_set_class f2_2sb5rf a_sup_set_class a_wceq a_wa p_anbi2i f3_2sb5rf a_sup_set_class f1_2sb5rf a_sup_set_class a_wceq f4_2sb5rf a_sup_set_class f2_2sb5rf a_sup_set_class a_wceq f0_2sb5rf f1_2sb5rf f3_2sb5rf a_wsb f2_2sb5rf f4_2sb5rf a_wsb p_anass f3_2sb5rf a_sup_set_class f1_2sb5rf a_sup_set_class a_wceq f4_2sb5rf a_sup_set_class f2_2sb5rf a_sup_set_class a_wceq a_wa f0_2sb5rf f2_2sb5rf f4_2sb5rf a_wsb f1_2sb5rf f3_2sb5rf a_wsb a_wa f3_2sb5rf a_sup_set_class f1_2sb5rf a_sup_set_class a_wceq f4_2sb5rf a_sup_set_class f2_2sb5rf a_sup_set_class a_wceq a_wa f0_2sb5rf f1_2sb5rf f3_2sb5rf a_wsb f2_2sb5rf f4_2sb5rf a_wsb a_wa f3_2sb5rf a_sup_set_class f1_2sb5rf a_sup_set_class a_wceq f4_2sb5rf a_sup_set_class f2_2sb5rf a_sup_set_class a_wceq f0_2sb5rf f1_2sb5rf f3_2sb5rf a_wsb f2_2sb5rf f4_2sb5rf a_wsb a_wa a_wa p_bitri f3_2sb5rf a_sup_set_class f1_2sb5rf a_sup_set_class a_wceq f4_2sb5rf a_sup_set_class f2_2sb5rf a_sup_set_class a_wceq a_wa f0_2sb5rf f2_2sb5rf f4_2sb5rf a_wsb f1_2sb5rf f3_2sb5rf a_wsb a_wa f3_2sb5rf a_sup_set_class f1_2sb5rf a_sup_set_class a_wceq f4_2sb5rf a_sup_set_class f2_2sb5rf a_sup_set_class a_wceq f0_2sb5rf f1_2sb5rf f3_2sb5rf a_wsb f2_2sb5rf f4_2sb5rf a_wsb a_wa a_wa f4_2sb5rf p_exbii e1_2sb5rf f0_2sb5rf f1_2sb5rf f3_2sb5rf f4_2sb5rf p_nfsb f0_2sb5rf f1_2sb5rf f3_2sb5rf a_wsb f2_2sb5rf f4_2sb5rf p_sb5rf f0_2sb5rf f1_2sb5rf f3_2sb5rf a_wsb f4_2sb5rf a_sup_set_class f2_2sb5rf a_sup_set_class a_wceq f0_2sb5rf f1_2sb5rf f3_2sb5rf a_wsb f2_2sb5rf f4_2sb5rf a_wsb a_wa f4_2sb5rf a_wex f3_2sb5rf a_sup_set_class f1_2sb5rf a_sup_set_class a_wceq p_anbi2i f3_2sb5rf a_sup_set_class f1_2sb5rf a_sup_set_class a_wceq f4_2sb5rf a_sup_set_class f2_2sb5rf a_sup_set_class a_wceq f0_2sb5rf f1_2sb5rf f3_2sb5rf a_wsb f2_2sb5rf f4_2sb5rf a_wsb a_wa a_wa f4_2sb5rf a_wex f3_2sb5rf a_sup_set_class f1_2sb5rf a_sup_set_class a_wceq f4_2sb5rf a_sup_set_class f2_2sb5rf a_sup_set_class a_wceq f0_2sb5rf f1_2sb5rf f3_2sb5rf a_wsb f2_2sb5rf f4_2sb5rf a_wsb a_wa f4_2sb5rf a_wex a_wa f3_2sb5rf a_sup_set_class f1_2sb5rf a_sup_set_class a_wceq f4_2sb5rf a_sup_set_class f2_2sb5rf a_sup_set_class a_wceq a_wa f0_2sb5rf f2_2sb5rf f4_2sb5rf a_wsb f1_2sb5rf f3_2sb5rf a_wsb a_wa f4_2sb5rf a_wex f3_2sb5rf a_sup_set_class f1_2sb5rf a_sup_set_class a_wceq f0_2sb5rf f1_2sb5rf f3_2sb5rf a_wsb a_wa p_3bitr4ri f3_2sb5rf a_sup_set_class f1_2sb5rf a_sup_set_class a_wceq f0_2sb5rf f1_2sb5rf f3_2sb5rf a_wsb a_wa f3_2sb5rf a_sup_set_class f1_2sb5rf a_sup_set_class a_wceq f4_2sb5rf a_sup_set_class f2_2sb5rf a_sup_set_class a_wceq a_wa f0_2sb5rf f2_2sb5rf f4_2sb5rf a_wsb f1_2sb5rf f3_2sb5rf a_wsb a_wa f4_2sb5rf a_wex f3_2sb5rf p_exbii f0_2sb5rf f3_2sb5rf a_sup_set_class f1_2sb5rf a_sup_set_class a_wceq f0_2sb5rf f1_2sb5rf f3_2sb5rf a_wsb a_wa f3_2sb5rf a_wex f3_2sb5rf a_sup_set_class f1_2sb5rf a_sup_set_class a_wceq f4_2sb5rf a_sup_set_class f2_2sb5rf a_sup_set_class a_wceq a_wa f0_2sb5rf f2_2sb5rf f4_2sb5rf a_wsb f1_2sb5rf f3_2sb5rf a_wsb a_wa f4_2sb5rf a_wex f3_2sb5rf a_wex p_bitri $.
$}

$(Reversed double substitution.  (Contributed by NM, 3-Feb-2005.)
       (Revised by Mario Carneiro, 6-Oct-2016.) $)

${
	$v ph x y z w  $.
	$d x y  $.
	$d x w  $.
	$d y z  $.
	$d z w  $.
	f0_2sb6rf $f wff ph $.
	f1_2sb6rf $f set x $.
	f2_2sb6rf $f set y $.
	f3_2sb6rf $f set z $.
	f4_2sb6rf $f set w $.
	e0_2sb6rf $e |- F/ z ph $.
	e1_2sb6rf $e |- F/ w ph $.
	p_2sb6rf $p |- ( ph <-> A. z A. w ( ( z = x /\ w = y ) -> [ z / x ] [ w / y ] ph ) ) $= e0_2sb6rf f0_2sb6rf f1_2sb6rf f3_2sb6rf p_sb6rf f3_2sb6rf a_sup_set_class f1_2sb6rf a_sup_set_class a_wceq f4_2sb6rf a_sup_set_class f2_2sb6rf a_sup_set_class a_wceq f0_2sb6rf f1_2sb6rf f3_2sb6rf a_wsb f2_2sb6rf f4_2sb6rf a_wsb a_wi f4_2sb6rf p_19.21v f0_2sb6rf f2_2sb6rf f4_2sb6rf f1_2sb6rf f3_2sb6rf p_sbcom2 f0_2sb6rf f2_2sb6rf f4_2sb6rf a_wsb f1_2sb6rf f3_2sb6rf a_wsb f0_2sb6rf f1_2sb6rf f3_2sb6rf a_wsb f2_2sb6rf f4_2sb6rf a_wsb f3_2sb6rf a_sup_set_class f1_2sb6rf a_sup_set_class a_wceq f4_2sb6rf a_sup_set_class f2_2sb6rf a_sup_set_class a_wceq a_wa p_imbi2i f3_2sb6rf a_sup_set_class f1_2sb6rf a_sup_set_class a_wceq f4_2sb6rf a_sup_set_class f2_2sb6rf a_sup_set_class a_wceq f0_2sb6rf f1_2sb6rf f3_2sb6rf a_wsb f2_2sb6rf f4_2sb6rf a_wsb p_impexp f3_2sb6rf a_sup_set_class f1_2sb6rf a_sup_set_class a_wceq f4_2sb6rf a_sup_set_class f2_2sb6rf a_sup_set_class a_wceq a_wa f0_2sb6rf f2_2sb6rf f4_2sb6rf a_wsb f1_2sb6rf f3_2sb6rf a_wsb a_wi f3_2sb6rf a_sup_set_class f1_2sb6rf a_sup_set_class a_wceq f4_2sb6rf a_sup_set_class f2_2sb6rf a_sup_set_class a_wceq a_wa f0_2sb6rf f1_2sb6rf f3_2sb6rf a_wsb f2_2sb6rf f4_2sb6rf a_wsb a_wi f3_2sb6rf a_sup_set_class f1_2sb6rf a_sup_set_class a_wceq f4_2sb6rf a_sup_set_class f2_2sb6rf a_sup_set_class a_wceq f0_2sb6rf f1_2sb6rf f3_2sb6rf a_wsb f2_2sb6rf f4_2sb6rf a_wsb a_wi a_wi p_bitri f3_2sb6rf a_sup_set_class f1_2sb6rf a_sup_set_class a_wceq f4_2sb6rf a_sup_set_class f2_2sb6rf a_sup_set_class a_wceq a_wa f0_2sb6rf f2_2sb6rf f4_2sb6rf a_wsb f1_2sb6rf f3_2sb6rf a_wsb a_wi f3_2sb6rf a_sup_set_class f1_2sb6rf a_sup_set_class a_wceq f4_2sb6rf a_sup_set_class f2_2sb6rf a_sup_set_class a_wceq f0_2sb6rf f1_2sb6rf f3_2sb6rf a_wsb f2_2sb6rf f4_2sb6rf a_wsb a_wi a_wi f4_2sb6rf p_albii e1_2sb6rf f0_2sb6rf f1_2sb6rf f3_2sb6rf f4_2sb6rf p_nfsb f0_2sb6rf f1_2sb6rf f3_2sb6rf a_wsb f2_2sb6rf f4_2sb6rf p_sb6rf f0_2sb6rf f1_2sb6rf f3_2sb6rf a_wsb f4_2sb6rf a_sup_set_class f2_2sb6rf a_sup_set_class a_wceq f0_2sb6rf f1_2sb6rf f3_2sb6rf a_wsb f2_2sb6rf f4_2sb6rf a_wsb a_wi f4_2sb6rf a_wal f3_2sb6rf a_sup_set_class f1_2sb6rf a_sup_set_class a_wceq p_imbi2i f3_2sb6rf a_sup_set_class f1_2sb6rf a_sup_set_class a_wceq f4_2sb6rf a_sup_set_class f2_2sb6rf a_sup_set_class a_wceq f0_2sb6rf f1_2sb6rf f3_2sb6rf a_wsb f2_2sb6rf f4_2sb6rf a_wsb a_wi a_wi f4_2sb6rf a_wal f3_2sb6rf a_sup_set_class f1_2sb6rf a_sup_set_class a_wceq f4_2sb6rf a_sup_set_class f2_2sb6rf a_sup_set_class a_wceq f0_2sb6rf f1_2sb6rf f3_2sb6rf a_wsb f2_2sb6rf f4_2sb6rf a_wsb a_wi f4_2sb6rf a_wal a_wi f3_2sb6rf a_sup_set_class f1_2sb6rf a_sup_set_class a_wceq f4_2sb6rf a_sup_set_class f2_2sb6rf a_sup_set_class a_wceq a_wa f0_2sb6rf f2_2sb6rf f4_2sb6rf a_wsb f1_2sb6rf f3_2sb6rf a_wsb a_wi f4_2sb6rf a_wal f3_2sb6rf a_sup_set_class f1_2sb6rf a_sup_set_class a_wceq f0_2sb6rf f1_2sb6rf f3_2sb6rf a_wsb a_wi p_3bitr4ri f3_2sb6rf a_sup_set_class f1_2sb6rf a_sup_set_class a_wceq f0_2sb6rf f1_2sb6rf f3_2sb6rf a_wsb a_wi f3_2sb6rf a_sup_set_class f1_2sb6rf a_sup_set_class a_wceq f4_2sb6rf a_sup_set_class f2_2sb6rf a_sup_set_class a_wceq a_wa f0_2sb6rf f2_2sb6rf f4_2sb6rf a_wsb f1_2sb6rf f3_2sb6rf a_wsb a_wi f4_2sb6rf a_wal f3_2sb6rf p_albii f0_2sb6rf f3_2sb6rf a_sup_set_class f1_2sb6rf a_sup_set_class a_wceq f0_2sb6rf f1_2sb6rf f3_2sb6rf a_wsb a_wi f3_2sb6rf a_wal f3_2sb6rf a_sup_set_class f1_2sb6rf a_sup_set_class a_wceq f4_2sb6rf a_sup_set_class f2_2sb6rf a_sup_set_class a_wceq a_wa f0_2sb6rf f2_2sb6rf f4_2sb6rf a_wsb f1_2sb6rf f3_2sb6rf a_wsb a_wi f4_2sb6rf a_wal f3_2sb6rf a_wal p_bitri $.
$}

$(An alternate definition of proper substitution ~ df-sb .  By introducing
       a dummy variable ` z ` in the definiens, we are able to eliminate any
       distinct variable restrictions among the variables ` x ` , ` y ` , and
       ` ph ` of the definiendum.  No distinct variable conflicts arise because
       ` z ` effectively insulates ` x ` from ` y ` .  To achieve this, we use
       a chain of two substitutions in the form of ~ sb5 , first ` z ` for
       ` x ` then ` y ` for ` z ` .  Compare Definition 2.1'' of [Quine] p. 17,
       which is obtained from this theorem by applying ~ df-clab .  Theorem
       ~ sb7h provides a version where ` ph ` and ` z ` don't have to be
       distinct.  (Contributed by NM, 28-Jan-2004.) $)

${
	$v ph x y z  $.
	$d x z  $.
	$d y z  $.
	$d z ph  $.
	f0_dfsb7 $f wff ph $.
	f1_dfsb7 $f set x $.
	f2_dfsb7 $f set y $.
	f3_dfsb7 $f set z $.
	p_dfsb7 $p |- ( [ y / x ] ph <-> E. z ( z = y /\ E. x ( x = z /\ ph ) ) ) $= f0_dfsb7 f1_dfsb7 f3_dfsb7 p_sb5 f0_dfsb7 f1_dfsb7 f3_dfsb7 a_wsb f1_dfsb7 a_sup_set_class f3_dfsb7 a_sup_set_class a_wceq f0_dfsb7 a_wa f1_dfsb7 a_wex f3_dfsb7 f2_dfsb7 p_sbbii f0_dfsb7 f3_dfsb7 p_nfv f0_dfsb7 f1_dfsb7 f2_dfsb7 f3_dfsb7 p_sbco2 f1_dfsb7 a_sup_set_class f3_dfsb7 a_sup_set_class a_wceq f0_dfsb7 a_wa f1_dfsb7 a_wex f3_dfsb7 f2_dfsb7 p_sb5 f0_dfsb7 f1_dfsb7 f3_dfsb7 a_wsb f3_dfsb7 f2_dfsb7 a_wsb f1_dfsb7 a_sup_set_class f3_dfsb7 a_sup_set_class a_wceq f0_dfsb7 a_wa f1_dfsb7 a_wex f3_dfsb7 f2_dfsb7 a_wsb f0_dfsb7 f1_dfsb7 f2_dfsb7 a_wsb f3_dfsb7 a_sup_set_class f2_dfsb7 a_sup_set_class a_wceq f1_dfsb7 a_sup_set_class f3_dfsb7 a_sup_set_class a_wceq f0_dfsb7 a_wa f1_dfsb7 a_wex a_wa f3_dfsb7 a_wex p_3bitr3i $.
$}

$(This version of ~ dfsb7 does not require that ` ph ` and ` z ` be
       distinct.  This permits it to be used as a definition for substitution
       in a formalization that omits the logically redundant axiom ~ ax-17 i.e.
       that doesn't have the concept of a variable not occurring in a wff.
       ( ~ df-sb is also suitable, but its mixing of free and bound variables
       is distasteful to some logicians.)  (Contributed by NM, 26-Jul-2006.)
       (Revised by Mario Carneiro, 6-Oct-2016.) $)

${
	$v ph x y z  $.
	$d x z  $.
	$d y z  $.
	$d ph  $.
	f0_sb7f $f wff ph $.
	f1_sb7f $f set x $.
	f2_sb7f $f set y $.
	f3_sb7f $f set z $.
	e0_sb7f $e |- F/ z ph $.
	p_sb7f $p |- ( [ y / x ] ph <-> E. z ( z = y /\ E. x ( x = z /\ ph ) ) ) $= f0_sb7f f1_sb7f f3_sb7f p_sb5 f0_sb7f f1_sb7f f3_sb7f a_wsb f1_sb7f a_sup_set_class f3_sb7f a_sup_set_class a_wceq f0_sb7f a_wa f1_sb7f a_wex f3_sb7f f2_sb7f p_sbbii e0_sb7f f0_sb7f f1_sb7f f2_sb7f f3_sb7f p_sbco2 f1_sb7f a_sup_set_class f3_sb7f a_sup_set_class a_wceq f0_sb7f a_wa f1_sb7f a_wex f3_sb7f f2_sb7f p_sb5 f0_sb7f f1_sb7f f3_sb7f a_wsb f3_sb7f f2_sb7f a_wsb f1_sb7f a_sup_set_class f3_sb7f a_sup_set_class a_wceq f0_sb7f a_wa f1_sb7f a_wex f3_sb7f f2_sb7f a_wsb f0_sb7f f1_sb7f f2_sb7f a_wsb f3_sb7f a_sup_set_class f2_sb7f a_sup_set_class a_wceq f1_sb7f a_sup_set_class f3_sb7f a_sup_set_class a_wceq f0_sb7f a_wa f1_sb7f a_wex a_wa f3_sb7f a_wex p_3bitr3i $.
$}

$(This version of ~ dfsb7 does not require that ` ph ` and ` z ` be
       distinct.  This permits it to be used as a definition for substitution
       in a formalization that omits the logically redundant axiom ~ ax-17 i.e.
       that doesn't have the concept of a variable not occurring in a wff.
       ( ~ df-sb is also suitable, but its mixing of free and bound variables
       is distasteful to some logicians.)  (Contributed by NM, 26-Jul-2006.)
       (Proof shortened by Andrew Salmon, 25-May-2011.) $)

${
	$v ph x y z  $.
	$d x z  $.
	$d y z  $.
	$d ph  $.
	f0_sb7h $f wff ph $.
	f1_sb7h $f set x $.
	f2_sb7h $f set y $.
	f3_sb7h $f set z $.
	e0_sb7h $e |- ( ph -> A. z ph ) $.
	p_sb7h $p |- ( [ y / x ] ph <-> E. z ( z = y /\ E. x ( x = z /\ ph ) ) ) $= e0_sb7h f0_sb7h f3_sb7h p_nfi f0_sb7h f1_sb7h f2_sb7h f3_sb7h p_sb7f $.
$}

$(Hao Wang's identity axiom P6 in Irving Copi, _Symbolic Logic_ (5th ed.,
       1979), p. 328.  In traditional predicate calculus, this is a sole axiom
       for identity from which the usual ones can be derived.  (Contributed by
       NM, 9-May-2005.)  (Revised by Mario Carneiro, 6-Oct-2016.) $)

${
	$v ph x y z  $.
	$d x y  $.
	f0_sb10f $f wff ph $.
	f1_sb10f $f set x $.
	f2_sb10f $f set y $.
	f3_sb10f $f set z $.
	e0_sb10f $e |- F/ x ph $.
	p_sb10f $p |- ( [ y / z ] ph <-> E. x ( x = y /\ [ x / z ] ph ) ) $= e0_sb10f f0_sb10f f3_sb10f f2_sb10f f1_sb10f p_nfsb f0_sb10f f1_sb10f f2_sb10f f3_sb10f p_sbequ f0_sb10f f3_sb10f f1_sb10f a_wsb f0_sb10f f3_sb10f f2_sb10f a_wsb f1_sb10f f2_sb10f p_equsex f1_sb10f a_sup_set_class f2_sb10f a_sup_set_class a_wceq f0_sb10f f3_sb10f f1_sb10f a_wsb a_wa f1_sb10f a_wex f0_sb10f f3_sb10f f2_sb10f a_wsb p_bicomi $.
$}

$(An identity law for substitution.  Used in proof of Theorem 9.7 of
       [Megill] p. 449 (p. 16 of the preprint).  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v ph x y  $.
	$d x ph  $.
	f0_sbid2v $f wff ph $.
	f1_sbid2v $f set x $.
	f2_sbid2v $f set y $.
	p_sbid2v $p |- ( [ y / x ] [ x / y ] ph <-> ph ) $= f0_sbid2v f1_sbid2v p_nfv f0_sbid2v f1_sbid2v f2_sbid2v p_sbid2 $.
$}

$(Elimination of substitution.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph x y  $.
	$d x y  $.
	$d x ph  $.
	f0_sbelx $f wff ph $.
	f1_sbelx $f set x $.
	f2_sbelx $f set y $.
	p_sbelx $p |- ( ph <-> E. x ( x = y /\ [ x / y ] ph ) ) $= f0_sbelx f1_sbelx f2_sbelx p_sbid2v f0_sbelx f2_sbelx f1_sbelx a_wsb f1_sbelx f2_sbelx p_sb5 f0_sbelx f0_sbelx f2_sbelx f1_sbelx a_wsb f1_sbelx f2_sbelx a_wsb f1_sbelx a_sup_set_class f2_sbelx a_sup_set_class a_wceq f0_sbelx f2_sbelx f1_sbelx a_wsb a_wa f1_sbelx a_wex p_bitr3i $.
$}

$(Note:  A more general case could also be proved with
       "$d x z $.  $d y w $.  $d x ph $.  $d y ph $.", but with more
       difficulty. $)

$(Elimination of double substitution.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph x y z w  $.
	$d x y z  $.
	$d w y  $.
	$d x y ph  $.
	f0_sbel2x $f wff ph $.
	f1_sbel2x $f set x $.
	f2_sbel2x $f set y $.
	f3_sbel2x $f set z $.
	f4_sbel2x $f set w $.
	p_sbel2x $p |- ( ph <-> E. x E. y ( ( x = z /\ y = w ) /\ [ y / w ] [ x / z ] ph ) ) $= f0_sbel2x f3_sbel2x f1_sbel2x a_wsb f2_sbel2x f4_sbel2x p_sbelx f0_sbel2x f3_sbel2x f1_sbel2x a_wsb f2_sbel2x a_sup_set_class f4_sbel2x a_sup_set_class a_wceq f0_sbel2x f3_sbel2x f1_sbel2x a_wsb f4_sbel2x f2_sbel2x a_wsb a_wa f2_sbel2x a_wex f1_sbel2x a_sup_set_class f3_sbel2x a_sup_set_class a_wceq p_anbi2i f1_sbel2x a_sup_set_class f3_sbel2x a_sup_set_class a_wceq f0_sbel2x f3_sbel2x f1_sbel2x a_wsb a_wa f1_sbel2x a_sup_set_class f3_sbel2x a_sup_set_class a_wceq f2_sbel2x a_sup_set_class f4_sbel2x a_sup_set_class a_wceq f0_sbel2x f3_sbel2x f1_sbel2x a_wsb f4_sbel2x f2_sbel2x a_wsb a_wa f2_sbel2x a_wex a_wa f1_sbel2x p_exbii f0_sbel2x f1_sbel2x f3_sbel2x p_sbelx f1_sbel2x a_sup_set_class f3_sbel2x a_sup_set_class a_wceq f2_sbel2x a_sup_set_class f4_sbel2x a_sup_set_class a_wceq f0_sbel2x f3_sbel2x f1_sbel2x a_wsb f4_sbel2x f2_sbel2x a_wsb a_wa f1_sbel2x f2_sbel2x p_exdistr f1_sbel2x a_sup_set_class f3_sbel2x a_sup_set_class a_wceq f0_sbel2x f3_sbel2x f1_sbel2x a_wsb a_wa f1_sbel2x a_wex f1_sbel2x a_sup_set_class f3_sbel2x a_sup_set_class a_wceq f2_sbel2x a_sup_set_class f4_sbel2x a_sup_set_class a_wceq f0_sbel2x f3_sbel2x f1_sbel2x a_wsb f4_sbel2x f2_sbel2x a_wsb a_wa f2_sbel2x a_wex a_wa f1_sbel2x a_wex f0_sbel2x f1_sbel2x a_sup_set_class f3_sbel2x a_sup_set_class a_wceq f2_sbel2x a_sup_set_class f4_sbel2x a_sup_set_class a_wceq f0_sbel2x f3_sbel2x f1_sbel2x a_wsb f4_sbel2x f2_sbel2x a_wsb a_wa a_wa f2_sbel2x a_wex f1_sbel2x a_wex p_3bitr4i f1_sbel2x a_sup_set_class f3_sbel2x a_sup_set_class a_wceq f2_sbel2x a_sup_set_class f4_sbel2x a_sup_set_class a_wceq f0_sbel2x f3_sbel2x f1_sbel2x a_wsb f4_sbel2x f2_sbel2x a_wsb p_anass f1_sbel2x a_sup_set_class f3_sbel2x a_sup_set_class a_wceq f2_sbel2x a_sup_set_class f4_sbel2x a_sup_set_class a_wceq a_wa f0_sbel2x f3_sbel2x f1_sbel2x a_wsb f4_sbel2x f2_sbel2x a_wsb a_wa f1_sbel2x a_sup_set_class f3_sbel2x a_sup_set_class a_wceq f2_sbel2x a_sup_set_class f4_sbel2x a_sup_set_class a_wceq f0_sbel2x f3_sbel2x f1_sbel2x a_wsb f4_sbel2x f2_sbel2x a_wsb a_wa a_wa f1_sbel2x f2_sbel2x p_2exbii f0_sbel2x f1_sbel2x a_sup_set_class f3_sbel2x a_sup_set_class a_wceq f2_sbel2x a_sup_set_class f4_sbel2x a_sup_set_class a_wceq f0_sbel2x f3_sbel2x f1_sbel2x a_wsb f4_sbel2x f2_sbel2x a_wsb a_wa a_wa f2_sbel2x a_wex f1_sbel2x a_wex f1_sbel2x a_sup_set_class f3_sbel2x a_sup_set_class a_wceq f2_sbel2x a_sup_set_class f4_sbel2x a_sup_set_class a_wceq a_wa f0_sbel2x f3_sbel2x f1_sbel2x a_wsb f4_sbel2x f2_sbel2x a_wsb a_wa f2_sbel2x a_wex f1_sbel2x a_wex p_bitr4i $.
$}

$(A theorem used in elimination of disjoint variable restriction on ` x `
       and ` y ` by replacing it with a distinctor ` -. A. x x = z ` .
       (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph x y z  $.
	$d x y  $.
	f0_sbal1 $f wff ph $.
	f1_sbal1 $f set x $.
	f2_sbal1 $f set y $.
	f3_sbal1 $f set z $.
	p_sbal1 $p |- ( -. A. x x = z -> ( [ z / y ] A. x ph <-> A. x [ z / y ] ph ) ) $= f0_sbal1 f1_sbal1 a_wal f2_sbal1 f3_sbal1 p_sbequ12 f2_sbal1 a_sup_set_class f3_sbal1 a_sup_set_class a_wceq f0_sbal1 f1_sbal1 a_wal f0_sbal1 f1_sbal1 a_wal f2_sbal1 f3_sbal1 a_wsb a_wb f2_sbal1 p_sps f0_sbal1 f2_sbal1 f3_sbal1 p_sbequ12 f2_sbal1 a_sup_set_class f3_sbal1 a_sup_set_class a_wceq f0_sbal1 f0_sbal1 f2_sbal1 f3_sbal1 a_wsb a_wb f2_sbal1 p_sps f0_sbal1 f0_sbal1 f2_sbal1 f3_sbal1 a_wsb f2_sbal1 f3_sbal1 f1_sbal1 p_dral2 f2_sbal1 a_sup_set_class f3_sbal1 a_sup_set_class a_wceq f2_sbal1 a_wal f0_sbal1 f1_sbal1 a_wal f0_sbal1 f1_sbal1 a_wal f2_sbal1 f3_sbal1 a_wsb f0_sbal1 f2_sbal1 f3_sbal1 a_wsb f1_sbal1 a_wal p_bitr3d f2_sbal1 a_sup_set_class f3_sbal1 a_sup_set_class a_wceq f2_sbal1 a_wal f0_sbal1 f1_sbal1 a_wal f2_sbal1 f3_sbal1 a_wsb f0_sbal1 f2_sbal1 f3_sbal1 a_wsb f1_sbal1 a_wal a_wb f1_sbal1 a_sup_set_class f3_sbal1 a_sup_set_class a_wceq f1_sbal1 a_wal a_wn p_a1d f0_sbal1 f1_sbal1 p_nfa1 f0_sbal1 f1_sbal1 a_wal f2_sbal1 f3_sbal1 f1_sbal1 p_nfsb4 f1_sbal1 a_sup_set_class f3_sbal1 a_sup_set_class a_wceq f1_sbal1 a_wal a_wn f0_sbal1 f1_sbal1 a_wal f2_sbal1 f3_sbal1 a_wsb f1_sbal1 p_nfrd f0_sbal1 f1_sbal1 p_sp f0_sbal1 f1_sbal1 a_wal f0_sbal1 f2_sbal1 f3_sbal1 p_sbimi f0_sbal1 f1_sbal1 a_wal f2_sbal1 f3_sbal1 a_wsb f0_sbal1 f2_sbal1 f3_sbal1 a_wsb f1_sbal1 p_alimi f1_sbal1 a_sup_set_class f3_sbal1 a_sup_set_class a_wceq f1_sbal1 a_wal a_wn f0_sbal1 f1_sbal1 a_wal f2_sbal1 f3_sbal1 a_wsb f0_sbal1 f1_sbal1 a_wal f2_sbal1 f3_sbal1 a_wsb f1_sbal1 a_wal f0_sbal1 f2_sbal1 f3_sbal1 a_wsb f1_sbal1 a_wal p_syl6 f1_sbal1 a_sup_set_class f3_sbal1 a_sup_set_class a_wceq f1_sbal1 a_wal a_wn f0_sbal1 f1_sbal1 a_wal f2_sbal1 f3_sbal1 a_wsb f0_sbal1 f2_sbal1 f3_sbal1 a_wsb f1_sbal1 a_wal a_wi f2_sbal1 a_sup_set_class f3_sbal1 a_sup_set_class a_wceq f2_sbal1 a_wal a_wn p_adantl f0_sbal1 f2_sbal1 f3_sbal1 p_sb4 f2_sbal1 a_sup_set_class f3_sbal1 a_sup_set_class a_wceq f2_sbal1 a_wal a_wn f0_sbal1 f2_sbal1 f3_sbal1 a_wsb f2_sbal1 a_sup_set_class f3_sbal1 a_sup_set_class a_wceq f0_sbal1 a_wi f2_sbal1 a_wal f1_sbal1 p_al2imi f0_sbal1 f2_sbal1 f3_sbal1 a_wsb f1_sbal1 a_wal f2_sbal1 a_sup_set_class f3_sbal1 a_sup_set_class a_wceq f0_sbal1 a_wi f2_sbal1 a_wal f1_sbal1 a_wal a_wi f2_sbal1 f3_sbal1 f1_sbal1 p_hbnaes f2_sbal1 a_sup_set_class f3_sbal1 a_sup_set_class a_wceq f0_sbal1 a_wi f1_sbal1 f2_sbal1 a_ax-7 f2_sbal1 a_sup_set_class f3_sbal1 a_sup_set_class a_wceq f2_sbal1 a_wal a_wn f0_sbal1 f2_sbal1 f3_sbal1 a_wsb f1_sbal1 a_wal f2_sbal1 a_sup_set_class f3_sbal1 a_sup_set_class a_wceq f0_sbal1 a_wi f2_sbal1 a_wal f1_sbal1 a_wal f2_sbal1 a_sup_set_class f3_sbal1 a_sup_set_class a_wceq f0_sbal1 a_wi f1_sbal1 a_wal f2_sbal1 a_wal p_syl6 f1_sbal1 f3_sbal1 f2_sbal1 p_dveeq2 f2_sbal1 a_sup_set_class f3_sbal1 a_sup_set_class a_wceq f0_sbal1 f1_sbal1 p_alim f1_sbal1 a_sup_set_class f3_sbal1 a_sup_set_class a_wceq f1_sbal1 a_wal a_wn f2_sbal1 a_sup_set_class f3_sbal1 a_sup_set_class a_wceq f2_sbal1 a_sup_set_class f3_sbal1 a_sup_set_class a_wceq f1_sbal1 a_wal f2_sbal1 a_sup_set_class f3_sbal1 a_sup_set_class a_wceq f0_sbal1 a_wi f1_sbal1 a_wal f0_sbal1 f1_sbal1 a_wal p_syl9 f1_sbal1 a_sup_set_class f3_sbal1 a_sup_set_class a_wceq f1_sbal1 a_wal a_wn f2_sbal1 a_sup_set_class f3_sbal1 a_sup_set_class a_wceq f0_sbal1 a_wi f1_sbal1 a_wal f2_sbal1 a_sup_set_class f3_sbal1 a_sup_set_class a_wceq f0_sbal1 f1_sbal1 a_wal a_wi f2_sbal1 p_al2imi f0_sbal1 f1_sbal1 a_wal f2_sbal1 f3_sbal1 p_sb2 f1_sbal1 a_sup_set_class f3_sbal1 a_sup_set_class a_wceq f1_sbal1 a_wal a_wn f2_sbal1 a_wal f2_sbal1 a_sup_set_class f3_sbal1 a_sup_set_class a_wceq f0_sbal1 a_wi f1_sbal1 a_wal f2_sbal1 a_wal f2_sbal1 a_sup_set_class f3_sbal1 a_sup_set_class a_wceq f0_sbal1 f1_sbal1 a_wal a_wi f2_sbal1 a_wal f0_sbal1 f1_sbal1 a_wal f2_sbal1 f3_sbal1 a_wsb p_syl6 f2_sbal1 a_sup_set_class f3_sbal1 a_sup_set_class a_wceq f0_sbal1 a_wi f1_sbal1 a_wal f2_sbal1 a_wal f0_sbal1 f1_sbal1 a_wal f2_sbal1 f3_sbal1 a_wsb a_wi f1_sbal1 f3_sbal1 f2_sbal1 p_hbnaes f2_sbal1 a_sup_set_class f3_sbal1 a_sup_set_class a_wceq f2_sbal1 a_wal a_wn f0_sbal1 f2_sbal1 f3_sbal1 a_wsb f1_sbal1 a_wal f2_sbal1 a_sup_set_class f3_sbal1 a_sup_set_class a_wceq f0_sbal1 a_wi f1_sbal1 a_wal f2_sbal1 a_wal f1_sbal1 a_sup_set_class f3_sbal1 a_sup_set_class a_wceq f1_sbal1 a_wal a_wn f0_sbal1 f1_sbal1 a_wal f2_sbal1 f3_sbal1 a_wsb p_sylan9 f2_sbal1 a_sup_set_class f3_sbal1 a_sup_set_class a_wceq f2_sbal1 a_wal a_wn f1_sbal1 a_sup_set_class f3_sbal1 a_sup_set_class a_wceq f1_sbal1 a_wal a_wn a_wa f0_sbal1 f1_sbal1 a_wal f2_sbal1 f3_sbal1 a_wsb f0_sbal1 f2_sbal1 f3_sbal1 a_wsb f1_sbal1 a_wal p_impbid f2_sbal1 a_sup_set_class f3_sbal1 a_sup_set_class a_wceq f2_sbal1 a_wal a_wn f1_sbal1 a_sup_set_class f3_sbal1 a_sup_set_class a_wceq f1_sbal1 a_wal a_wn f0_sbal1 f1_sbal1 a_wal f2_sbal1 f3_sbal1 a_wsb f0_sbal1 f2_sbal1 f3_sbal1 a_wsb f1_sbal1 a_wal a_wb p_ex f2_sbal1 a_sup_set_class f3_sbal1 a_sup_set_class a_wceq f2_sbal1 a_wal f1_sbal1 a_sup_set_class f3_sbal1 a_sup_set_class a_wceq f1_sbal1 a_wal a_wn f0_sbal1 f1_sbal1 a_wal f2_sbal1 f3_sbal1 a_wsb f0_sbal1 f2_sbal1 f3_sbal1 a_wsb f1_sbal1 a_wal a_wb a_wi p_pm2.61i $.
$}

$(Move universal quantifier in and out of substitution.  (Contributed by
       NM, 5-Aug-1993.) $)

${
	$v ph x y z  $.
	$d x y  $.
	$d x z  $.
	f0_sbal $f wff ph $.
	f1_sbal $f set x $.
	f2_sbal $f set y $.
	f3_sbal $f set z $.
	p_sbal $p |- ( [ z / y ] A. x ph <-> A. x [ z / y ] ph ) $= f0_sbal f1_sbal f3_sbal f1_sbal p_a16gb f1_sbal a_sup_set_class f3_sbal a_sup_set_class a_wceq f1_sbal a_wal f0_sbal f0_sbal f1_sbal a_wal a_wb f2_sbal f3_sbal p_sbimi f1_sbal f3_sbal f2_sbal f3_sbal p_sbequ5 f0_sbal f0_sbal f1_sbal a_wal f2_sbal f3_sbal p_sbbi f1_sbal a_sup_set_class f3_sbal a_sup_set_class a_wceq f1_sbal a_wal f2_sbal f3_sbal a_wsb f0_sbal f0_sbal f1_sbal a_wal a_wb f2_sbal f3_sbal a_wsb f1_sbal a_sup_set_class f3_sbal a_sup_set_class a_wceq f1_sbal a_wal f0_sbal f2_sbal f3_sbal a_wsb f0_sbal f1_sbal a_wal f2_sbal f3_sbal a_wsb a_wb p_3imtr3i f0_sbal f2_sbal f3_sbal a_wsb f1_sbal f3_sbal f1_sbal p_a16gb f1_sbal a_sup_set_class f3_sbal a_sup_set_class a_wceq f1_sbal a_wal f0_sbal f2_sbal f3_sbal a_wsb f0_sbal f1_sbal a_wal f2_sbal f3_sbal a_wsb f0_sbal f2_sbal f3_sbal a_wsb f1_sbal a_wal p_bitr3d f0_sbal f1_sbal f2_sbal f3_sbal p_sbal1 f1_sbal a_sup_set_class f3_sbal a_sup_set_class a_wceq f1_sbal a_wal f0_sbal f1_sbal a_wal f2_sbal f3_sbal a_wsb f0_sbal f2_sbal f3_sbal a_wsb f1_sbal a_wal a_wb p_pm2.61i $.
$}

$(Move existential quantifier in and out of substitution.  (Contributed by
       NM, 27-Sep-2003.) $)

${
	$v ph x y z  $.
	$d x y  $.
	$d x z  $.
	f0_sbex $f wff ph $.
	f1_sbex $f set x $.
	f2_sbex $f set y $.
	f3_sbex $f set z $.
	p_sbex $p |- ( [ z / y ] E. x ph <-> E. x [ z / y ] ph ) $= f0_sbex a_wn f1_sbex a_wal f2_sbex f3_sbex p_sbn f0_sbex a_wn f1_sbex f2_sbex f3_sbex p_sbal f0_sbex f2_sbex f3_sbex p_sbn f0_sbex a_wn f2_sbex f3_sbex a_wsb f0_sbex f2_sbex f3_sbex a_wsb a_wn f1_sbex p_albii f0_sbex a_wn f1_sbex a_wal f2_sbex f3_sbex a_wsb f0_sbex a_wn f2_sbex f3_sbex a_wsb f1_sbex a_wal f0_sbex f2_sbex f3_sbex a_wsb a_wn f1_sbex a_wal p_bitri f0_sbex a_wn f1_sbex a_wal a_wn f2_sbex f3_sbex a_wsb f0_sbex a_wn f1_sbex a_wal f2_sbex f3_sbex a_wsb f0_sbex f2_sbex f3_sbex a_wsb a_wn f1_sbex a_wal p_xchbinx f0_sbex f1_sbex a_df-ex f0_sbex f1_sbex a_wex f0_sbex a_wn f1_sbex a_wal a_wn f2_sbex f3_sbex p_sbbii f0_sbex f2_sbex f3_sbex a_wsb f1_sbex a_df-ex f0_sbex a_wn f1_sbex a_wal a_wn f2_sbex f3_sbex a_wsb f0_sbex f2_sbex f3_sbex a_wsb a_wn f1_sbex a_wal a_wn f0_sbex f1_sbex a_wex f2_sbex f3_sbex a_wsb f0_sbex f2_sbex f3_sbex a_wsb f1_sbex a_wex p_3bitr4i $.
$}

$(Quantify with new variable inside substitution.  (Contributed by NM,
       18-Aug-1993.) $)

${
	$v ph ps x y z  $.
	$d x z  $.
	$d y z  $.
	f0_sbalv $f wff ph $.
	f1_sbalv $f wff ps $.
	f2_sbalv $f set x $.
	f3_sbalv $f set y $.
	f4_sbalv $f set z $.
	e0_sbalv $e |- ( [ y / x ] ph <-> ps ) $.
	p_sbalv $p |- ( [ y / x ] A. z ph <-> A. z ps ) $= f0_sbalv f4_sbalv f2_sbalv f3_sbalv p_sbal e0_sbalv f0_sbalv f2_sbalv f3_sbalv a_wsb f1_sbalv f4_sbalv p_albii f0_sbalv f4_sbalv a_wal f2_sbalv f3_sbalv a_wsb f0_sbalv f2_sbalv f3_sbalv a_wsb f4_sbalv a_wal f1_sbalv f4_sbalv a_wal p_bitri $.
$}

$(An equivalent expression for existence.  (Contributed by NM,
       2-Feb-2005.) $)

${
	$v ph x y  $.
	$d x y  $.
	$d y ph  $.
	f0_exsb $f wff ph $.
	f1_exsb $f set x $.
	f2_exsb $f set y $.
	p_exsb $p |- ( E. x ph <-> E. y A. x ( x = y -> ph ) ) $= f0_exsb f2_exsb p_nfv f1_exsb a_sup_set_class f2_exsb a_sup_set_class a_wceq f0_exsb a_wi f1_exsb p_nfa1 f0_exsb f1_exsb f2_exsb p_ax11v f1_exsb a_sup_set_class f2_exsb a_sup_set_class a_wceq f0_exsb a_wi f1_exsb p_sp f1_exsb a_sup_set_class f2_exsb a_sup_set_class a_wceq f0_exsb a_wi f1_exsb a_wal f1_exsb a_sup_set_class f2_exsb a_sup_set_class a_wceq f0_exsb p_com12 f1_exsb a_sup_set_class f2_exsb a_sup_set_class a_wceq f0_exsb f1_exsb a_sup_set_class f2_exsb a_sup_set_class a_wceq f0_exsb a_wi f1_exsb a_wal p_impbid f0_exsb f1_exsb a_sup_set_class f2_exsb a_sup_set_class a_wceq f0_exsb a_wi f1_exsb a_wal f1_exsb f2_exsb p_cbvex $.
$}

$(An equivalent expression for existence.  Obsolete as of 19-Jun-2017.
       (Contributed by NM, 2-Feb-2005.)  (New usage is discouraged.) $)

${
	$v ph x y  $.
	$d x y  $.
	$d y ph  $.
	f0_exsbOLD $f wff ph $.
	f1_exsbOLD $f set x $.
	f2_exsbOLD $f set y $.
	p_exsbOLD $p |- ( E. x ph <-> E. y A. x ( x = y -> ph ) ) $= f0_exsbOLD f2_exsbOLD p_nfv f0_exsbOLD f1_exsbOLD f2_exsbOLD p_sb8e f0_exsbOLD f1_exsbOLD f2_exsbOLD p_sb6 f0_exsbOLD f1_exsbOLD f2_exsbOLD a_wsb f1_exsbOLD a_sup_set_class f2_exsbOLD a_sup_set_class a_wceq f0_exsbOLD a_wi f1_exsbOLD a_wal f2_exsbOLD p_exbii f0_exsbOLD f1_exsbOLD a_wex f0_exsbOLD f1_exsbOLD f2_exsbOLD a_wsb f2_exsbOLD a_wex f1_exsbOLD a_sup_set_class f2_exsbOLD a_sup_set_class a_wceq f0_exsbOLD a_wi f1_exsbOLD a_wal f2_exsbOLD a_wex p_bitri $.
$}

$(An equivalent expression for double existence.  (Contributed by NM,
       2-Feb-2005.) $)

${
	$v ph x y z w  $.
	$d x y z  $.
	$d y w  $.
	$d z w ph  $.
	f0_2exsb $f wff ph $.
	f1_2exsb $f set x $.
	f2_2exsb $f set y $.
	f3_2exsb $f set z $.
	f4_2exsb $f set w $.
	p_2exsb $p |- ( E. x E. y ph <-> E. z E. w A. x A. y ( ( x = z /\ y = w ) -> ph ) ) $= f0_2exsb f2_2exsb f4_2exsb p_exsb f0_2exsb f2_2exsb a_wex f2_2exsb a_sup_set_class f4_2exsb a_sup_set_class a_wceq f0_2exsb a_wi f2_2exsb a_wal f4_2exsb a_wex f1_2exsb p_exbii f2_2exsb a_sup_set_class f4_2exsb a_sup_set_class a_wceq f0_2exsb a_wi f2_2exsb a_wal f1_2exsb f4_2exsb p_excom f0_2exsb f2_2exsb a_wex f1_2exsb a_wex f2_2exsb a_sup_set_class f4_2exsb a_sup_set_class a_wceq f0_2exsb a_wi f2_2exsb a_wal f4_2exsb a_wex f1_2exsb a_wex f2_2exsb a_sup_set_class f4_2exsb a_sup_set_class a_wceq f0_2exsb a_wi f2_2exsb a_wal f1_2exsb a_wex f4_2exsb a_wex p_bitri f2_2exsb a_sup_set_class f4_2exsb a_sup_set_class a_wceq f0_2exsb a_wi f2_2exsb a_wal f1_2exsb f3_2exsb p_exsb f1_2exsb a_sup_set_class f3_2exsb a_sup_set_class a_wceq f2_2exsb a_sup_set_class f4_2exsb a_sup_set_class a_wceq f0_2exsb p_impexp f1_2exsb a_sup_set_class f3_2exsb a_sup_set_class a_wceq f2_2exsb a_sup_set_class f4_2exsb a_sup_set_class a_wceq a_wa f0_2exsb a_wi f1_2exsb a_sup_set_class f3_2exsb a_sup_set_class a_wceq f2_2exsb a_sup_set_class f4_2exsb a_sup_set_class a_wceq f0_2exsb a_wi a_wi f2_2exsb p_albii f1_2exsb a_sup_set_class f3_2exsb a_sup_set_class a_wceq f2_2exsb a_sup_set_class f4_2exsb a_sup_set_class a_wceq f0_2exsb a_wi f2_2exsb p_19.21v f1_2exsb a_sup_set_class f3_2exsb a_sup_set_class a_wceq f2_2exsb a_sup_set_class f4_2exsb a_sup_set_class a_wceq a_wa f0_2exsb a_wi f2_2exsb a_wal f1_2exsb a_sup_set_class f3_2exsb a_sup_set_class a_wceq f2_2exsb a_sup_set_class f4_2exsb a_sup_set_class a_wceq f0_2exsb a_wi a_wi f2_2exsb a_wal f1_2exsb a_sup_set_class f3_2exsb a_sup_set_class a_wceq f2_2exsb a_sup_set_class f4_2exsb a_sup_set_class a_wceq f0_2exsb a_wi f2_2exsb a_wal a_wi p_bitr2i f1_2exsb a_sup_set_class f3_2exsb a_sup_set_class a_wceq f2_2exsb a_sup_set_class f4_2exsb a_sup_set_class a_wceq f0_2exsb a_wi f2_2exsb a_wal a_wi f1_2exsb a_sup_set_class f3_2exsb a_sup_set_class a_wceq f2_2exsb a_sup_set_class f4_2exsb a_sup_set_class a_wceq a_wa f0_2exsb a_wi f2_2exsb a_wal f1_2exsb p_albii f1_2exsb a_sup_set_class f3_2exsb a_sup_set_class a_wceq f2_2exsb a_sup_set_class f4_2exsb a_sup_set_class a_wceq f0_2exsb a_wi f2_2exsb a_wal a_wi f1_2exsb a_wal f1_2exsb a_sup_set_class f3_2exsb a_sup_set_class a_wceq f2_2exsb a_sup_set_class f4_2exsb a_sup_set_class a_wceq a_wa f0_2exsb a_wi f2_2exsb a_wal f1_2exsb a_wal f3_2exsb p_exbii f2_2exsb a_sup_set_class f4_2exsb a_sup_set_class a_wceq f0_2exsb a_wi f2_2exsb a_wal f1_2exsb a_wex f1_2exsb a_sup_set_class f3_2exsb a_sup_set_class a_wceq f2_2exsb a_sup_set_class f4_2exsb a_sup_set_class a_wceq f0_2exsb a_wi f2_2exsb a_wal a_wi f1_2exsb a_wal f3_2exsb a_wex f1_2exsb a_sup_set_class f3_2exsb a_sup_set_class a_wceq f2_2exsb a_sup_set_class f4_2exsb a_sup_set_class a_wceq a_wa f0_2exsb a_wi f2_2exsb a_wal f1_2exsb a_wal f3_2exsb a_wex p_bitri f2_2exsb a_sup_set_class f4_2exsb a_sup_set_class a_wceq f0_2exsb a_wi f2_2exsb a_wal f1_2exsb a_wex f1_2exsb a_sup_set_class f3_2exsb a_sup_set_class a_wceq f2_2exsb a_sup_set_class f4_2exsb a_sup_set_class a_wceq a_wa f0_2exsb a_wi f2_2exsb a_wal f1_2exsb a_wal f3_2exsb a_wex f4_2exsb p_exbii f1_2exsb a_sup_set_class f3_2exsb a_sup_set_class a_wceq f2_2exsb a_sup_set_class f4_2exsb a_sup_set_class a_wceq a_wa f0_2exsb a_wi f2_2exsb a_wal f1_2exsb a_wal f4_2exsb f3_2exsb p_excom f2_2exsb a_sup_set_class f4_2exsb a_sup_set_class a_wceq f0_2exsb a_wi f2_2exsb a_wal f1_2exsb a_wex f4_2exsb a_wex f1_2exsb a_sup_set_class f3_2exsb a_sup_set_class a_wceq f2_2exsb a_sup_set_class f4_2exsb a_sup_set_class a_wceq a_wa f0_2exsb a_wi f2_2exsb a_wal f1_2exsb a_wal f3_2exsb a_wex f4_2exsb a_wex f1_2exsb a_sup_set_class f3_2exsb a_sup_set_class a_wceq f2_2exsb a_sup_set_class f4_2exsb a_sup_set_class a_wceq a_wa f0_2exsb a_wi f2_2exsb a_wal f1_2exsb a_wal f4_2exsb a_wex f3_2exsb a_wex p_bitri f0_2exsb f2_2exsb a_wex f1_2exsb a_wex f2_2exsb a_sup_set_class f4_2exsb a_sup_set_class a_wceq f0_2exsb a_wi f2_2exsb a_wal f1_2exsb a_wex f4_2exsb a_wex f1_2exsb a_sup_set_class f3_2exsb a_sup_set_class a_wceq f2_2exsb a_sup_set_class f4_2exsb a_sup_set_class a_wceq a_wa f0_2exsb a_wi f2_2exsb a_wal f1_2exsb a_wal f4_2exsb a_wex f3_2exsb a_wex p_bitri $.
$}

$(Version of ~ dvelim that doesn't use ~ ax-10 .  (See ~ dvelimh for a
       version that doesn't use ~ ax-11 .)  (Contributed by NM, 17-May-2008.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)

${
	$v ph ps x y z  $.
	$d z ps  $.
	$d x z  $.
	$d y z  $.
	f0_dvelimALT $f wff ph $.
	f1_dvelimALT $f wff ps $.
	f2_dvelimALT $f set x $.
	f3_dvelimALT $f set y $.
	f4_dvelimALT $f set z $.
	e0_dvelimALT $e |- ( ph -> A. x ph ) $.
	e1_dvelimALT $e |- ( z = y -> ( ph <-> ps ) ) $.
	p_dvelimALT $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $= f2_dvelimALT a_sup_set_class f3_dvelimALT a_sup_set_class a_wceq f2_dvelimALT a_wal a_wn f4_dvelimALT a_ax-17 f4_dvelimALT a_sup_set_class f3_dvelimALT a_sup_set_class a_wceq f0_dvelimALT a_wi f2_dvelimALT f4_dvelimALT p_ax16ALT f2_dvelimALT a_sup_set_class f4_dvelimALT a_sup_set_class a_wceq f2_dvelimALT a_wal f4_dvelimALT a_sup_set_class f3_dvelimALT a_sup_set_class a_wceq f0_dvelimALT a_wi f4_dvelimALT a_sup_set_class f3_dvelimALT a_sup_set_class a_wceq f0_dvelimALT a_wi f2_dvelimALT a_wal a_wi f2_dvelimALT a_sup_set_class f3_dvelimALT a_sup_set_class a_wceq f2_dvelimALT a_wal a_wn p_a1d f2_dvelimALT a_sup_set_class f4_dvelimALT a_sup_set_class a_wceq f2_dvelimALT p_hbn1 f2_dvelimALT a_sup_set_class f3_dvelimALT a_sup_set_class a_wceq f2_dvelimALT p_hbn1 f2_dvelimALT a_sup_set_class f4_dvelimALT a_sup_set_class a_wceq f2_dvelimALT a_wal a_wn f2_dvelimALT a_sup_set_class f3_dvelimALT a_sup_set_class a_wceq f2_dvelimALT a_wal a_wn f2_dvelimALT p_hban f4_dvelimALT f3_dvelimALT f2_dvelimALT p_ax12o f2_dvelimALT a_sup_set_class f4_dvelimALT a_sup_set_class a_wceq f2_dvelimALT a_wal a_wn f2_dvelimALT a_sup_set_class f3_dvelimALT a_sup_set_class a_wceq f2_dvelimALT a_wal a_wn f4_dvelimALT a_sup_set_class f3_dvelimALT a_sup_set_class a_wceq f4_dvelimALT a_sup_set_class f3_dvelimALT a_sup_set_class a_wceq f2_dvelimALT a_wal a_wi p_imp e0_dvelimALT f0_dvelimALT f0_dvelimALT f2_dvelimALT a_wal a_wi f2_dvelimALT a_sup_set_class f4_dvelimALT a_sup_set_class a_wceq f2_dvelimALT a_wal a_wn f2_dvelimALT a_sup_set_class f3_dvelimALT a_sup_set_class a_wceq f2_dvelimALT a_wal a_wn a_wa p_a1i f2_dvelimALT a_sup_set_class f4_dvelimALT a_sup_set_class a_wceq f2_dvelimALT a_wal a_wn f2_dvelimALT a_sup_set_class f3_dvelimALT a_sup_set_class a_wceq f2_dvelimALT a_wal a_wn a_wa f4_dvelimALT a_sup_set_class f3_dvelimALT a_sup_set_class a_wceq f0_dvelimALT f2_dvelimALT p_hbimd f2_dvelimALT a_sup_set_class f4_dvelimALT a_sup_set_class a_wceq f2_dvelimALT a_wal a_wn f2_dvelimALT a_sup_set_class f3_dvelimALT a_sup_set_class a_wceq f2_dvelimALT a_wal a_wn f4_dvelimALT a_sup_set_class f3_dvelimALT a_sup_set_class a_wceq f0_dvelimALT a_wi f4_dvelimALT a_sup_set_class f3_dvelimALT a_sup_set_class a_wceq f0_dvelimALT a_wi f2_dvelimALT a_wal a_wi p_ex f2_dvelimALT a_sup_set_class f4_dvelimALT a_sup_set_class a_wceq f2_dvelimALT a_wal f2_dvelimALT a_sup_set_class f3_dvelimALT a_sup_set_class a_wceq f2_dvelimALT a_wal a_wn f4_dvelimALT a_sup_set_class f3_dvelimALT a_sup_set_class a_wceq f0_dvelimALT a_wi f4_dvelimALT a_sup_set_class f3_dvelimALT a_sup_set_class a_wceq f0_dvelimALT a_wi f2_dvelimALT a_wal a_wi a_wi p_pm2.61i f2_dvelimALT a_sup_set_class f3_dvelimALT a_sup_set_class a_wceq f2_dvelimALT a_wal a_wn f4_dvelimALT a_sup_set_class f3_dvelimALT a_sup_set_class a_wceq f0_dvelimALT a_wi f2_dvelimALT f4_dvelimALT p_hbald f1_dvelimALT f4_dvelimALT a_ax-17 e1_dvelimALT f0_dvelimALT f1_dvelimALT f4_dvelimALT f3_dvelimALT p_equsalh f1_dvelimALT f4_dvelimALT a_ax-17 e1_dvelimALT f0_dvelimALT f1_dvelimALT f4_dvelimALT f3_dvelimALT p_equsalh f4_dvelimALT a_sup_set_class f3_dvelimALT a_sup_set_class a_wceq f0_dvelimALT a_wi f4_dvelimALT a_wal f1_dvelimALT f2_dvelimALT p_albii f2_dvelimALT a_sup_set_class f3_dvelimALT a_sup_set_class a_wceq f2_dvelimALT a_wal a_wn f4_dvelimALT a_sup_set_class f3_dvelimALT a_sup_set_class a_wceq f0_dvelimALT a_wi f4_dvelimALT a_wal f4_dvelimALT a_sup_set_class f3_dvelimALT a_sup_set_class a_wceq f0_dvelimALT a_wi f4_dvelimALT a_wal f2_dvelimALT a_wal f1_dvelimALT f1_dvelimALT f2_dvelimALT a_wal p_3imtr3g $.
$}

$(Move quantifier in and out of substitution.  (Contributed by NM,
       2-Jan-2002.) $)

${
	$v ph x y z  $.
	$d z y  $.
	$d z x  $.
	f0_sbal2 $f wff ph $.
	f1_sbal2 $f set x $.
	f2_sbal2 $f set y $.
	f3_sbal2 $f set z $.
	p_sbal2 $p |- ( -. A. x x = y -> ( [ z / y ] A. x ph <-> A. x [ z / y ] ph ) ) $= f2_sbal2 a_sup_set_class f3_sbal2 a_sup_set_class a_wceq f0_sbal2 a_wi f2_sbal2 f1_sbal2 p_alcom f1_sbal2 f2_sbal2 f2_sbal2 p_nfnae f1_sbal2 f2_sbal2 f1_sbal2 p_nfnae f1_sbal2 f2_sbal2 f3_sbal2 p_dveeq1 f1_sbal2 a_sup_set_class f2_sbal2 a_sup_set_class a_wceq f1_sbal2 a_wal a_wn f2_sbal2 a_sup_set_class f3_sbal2 a_sup_set_class a_wceq f1_sbal2 p_nfd f2_sbal2 a_sup_set_class f3_sbal2 a_sup_set_class a_wceq f0_sbal2 f1_sbal2 p_19.21t f1_sbal2 a_sup_set_class f2_sbal2 a_sup_set_class a_wceq f1_sbal2 a_wal a_wn f2_sbal2 a_sup_set_class f3_sbal2 a_sup_set_class a_wceq f1_sbal2 a_wnf f2_sbal2 a_sup_set_class f3_sbal2 a_sup_set_class a_wceq f0_sbal2 a_wi f1_sbal2 a_wal f2_sbal2 a_sup_set_class f3_sbal2 a_sup_set_class a_wceq f0_sbal2 f1_sbal2 a_wal a_wi a_wb p_syl f1_sbal2 a_sup_set_class f2_sbal2 a_sup_set_class a_wceq f1_sbal2 a_wal a_wn f2_sbal2 a_sup_set_class f3_sbal2 a_sup_set_class a_wceq f0_sbal2 a_wi f1_sbal2 a_wal f2_sbal2 a_sup_set_class f3_sbal2 a_sup_set_class a_wceq f0_sbal2 f1_sbal2 a_wal a_wi f2_sbal2 p_albid f2_sbal2 a_sup_set_class f3_sbal2 a_sup_set_class a_wceq f0_sbal2 a_wi f2_sbal2 a_wal f1_sbal2 a_wal f2_sbal2 a_sup_set_class f3_sbal2 a_sup_set_class a_wceq f0_sbal2 a_wi f1_sbal2 a_wal f2_sbal2 a_wal f1_sbal2 a_sup_set_class f2_sbal2 a_sup_set_class a_wceq f1_sbal2 a_wal a_wn f2_sbal2 a_sup_set_class f3_sbal2 a_sup_set_class a_wceq f0_sbal2 f1_sbal2 a_wal a_wi f2_sbal2 a_wal p_syl5rbbr f0_sbal2 f1_sbal2 a_wal f2_sbal2 f3_sbal2 p_sb6 f0_sbal2 f2_sbal2 f3_sbal2 p_sb6 f0_sbal2 f2_sbal2 f3_sbal2 a_wsb f2_sbal2 a_sup_set_class f3_sbal2 a_sup_set_class a_wceq f0_sbal2 a_wi f2_sbal2 a_wal f1_sbal2 p_albii f1_sbal2 a_sup_set_class f2_sbal2 a_sup_set_class a_wceq f1_sbal2 a_wal a_wn f2_sbal2 a_sup_set_class f3_sbal2 a_sup_set_class a_wceq f0_sbal2 f1_sbal2 a_wal a_wi f2_sbal2 a_wal f2_sbal2 a_sup_set_class f3_sbal2 a_sup_set_class a_wceq f0_sbal2 a_wi f2_sbal2 a_wal f1_sbal2 a_wal f0_sbal2 f1_sbal2 a_wal f2_sbal2 f3_sbal2 a_wsb f0_sbal2 f2_sbal2 f3_sbal2 a_wsb f1_sbal2 a_wal p_3bitr4g $.
$}


