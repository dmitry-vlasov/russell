$[ turnstile_special_source.mm $]
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Auxiliary_axiom_schemes_(4_schemes)/Axiom_scheme_ax-11_(Substitution).mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
          Axiom scheme ax-12 (Quantified Equality)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( Axiom of Quantified Equality.  One of the equality and substitution axioms
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
	$v x $.
	$v y $.
	$v z $.
	fax-12_0 $f set x $.
	fax-12_1 $f set y $.
	fax-12_2 $f set z $.
	ax-12 $a |- ( -. x = y -> ( y = z -> A. x y = z ) ) $.
$}
$( A weaker version of ~ ax-12 with distinct variable restrictions on pairs
       ` x , z ` and ` y , z ` .  In order to show that this weakening is
       adequate, this should be the only theorem referencing ~ ax-12 directly.
       (Contributed by NM, 30-Jun-2016.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$d x z $.
	$d y z $.
	fax12v_0 $f set x $.
	fax12v_1 $f set y $.
	fax12v_2 $f set z $.
	ax12v $p |- ( -. x = y -> ( y = z -> A. x y = z ) ) $= fax12v_0 fax12v_1 fax12v_2 ax-12 $.
$}
$( Lemma for ~ ax12o .  Similar to ~ equvin but with a negated equality.
       (Contributed by NM, 24-Dec-2015.) $)
${
	$v y $.
	$v z $.
	$v w $.
	$d w y $.
	$d w z $.
	fax12olem1_0 $f set y $.
	fax12olem1_1 $f set z $.
	fax12olem1_2 $f set w $.
	ax12olem1 $p |- ( E. w ( y = w /\ -. z = w ) <-> -. y = z ) $= fax12olem1_0 sup_set_class fax12olem1_2 sup_set_class wceq fax12olem1_1 sup_set_class fax12olem1_2 sup_set_class wceq wn wa fax12olem1_2 wex fax12olem1_0 sup_set_class fax12olem1_1 sup_set_class wceq wn fax12olem1_0 sup_set_class fax12olem1_2 sup_set_class wceq fax12olem1_1 sup_set_class fax12olem1_2 sup_set_class wceq wn wa fax12olem1_0 sup_set_class fax12olem1_1 sup_set_class wceq wn fax12olem1_2 fax12olem1_0 sup_set_class fax12olem1_2 sup_set_class wceq fax12olem1_0 sup_set_class fax12olem1_1 sup_set_class wceq fax12olem1_1 sup_set_class fax12olem1_2 sup_set_class wceq fax12olem1_0 sup_set_class fax12olem1_2 sup_set_class wceq fax12olem1_0 sup_set_class fax12olem1_1 sup_set_class wceq fax12olem1_2 sup_set_class fax12olem1_1 sup_set_class wceq fax12olem1_1 sup_set_class fax12olem1_2 sup_set_class wceq fax12olem1_0 fax12olem1_2 fax12olem1_1 ax-8 fax12olem1_2 fax12olem1_1 equcomi syl6 con3and exlimiv fax12olem1_0 sup_set_class fax12olem1_1 sup_set_class wceq wn fax12olem1_0 sup_set_class fax12olem1_2 sup_set_class wceq fax12olem1_1 sup_set_class fax12olem1_2 sup_set_class wceq wn wa fax12olem1_2 fax12olem1_0 fax12olem1_0 sup_set_class fax12olem1_1 sup_set_class wceq wn fax12olem1_2 ax-17 fax12olem1_2 sup_set_class fax12olem1_0 sup_set_class wceq fax12olem1_0 sup_set_class fax12olem1_1 sup_set_class wceq wn fax12olem1_1 sup_set_class fax12olem1_2 sup_set_class wceq wn fax12olem1_0 sup_set_class fax12olem1_2 sup_set_class wceq fax12olem1_2 sup_set_class fax12olem1_0 sup_set_class wceq fax12olem1_1 sup_set_class fax12olem1_2 sup_set_class wceq fax12olem1_0 sup_set_class fax12olem1_1 sup_set_class wceq fax12olem1_1 sup_set_class fax12olem1_2 sup_set_class wceq fax12olem1_2 sup_set_class fax12olem1_0 sup_set_class wceq fax12olem1_0 sup_set_class fax12olem1_1 sup_set_class wceq fax12olem1_2 sup_set_class fax12olem1_0 sup_set_class wceq fax12olem1_0 sup_set_class fax12olem1_1 sup_set_class wceq wi fax12olem1_2 fax12olem1_1 fax12olem1_2 sup_set_class fax12olem1_1 sup_set_class wceq fax12olem1_2 sup_set_class fax12olem1_0 sup_set_class wceq fax12olem1_1 sup_set_class fax12olem1_0 sup_set_class wceq fax12olem1_0 sup_set_class fax12olem1_1 sup_set_class wceq fax12olem1_2 fax12olem1_1 fax12olem1_0 ax-8 fax12olem1_1 fax12olem1_0 equcomi syl6 equcoms com12 con3d fax12olem1_2 fax12olem1_0 equcomi jctild spimeh impbii $.
$}
$( Lemma for ~ ax12o .  Negate the equalities in ~ ax-12 , shown as the
       hypothesis.  (Contributed by NM, 24-Dec-2015.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d w x z $.
	$d w y $.
	fax12olem2_0 $f set x $.
	fax12olem2_1 $f set y $.
	fax12olem2_2 $f set z $.
	fax12olem2_3 $f set w $.
	eax12olem2_0 $e |- ( -. x = y -> ( y = w -> A. x y = w ) ) $.
	ax12olem2 $p |- ( -. x = y -> ( -. y = z -> A. x -. y = z ) ) $= fax12olem2_0 sup_set_class fax12olem2_1 sup_set_class wceq wn fax12olem2_1 sup_set_class fax12olem2_3 sup_set_class wceq fax12olem2_2 sup_set_class fax12olem2_3 sup_set_class wceq wn wa fax12olem2_3 wex fax12olem2_1 sup_set_class fax12olem2_3 sup_set_class wceq fax12olem2_2 sup_set_class fax12olem2_3 sup_set_class wceq wn wa fax12olem2_3 wex fax12olem2_0 wal fax12olem2_1 sup_set_class fax12olem2_2 sup_set_class wceq wn fax12olem2_1 sup_set_class fax12olem2_2 sup_set_class wceq wn fax12olem2_0 wal fax12olem2_0 sup_set_class fax12olem2_1 sup_set_class wceq wn fax12olem2_1 sup_set_class fax12olem2_3 sup_set_class wceq fax12olem2_2 sup_set_class fax12olem2_3 sup_set_class wceq wn wa fax12olem2_3 wex fax12olem2_1 sup_set_class fax12olem2_3 sup_set_class wceq fax12olem2_2 sup_set_class fax12olem2_3 sup_set_class wceq wn wa fax12olem2_0 wal fax12olem2_3 wex fax12olem2_1 sup_set_class fax12olem2_3 sup_set_class wceq fax12olem2_2 sup_set_class fax12olem2_3 sup_set_class wceq wn wa fax12olem2_3 wex fax12olem2_0 wal fax12olem2_0 sup_set_class fax12olem2_1 sup_set_class wceq wn fax12olem2_1 sup_set_class fax12olem2_3 sup_set_class wceq fax12olem2_2 sup_set_class fax12olem2_3 sup_set_class wceq wn wa fax12olem2_1 sup_set_class fax12olem2_3 sup_set_class wceq fax12olem2_2 sup_set_class fax12olem2_3 sup_set_class wceq wn wa fax12olem2_0 wal fax12olem2_3 fax12olem2_0 sup_set_class fax12olem2_1 sup_set_class wceq wn fax12olem2_1 sup_set_class fax12olem2_3 sup_set_class wceq fax12olem2_2 sup_set_class fax12olem2_3 sup_set_class wceq wn wa fax12olem2_1 sup_set_class fax12olem2_3 sup_set_class wceq fax12olem2_0 wal fax12olem2_2 sup_set_class fax12olem2_3 sup_set_class wceq wn wa fax12olem2_1 sup_set_class fax12olem2_3 sup_set_class wceq fax12olem2_2 sup_set_class fax12olem2_3 sup_set_class wceq wn wa fax12olem2_0 wal fax12olem2_0 sup_set_class fax12olem2_1 sup_set_class wceq wn fax12olem2_1 sup_set_class fax12olem2_3 sup_set_class wceq fax12olem2_1 sup_set_class fax12olem2_3 sup_set_class wceq fax12olem2_0 wal fax12olem2_2 sup_set_class fax12olem2_3 sup_set_class wceq wn eax12olem2_0 anim1d fax12olem2_1 sup_set_class fax12olem2_3 sup_set_class wceq fax12olem2_0 wal fax12olem2_2 sup_set_class fax12olem2_3 sup_set_class wceq wn wa fax12olem2_1 sup_set_class fax12olem2_3 sup_set_class wceq fax12olem2_0 wal fax12olem2_2 sup_set_class fax12olem2_3 sup_set_class wceq wn fax12olem2_0 wal wa fax12olem2_1 sup_set_class fax12olem2_3 sup_set_class wceq fax12olem2_2 sup_set_class fax12olem2_3 sup_set_class wceq wn wa fax12olem2_0 wal fax12olem2_2 sup_set_class fax12olem2_3 sup_set_class wceq wn fax12olem2_2 sup_set_class fax12olem2_3 sup_set_class wceq wn fax12olem2_0 wal fax12olem2_1 sup_set_class fax12olem2_3 sup_set_class wceq fax12olem2_0 wal fax12olem2_2 sup_set_class fax12olem2_3 sup_set_class wceq wn fax12olem2_0 ax-17 anim2i fax12olem2_1 sup_set_class fax12olem2_3 sup_set_class wceq fax12olem2_2 sup_set_class fax12olem2_3 sup_set_class wceq wn fax12olem2_0 19.26 sylibr syl6 eximdv fax12olem2_1 sup_set_class fax12olem2_3 sup_set_class wceq fax12olem2_2 sup_set_class fax12olem2_3 sup_set_class wceq wn wa fax12olem2_3 fax12olem2_0 19.12 syl6 fax12olem2_1 fax12olem2_2 fax12olem2_3 ax12olem1 fax12olem2_1 sup_set_class fax12olem2_3 sup_set_class wceq fax12olem2_2 sup_set_class fax12olem2_3 sup_set_class wceq wn wa fax12olem2_3 wex fax12olem2_1 sup_set_class fax12olem2_2 sup_set_class wceq wn fax12olem2_0 fax12olem2_1 fax12olem2_2 fax12olem2_3 ax12olem1 albii 3imtr3g $.
$}
$( Lemma for ~ ax12o .  Show the equivalence of an intermediate equivalent to
     ~ ax12o with the conjunction of ~ ax-12 and a variant with negated
     equalities.  (Contributed by NM, 24-Dec-2015.) $)
${
	$v x $.
	$v y $.
	$v z $.
	fax12olem3_0 $f set x $.
	fax12olem3_1 $f set y $.
	fax12olem3_2 $f set z $.
	ax12olem3 $p |- ( ( -. x = y -> ( -. A. x -. y = z -> A. x y = z ) ) <-> ( ( -. x = y -> ( y = z -> A. x y = z ) ) /\ ( -. x = y -> ( -. y = z -> A. x -. y = z ) ) ) ) $= fax12olem3_0 sup_set_class fax12olem3_1 sup_set_class wceq wn fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq wn fax12olem3_0 wal wn fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq fax12olem3_0 wal wi wi fax12olem3_0 sup_set_class fax12olem3_1 sup_set_class wceq wn fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq fax12olem3_0 wal wi wi fax12olem3_0 sup_set_class fax12olem3_1 sup_set_class wceq wn fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq wn fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq wn fax12olem3_0 wal wi wi wa fax12olem3_0 sup_set_class fax12olem3_1 sup_set_class wceq wn fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq wn fax12olem3_0 wal wn fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq fax12olem3_0 wal wi wi fax12olem3_0 sup_set_class fax12olem3_1 sup_set_class wceq wn fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq fax12olem3_0 wal wi wi fax12olem3_0 sup_set_class fax12olem3_1 sup_set_class wceq wn fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq wn fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq wn fax12olem3_0 wal wi wi fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq wn fax12olem3_0 wal wn fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq fax12olem3_0 wal wi fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq fax12olem3_0 wal wi fax12olem3_0 sup_set_class fax12olem3_1 sup_set_class wceq wn fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq wn fax12olem3_0 wal wn fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq fax12olem3_0 wal fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq wn fax12olem3_0 wal fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq wn fax12olem3_0 sp con2i imim1i imim2i fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq wn fax12olem3_0 wal wn fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq fax12olem3_0 wal wi fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq wn fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq wn fax12olem3_0 wal wi fax12olem3_0 sup_set_class fax12olem3_1 sup_set_class wceq wn fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq wn fax12olem3_0 wal wn fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq fax12olem3_0 wal wi fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq wn fax12olem3_0 wal fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq fax12olem3_0 wal fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq wn fax12olem3_0 wal wn fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq fax12olem3_0 sp imim2i con1d imim2i jca fax12olem3_0 sup_set_class fax12olem3_1 sup_set_class wceq wn fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq fax12olem3_0 wal wi wi fax12olem3_0 sup_set_class fax12olem3_1 sup_set_class wceq wn fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq wn fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq wn fax12olem3_0 wal wi wi fax12olem3_0 sup_set_class fax12olem3_1 sup_set_class wceq wn fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq wn fax12olem3_0 wal wn fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq fax12olem3_0 wal wi wi fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq fax12olem3_0 wal wi fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq wn fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq wn fax12olem3_0 wal wi fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq wn fax12olem3_0 wal wn fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq fax12olem3_0 wal wi fax12olem3_0 sup_set_class fax12olem3_1 sup_set_class wceq wn fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq wn fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq wn fax12olem3_0 wal wi fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq fax12olem3_0 wal wi fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq wn fax12olem3_0 wal wn fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq fax12olem3_0 wal wi fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq wn fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq wn fax12olem3_0 wal wi fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq wn fax12olem3_0 wal wn fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq fax12olem3_0 wal fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq fax12olem3_1 sup_set_class fax12olem3_2 sup_set_class wceq wn fax12olem3_0 wal con1 imim1d com12 imim3i imp impbii $.
$}
$( Lemma for ~ ax12o .  Construct an intermediate equivalent to ~ ax-12
       from two instances of ~ ax-12 .  (Contributed by NM, 24-Dec-2015.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d w x z $.
	$d w y z $.
	fax12olem4_0 $f set x $.
	fax12olem4_1 $f set y $.
	fax12olem4_2 $f set z $.
	fax12olem4_3 $f set w $.
	eax12olem4_0 $e |- ( -. x = y -> ( y = z -> A. x y = z ) ) $.
	eax12olem4_1 $e |- ( -. x = y -> ( y = w -> A. x y = w ) ) $.
	ax12olem4 $p |- ( -. x = y -> ( -. A. x -. y = z -> A. x y = z ) ) $= fax12olem4_0 sup_set_class fax12olem4_1 sup_set_class wceq wn fax12olem4_1 sup_set_class fax12olem4_2 sup_set_class wceq wn fax12olem4_0 wal wn fax12olem4_1 sup_set_class fax12olem4_2 sup_set_class wceq fax12olem4_0 wal wi wi fax12olem4_0 sup_set_class fax12olem4_1 sup_set_class wceq wn fax12olem4_1 sup_set_class fax12olem4_2 sup_set_class wceq fax12olem4_1 sup_set_class fax12olem4_2 sup_set_class wceq fax12olem4_0 wal wi wi fax12olem4_0 sup_set_class fax12olem4_1 sup_set_class wceq wn fax12olem4_1 sup_set_class fax12olem4_2 sup_set_class wceq wn fax12olem4_1 sup_set_class fax12olem4_2 sup_set_class wceq wn fax12olem4_0 wal wi wi eax12olem4_0 fax12olem4_0 fax12olem4_1 fax12olem4_2 fax12olem4_3 eax12olem4_1 ax12olem2 fax12olem4_0 fax12olem4_1 fax12olem4_2 ax12olem3 mpbir2an $.
$}
$( Lemma for ~ ax12o .  See ~ ax12olem6 for derivation of ~ ax12o from the
       conclusion.  (Contributed by NM, 24-Dec-2015.) $)
${
	$v x $.
	$v y $.
	$v z $.
	fax12olem5_0 $f set x $.
	fax12olem5_1 $f set y $.
	fax12olem5_2 $f set z $.
	eax12olem5_0 $e |- ( -. x = y -> ( -. A. x -. y = z -> A. x y = z ) ) $.
	ax12olem5 $p |- ( -. A. x x = y -> ( y = z -> A. x y = z ) ) $= fax12olem5_0 sup_set_class fax12olem5_1 sup_set_class wceq fax12olem5_0 wal wn fax12olem5_0 sup_set_class fax12olem5_1 sup_set_class wceq wn fax12olem5_0 wex fax12olem5_1 sup_set_class fax12olem5_2 sup_set_class wceq fax12olem5_1 sup_set_class fax12olem5_2 sup_set_class wceq fax12olem5_0 wal wi fax12olem5_0 sup_set_class fax12olem5_1 sup_set_class wceq fax12olem5_0 exnal fax12olem5_1 sup_set_class fax12olem5_2 sup_set_class wceq fax12olem5_1 sup_set_class fax12olem5_2 sup_set_class wceq fax12olem5_0 wex fax12olem5_0 sup_set_class fax12olem5_1 sup_set_class wceq wn fax12olem5_0 wex fax12olem5_1 sup_set_class fax12olem5_2 sup_set_class wceq fax12olem5_0 wal fax12olem5_1 sup_set_class fax12olem5_2 sup_set_class wceq fax12olem5_0 19.8a fax12olem5_0 sup_set_class fax12olem5_1 sup_set_class wceq wn fax12olem5_1 sup_set_class fax12olem5_2 sup_set_class wceq fax12olem5_0 wex fax12olem5_1 sup_set_class fax12olem5_2 sup_set_class wceq fax12olem5_0 wal wi fax12olem5_0 fax12olem5_1 sup_set_class fax12olem5_2 sup_set_class wceq fax12olem5_0 wex fax12olem5_1 sup_set_class fax12olem5_2 sup_set_class wceq fax12olem5_0 wal fax12olem5_0 fax12olem5_1 sup_set_class fax12olem5_2 sup_set_class wceq fax12olem5_0 hbe1 fax12olem5_1 sup_set_class fax12olem5_2 sup_set_class wceq fax12olem5_0 hba1 hbim fax12olem5_1 sup_set_class fax12olem5_2 sup_set_class wceq fax12olem5_0 wex fax12olem5_1 sup_set_class fax12olem5_2 sup_set_class wceq wn fax12olem5_0 wal wn fax12olem5_0 sup_set_class fax12olem5_1 sup_set_class wceq wn fax12olem5_1 sup_set_class fax12olem5_2 sup_set_class wceq fax12olem5_0 wal fax12olem5_1 sup_set_class fax12olem5_2 sup_set_class wceq fax12olem5_0 df-ex eax12olem5_0 syl5bi exlimih syl5 sylbir $.
$}
$( Lemma for ~ ax12o .  Derivation of ~ ax12o from the hypotheses, without
       using ~ ax12o .  (Contributed by Andrew Salmon, 21-Jul-2011.)  (Revised
       by NM, 24-Dec-2015.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d w x $.
	$d w y $.
	$d w z $.
	fax12olem6_0 $f set x $.
	fax12olem6_1 $f set y $.
	fax12olem6_2 $f set z $.
	fax12olem6_3 $f set w $.
	eax12olem6_0 $e |- ( -. A. x x = z -> ( z = w -> A. x z = w ) ) $.
	eax12olem6_1 $e |- ( -. A. x x = y -> ( y = w -> A. x y = w ) ) $.
	ax12olem6 $p |- ( -. A. x x = y -> ( -. A. x x = z -> ( y = z -> A. x y = z ) ) ) $= fax12olem6_0 sup_set_class fax12olem6_1 sup_set_class wceq fax12olem6_0 wal wn fax12olem6_0 sup_set_class fax12olem6_2 sup_set_class wceq fax12olem6_0 wal wn fax12olem6_1 sup_set_class fax12olem6_2 sup_set_class wceq fax12olem6_1 sup_set_class fax12olem6_2 sup_set_class wceq fax12olem6_0 wal fax12olem6_0 sup_set_class fax12olem6_1 sup_set_class wceq fax12olem6_0 wal wn fax12olem6_0 sup_set_class fax12olem6_2 sup_set_class wceq fax12olem6_0 wal wn fax12olem6_1 sup_set_class fax12olem6_2 sup_set_class wceq wi fax12olem6_0 sup_set_class fax12olem6_2 sup_set_class wceq fax12olem6_0 wal wn fax12olem6_1 sup_set_class fax12olem6_2 sup_set_class wceq wi fax12olem6_0 wal fax12olem6_0 sup_set_class fax12olem6_2 sup_set_class wceq fax12olem6_0 wal wn fax12olem6_1 sup_set_class fax12olem6_2 sup_set_class wceq fax12olem6_0 wal wi fax12olem6_0 sup_set_class fax12olem6_2 sup_set_class wceq fax12olem6_0 wal wn fax12olem6_2 sup_set_class fax12olem6_3 sup_set_class wceq wi fax12olem6_0 sup_set_class fax12olem6_2 sup_set_class wceq fax12olem6_0 wal wn fax12olem6_1 sup_set_class fax12olem6_2 sup_set_class wceq wi fax12olem6_0 fax12olem6_1 fax12olem6_3 fax12olem6_0 sup_set_class fax12olem6_2 sup_set_class wceq fax12olem6_0 wal wn fax12olem6_2 sup_set_class fax12olem6_3 sup_set_class wceq fax12olem6_0 fax12olem6_0 sup_set_class fax12olem6_2 sup_set_class wceq fax12olem6_0 hbn1 eax12olem6_0 hbim1 fax12olem6_0 sup_set_class fax12olem6_2 sup_set_class wceq fax12olem6_0 wal wn fax12olem6_1 sup_set_class fax12olem6_2 sup_set_class wceq wi fax12olem6_3 ax-17 fax12olem6_3 sup_set_class fax12olem6_1 sup_set_class wceq fax12olem6_2 sup_set_class fax12olem6_3 sup_set_class wceq fax12olem6_1 sup_set_class fax12olem6_2 sup_set_class wceq fax12olem6_0 sup_set_class fax12olem6_2 sup_set_class wceq fax12olem6_0 wal wn fax12olem6_2 sup_set_class fax12olem6_3 sup_set_class wceq fax12olem6_3 sup_set_class fax12olem6_2 sup_set_class wceq fax12olem6_3 sup_set_class fax12olem6_1 sup_set_class wceq fax12olem6_1 sup_set_class fax12olem6_2 sup_set_class wceq fax12olem6_2 fax12olem6_3 equcom fax12olem6_3 fax12olem6_1 fax12olem6_2 equequ1 syl5bb imbi2d eax12olem6_1 dvelimhw fax12olem6_0 sup_set_class fax12olem6_2 sup_set_class wceq fax12olem6_0 wal wn fax12olem6_1 sup_set_class fax12olem6_2 sup_set_class wceq fax12olem6_0 fax12olem6_0 sup_set_class fax12olem6_2 sup_set_class wceq fax12olem6_0 hbn1 19.21h syl6ib pm2.86d $.
$}
$( Lemma for ~ ax12o .  Derivation of ~ ax12o from the hypotheses, without
       using ~ ax12o .  (Contributed by NM, 24-Dec-2015.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d w x $.
	$d w y $.
	$d w z $.
	fax12olem7_0 $f set x $.
	fax12olem7_1 $f set y $.
	fax12olem7_2 $f set z $.
	fax12olem7_3 $f set w $.
	eax12olem7_0 $e |- ( -. x = z -> ( -. A. x -. z = w -> A. x z = w ) ) $.
	eax12olem7_1 $e |- ( -. x = y -> ( -. A. x -. y = w -> A. x y = w ) ) $.
	ax12olem7 $p |- ( -. A. x x = y -> ( -. A. x x = z -> ( y = z -> A. x y = z ) ) ) $= fax12olem7_0 fax12olem7_1 fax12olem7_2 fax12olem7_3 fax12olem7_0 fax12olem7_2 fax12olem7_3 eax12olem7_0 ax12olem5 fax12olem7_0 fax12olem7_1 fax12olem7_3 eax12olem7_1 ax12olem5 ax12olem6 $.
$}
$( Derive set.mm's original ~ ax-12o from the shorter ~ ax-12 .
       (Contributed by NM, 29-Nov-2015.)  (Revised by NM, 24-Dec-2015.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$v v $.
	$d x w v $.
	$d y w v $.
	$d z w v $.
	iax12o_0 $f set w $.
	iax12o_1 $f set v $.
	fax12o_0 $f set x $.
	fax12o_1 $f set y $.
	fax12o_2 $f set z $.
	ax12o $p |- ( -. A. z z = x -> ( -. A. z z = y -> ( x = y -> A. z x = y ) ) ) $= fax12o_2 fax12o_0 fax12o_1 iax12o_0 fax12o_2 fax12o_1 iax12o_0 iax12o_1 fax12o_2 fax12o_1 iax12o_0 ax12v fax12o_2 fax12o_1 iax12o_1 ax12v ax12olem4 fax12o_2 fax12o_0 iax12o_0 iax12o_1 fax12o_2 fax12o_0 iax12o_0 ax12v fax12o_2 fax12o_0 iax12o_1 ax12v ax12olem4 ax12olem7 $.
$}
$( Lemma for ~ ax10 .  Change bound variable.  (Contributed by NM,
       22-Jul-2015.) $)
${
	$v x $.
	$v y $.
	$v w $.
	$v v $.
	$d x v w $.
	$d y v w $.
	iax10lem1_0 $f set v $.
	fax10lem1_0 $f set x $.
	fax10lem1_1 $f set y $.
	fax10lem1_2 $f set w $.
	ax10lem1 $p |- ( A. x x = w -> A. y y = w ) $= fax10lem1_0 sup_set_class fax10lem1_2 sup_set_class wceq fax10lem1_0 wal iax10lem1_0 sup_set_class fax10lem1_2 sup_set_class wceq iax10lem1_0 wal fax10lem1_1 sup_set_class fax10lem1_2 sup_set_class wceq fax10lem1_1 wal fax10lem1_0 sup_set_class fax10lem1_2 sup_set_class wceq iax10lem1_0 sup_set_class fax10lem1_2 sup_set_class wceq fax10lem1_0 iax10lem1_0 fax10lem1_0 iax10lem1_0 fax10lem1_2 ax-8 cbvalivw iax10lem1_0 sup_set_class fax10lem1_2 sup_set_class wceq fax10lem1_1 sup_set_class fax10lem1_2 sup_set_class wceq iax10lem1_0 fax10lem1_1 iax10lem1_0 fax10lem1_1 fax10lem1_2 ax-8 cbvalivw syl $.
$}
$( Lemma for ~ ax10 .  Change free variable.  (Contributed by NM,
       25-Jul-2015.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$d x y $.
	$d x z $.
	fax10lem2_0 $f set x $.
	fax10lem2_1 $f set y $.
	fax10lem2_2 $f set z $.
	ax10lem2 $p |- ( A. x x = y -> A. x x = z ) $= fax10lem2_0 sup_set_class fax10lem2_2 sup_set_class wceq fax10lem2_0 wal fax10lem2_0 sup_set_class fax10lem2_1 sup_set_class wceq fax10lem2_0 wal fax10lem2_0 sup_set_class fax10lem2_2 sup_set_class wceq wn fax10lem2_0 wex fax10lem2_0 sup_set_class fax10lem2_1 sup_set_class wceq wn fax10lem2_0 wex fax10lem2_0 sup_set_class fax10lem2_2 sup_set_class wceq fax10lem2_0 wal wn fax10lem2_0 sup_set_class fax10lem2_1 sup_set_class wceq fax10lem2_0 wal wn fax10lem2_0 sup_set_class fax10lem2_2 sup_set_class wceq wn fax10lem2_0 sup_set_class fax10lem2_1 sup_set_class wceq wn fax10lem2_0 wex fax10lem2_0 fax10lem2_0 sup_set_class fax10lem2_1 sup_set_class wceq wn fax10lem2_0 hbe1 fax10lem2_0 sup_set_class fax10lem2_2 sup_set_class wceq wn fax10lem2_2 sup_set_class fax10lem2_1 sup_set_class wceq fax10lem2_0 sup_set_class fax10lem2_1 sup_set_class wceq wn fax10lem2_0 wex fax10lem2_0 sup_set_class fax10lem2_2 sup_set_class wceq wn fax10lem2_2 sup_set_class fax10lem2_1 sup_set_class wceq fax10lem2_0 sup_set_class fax10lem2_1 sup_set_class wceq wn fax10lem2_0 sup_set_class fax10lem2_1 sup_set_class wceq wn fax10lem2_0 wex fax10lem2_2 sup_set_class fax10lem2_1 sup_set_class wceq fax10lem2_0 sup_set_class fax10lem2_1 sup_set_class wceq fax10lem2_0 sup_set_class fax10lem2_2 sup_set_class wceq fax10lem2_2 sup_set_class fax10lem2_1 sup_set_class wceq fax10lem2_0 sup_set_class fax10lem2_2 sup_set_class wceq fax10lem2_0 sup_set_class fax10lem2_1 sup_set_class wceq fax10lem2_2 fax10lem2_1 fax10lem2_0 equequ2 biimprd con3rr3 fax10lem2_0 sup_set_class fax10lem2_1 sup_set_class wceq wn fax10lem2_0 19.8a syl6 fax10lem2_2 sup_set_class fax10lem2_1 sup_set_class wceq wn fax10lem2_0 sup_set_class fax10lem2_1 sup_set_class wceq wn fax10lem2_0 fax10lem2_2 fax10lem2_2 sup_set_class fax10lem2_1 sup_set_class wceq wn fax10lem2_0 ax-17 fax10lem2_0 sup_set_class fax10lem2_2 sup_set_class wceq fax10lem2_0 sup_set_class fax10lem2_1 sup_set_class wceq wn fax10lem2_2 sup_set_class fax10lem2_1 sup_set_class wceq wn fax10lem2_0 sup_set_class fax10lem2_2 sup_set_class wceq fax10lem2_0 sup_set_class fax10lem2_1 sup_set_class wceq fax10lem2_2 sup_set_class fax10lem2_1 sup_set_class wceq fax10lem2_0 fax10lem2_2 fax10lem2_1 equequ1 notbid biimprd spimeh pm2.61d1 exlimih fax10lem2_0 sup_set_class fax10lem2_2 sup_set_class wceq fax10lem2_0 exnal fax10lem2_0 sup_set_class fax10lem2_1 sup_set_class wceq fax10lem2_0 exnal 3imtr3i con4i $.
$}
$( Lemma for ~ ax10 .  Similar to ~ ax-10 but with distinct variables.
       (Contributed by NM, 25-Jul-2015.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d w x y $.
	$d w x z $.
	iax10lem3_0 $f set z $.
	iax10lem3_1 $f set w $.
	fax10lem3_0 $f set x $.
	fax10lem3_1 $f set y $.
	ax10lem3 $p |- ( A. x x = y -> A. y y = x ) $= fax10lem3_0 sup_set_class fax10lem3_1 sup_set_class wceq fax10lem3_0 wal fax10lem3_0 sup_set_class iax10lem3_0 sup_set_class wceq fax10lem3_0 wal fax10lem3_1 sup_set_class fax10lem3_0 sup_set_class wceq fax10lem3_1 wal fax10lem3_0 fax10lem3_1 iax10lem3_0 ax10lem2 fax10lem3_0 sup_set_class iax10lem3_0 sup_set_class wceq fax10lem3_0 wal iax10lem3_1 sup_set_class fax10lem3_0 sup_set_class wceq iax10lem3_1 wal fax10lem3_1 sup_set_class fax10lem3_0 sup_set_class wceq fax10lem3_1 wal fax10lem3_0 sup_set_class iax10lem3_0 sup_set_class wceq fax10lem3_0 wal iax10lem3_1 sup_set_class iax10lem3_0 sup_set_class wceq iax10lem3_1 wal iax10lem3_1 sup_set_class fax10lem3_0 sup_set_class wceq iax10lem3_1 wal fax10lem3_0 iax10lem3_1 iax10lem3_0 ax10lem1 iax10lem3_1 iax10lem3_0 fax10lem3_0 ax10lem2 syl iax10lem3_1 fax10lem3_1 fax10lem3_0 ax10lem1 syl syl $.
$}
$( Similar to ~ dvelim with first hypothesis replaced by distinct variable
       condition.  (Contributed by NM, 25-Jul-2015.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v z $.
	$d x z $.
	$d y z $.
	$d z ps $.
	$d x ph $.
	fdvelimv_0 $f wff ph $.
	fdvelimv_1 $f wff ps $.
	fdvelimv_2 $f set x $.
	fdvelimv_3 $f set y $.
	fdvelimv_4 $f set z $.
	edvelimv_0 $e |- ( z = y -> ( ph <-> ps ) ) $.
	dvelimv $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $= fdvelimv_2 sup_set_class fdvelimv_3 sup_set_class wceq fdvelimv_2 wal wn fdvelimv_2 sup_set_class fdvelimv_4 sup_set_class wceq fdvelimv_2 wal fdvelimv_1 fdvelimv_1 fdvelimv_2 wal wi fdvelimv_2 sup_set_class fdvelimv_4 sup_set_class wceq fdvelimv_2 wal wn fdvelimv_2 sup_set_class fdvelimv_3 sup_set_class wceq fdvelimv_2 wal wn fdvelimv_1 fdvelimv_1 fdvelimv_2 wal wi fdvelimv_1 fdvelimv_4 sup_set_class fdvelimv_3 sup_set_class wceq fdvelimv_0 wi fdvelimv_4 wal fdvelimv_2 sup_set_class fdvelimv_4 sup_set_class wceq fdvelimv_2 wal wn fdvelimv_2 sup_set_class fdvelimv_3 sup_set_class wceq fdvelimv_2 wal wn wa fdvelimv_4 sup_set_class fdvelimv_3 sup_set_class wceq fdvelimv_0 wi fdvelimv_4 wal fdvelimv_2 wal fdvelimv_1 fdvelimv_2 wal fdvelimv_1 fdvelimv_4 sup_set_class fdvelimv_3 sup_set_class wceq fdvelimv_1 fdvelimv_4 wal wi fdvelimv_4 wal fdvelimv_4 sup_set_class fdvelimv_3 sup_set_class wceq fdvelimv_0 wi fdvelimv_4 wal fdvelimv_1 fdvelimv_4 sup_set_class fdvelimv_3 sup_set_class wceq fdvelimv_1 fdvelimv_4 wal wi fdvelimv_4 fdvelimv_1 fdvelimv_4 ax-17 fdvelimv_1 fdvelimv_1 fdvelimv_4 wal fdvelimv_4 sup_set_class fdvelimv_3 sup_set_class wceq fdvelimv_1 fdvelimv_4 ax-17 a1d alrimih fdvelimv_4 sup_set_class fdvelimv_3 sup_set_class wceq fdvelimv_1 fdvelimv_4 wal wi fdvelimv_4 sup_set_class fdvelimv_3 sup_set_class wceq fdvelimv_0 wi fdvelimv_4 fdvelimv_4 sup_set_class fdvelimv_3 sup_set_class wceq fdvelimv_1 fdvelimv_4 wal fdvelimv_0 fdvelimv_1 fdvelimv_4 wal fdvelimv_0 fdvelimv_4 sup_set_class fdvelimv_3 sup_set_class wceq fdvelimv_1 fdvelimv_1 fdvelimv_4 sp edvelimv_0 syl5ibr a2i alimi syl fdvelimv_2 sup_set_class fdvelimv_4 sup_set_class wceq fdvelimv_2 wal wn fdvelimv_2 sup_set_class fdvelimv_3 sup_set_class wceq fdvelimv_2 wal wn wa fdvelimv_4 sup_set_class fdvelimv_3 sup_set_class wceq fdvelimv_0 wi fdvelimv_2 fdvelimv_4 fdvelimv_2 sup_set_class fdvelimv_4 sup_set_class wceq fdvelimv_2 wal wn fdvelimv_2 sup_set_class fdvelimv_3 sup_set_class wceq fdvelimv_2 wal wn fdvelimv_4 fdvelimv_2 sup_set_class fdvelimv_4 sup_set_class wceq fdvelimv_2 wal wn fdvelimv_4 sup_set_class fdvelimv_2 sup_set_class wceq fdvelimv_4 wal wn fdvelimv_2 sup_set_class fdvelimv_4 sup_set_class wceq fdvelimv_2 wal wn fdvelimv_4 wal fdvelimv_4 sup_set_class fdvelimv_2 sup_set_class wceq fdvelimv_4 wal fdvelimv_2 sup_set_class fdvelimv_4 sup_set_class wceq fdvelimv_2 wal fdvelimv_4 fdvelimv_2 ax10lem3 con3i fdvelimv_4 sup_set_class fdvelimv_2 sup_set_class wceq fdvelimv_4 wal wn fdvelimv_2 sup_set_class fdvelimv_4 sup_set_class wceq fdvelimv_2 wal wn fdvelimv_4 fdvelimv_4 sup_set_class fdvelimv_2 sup_set_class wceq fdvelimv_4 hbn1 fdvelimv_2 sup_set_class fdvelimv_4 sup_set_class wceq fdvelimv_2 wal fdvelimv_4 sup_set_class fdvelimv_2 sup_set_class wceq fdvelimv_4 wal fdvelimv_2 fdvelimv_4 ax10lem3 con3i alrimih syl fdvelimv_2 sup_set_class fdvelimv_3 sup_set_class wceq fdvelimv_2 wal wn fdvelimv_4 ax-17 hban fdvelimv_2 sup_set_class fdvelimv_4 sup_set_class wceq fdvelimv_2 wal wn fdvelimv_2 sup_set_class fdvelimv_3 sup_set_class wceq fdvelimv_2 wal wn wa fdvelimv_4 sup_set_class fdvelimv_3 sup_set_class wceq fdvelimv_0 fdvelimv_2 fdvelimv_2 sup_set_class fdvelimv_4 sup_set_class wceq fdvelimv_2 wal wn fdvelimv_2 sup_set_class fdvelimv_3 sup_set_class wceq fdvelimv_2 wal wn fdvelimv_2 fdvelimv_2 sup_set_class fdvelimv_4 sup_set_class wceq fdvelimv_2 hbn1 fdvelimv_2 sup_set_class fdvelimv_3 sup_set_class wceq fdvelimv_2 hbn1 hban fdvelimv_2 sup_set_class fdvelimv_4 sup_set_class wceq fdvelimv_2 wal wn fdvelimv_2 sup_set_class fdvelimv_3 sup_set_class wceq fdvelimv_2 wal wn fdvelimv_4 sup_set_class fdvelimv_3 sup_set_class wceq fdvelimv_4 sup_set_class fdvelimv_3 sup_set_class wceq fdvelimv_2 wal wi fdvelimv_4 fdvelimv_3 fdvelimv_2 ax12o imp fdvelimv_2 sup_set_class fdvelimv_4 sup_set_class wceq fdvelimv_2 wal wn fdvelimv_2 sup_set_class fdvelimv_3 sup_set_class wceq fdvelimv_2 wal wn wa fdvelimv_0 fdvelimv_2 a17d hbimd hbald fdvelimv_4 sup_set_class fdvelimv_3 sup_set_class wceq fdvelimv_0 wi fdvelimv_4 wal fdvelimv_1 fdvelimv_2 fdvelimv_4 sup_set_class fdvelimv_3 sup_set_class wceq fdvelimv_0 wi fdvelimv_4 wal fdvelimv_1 wn fdvelimv_4 wal fdvelimv_1 fdvelimv_4 sup_set_class fdvelimv_3 sup_set_class wceq fdvelimv_0 wi fdvelimv_4 wal fdvelimv_4 sup_set_class fdvelimv_3 sup_set_class wceq fdvelimv_1 wi fdvelimv_4 wal fdvelimv_1 wn fdvelimv_4 wal wn fdvelimv_4 sup_set_class fdvelimv_3 sup_set_class wceq fdvelimv_0 wi fdvelimv_4 sup_set_class fdvelimv_3 sup_set_class wceq fdvelimv_1 wi fdvelimv_4 fdvelimv_4 sup_set_class fdvelimv_3 sup_set_class wceq fdvelimv_0 fdvelimv_1 fdvelimv_4 sup_set_class fdvelimv_3 sup_set_class wceq fdvelimv_0 fdvelimv_1 edvelimv_0 biimpd a2i alimi fdvelimv_4 sup_set_class fdvelimv_3 sup_set_class wceq fdvelimv_1 wi fdvelimv_4 wal fdvelimv_1 wn fdvelimv_4 wal fdvelimv_4 sup_set_class fdvelimv_3 sup_set_class wceq wn fdvelimv_4 wal fdvelimv_4 fdvelimv_3 ax9v fdvelimv_4 sup_set_class fdvelimv_3 sup_set_class wceq fdvelimv_1 wi fdvelimv_1 wn fdvelimv_4 sup_set_class fdvelimv_3 sup_set_class wceq wn fdvelimv_4 fdvelimv_4 sup_set_class fdvelimv_3 sup_set_class wceq fdvelimv_1 con3 al2imi mtoi syl fdvelimv_1 wn fdvelimv_4 ax-17 nsyl2 alimi syl56 expcom fdvelimv_2 sup_set_class fdvelimv_4 sup_set_class wceq fdvelimv_2 wal fdvelimv_1 fdvelimv_2 sup_set_class fdvelimv_4 sup_set_class wceq fdvelimv_1 wi fdvelimv_2 wal fdvelimv_1 fdvelimv_2 wal fdvelimv_2 sup_set_class fdvelimv_4 sup_set_class wceq fdvelimv_2 wal fdvelimv_2 sup_set_class fdvelimv_4 sup_set_class wceq fdvelimv_1 fdvelimv_1 fdvelimv_4 wal fdvelimv_2 sup_set_class fdvelimv_4 sup_set_class wceq fdvelimv_1 wi fdvelimv_2 wal fdvelimv_2 sup_set_class fdvelimv_4 sup_set_class wceq fdvelimv_2 sp fdvelimv_1 fdvelimv_4 ax-17 fdvelimv_1 fdvelimv_2 fdvelimv_4 ax-11 syl2im fdvelimv_2 sup_set_class fdvelimv_4 sup_set_class wceq fdvelimv_2 sup_set_class fdvelimv_4 sup_set_class wceq fdvelimv_1 wi fdvelimv_1 fdvelimv_2 fdvelimv_2 sup_set_class fdvelimv_4 sup_set_class wceq fdvelimv_1 pm2.27 al2imi syld pm2.61d2 $.
$}
$( Quantifier introduction when one pair of variables is distinct.
       (Contributed by NM, 2-Jan-2002.)  (Revised by NM, 20-Jul-2015.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d w z x $.
	$d w y $.
	idveeq2_0 $f set w $.
	fdveeq2_0 $f set x $.
	fdveeq2_1 $f set y $.
	fdveeq2_2 $f set z $.
	dveeq2 $p |- ( -. A. x x = y -> ( z = y -> A. x z = y ) ) $= fdveeq2_2 sup_set_class idveeq2_0 sup_set_class wceq fdveeq2_2 sup_set_class fdveeq2_1 sup_set_class wceq fdveeq2_0 fdveeq2_1 idveeq2_0 idveeq2_0 fdveeq2_1 fdveeq2_2 equequ2 dvelimv $.
$}
$( Lemma for ~ ax10 .  Change bound variable.  (Contributed by NM,
       8-Jul-2016.) $)
${
	$v x $.
	$v y $.
	$v w $.
	$v z $.
	$d w z x $.
	$d w z y $.
	iax10lem4_0 $f set z $.
	fax10lem4_0 $f set x $.
	fax10lem4_1 $f set y $.
	fax10lem4_2 $f set w $.
	ax10lem4 $p |- ( A. x x = w -> A. y y = x ) $= fax10lem4_0 sup_set_class fax10lem4_2 sup_set_class wceq fax10lem4_0 wal fax10lem4_1 sup_set_class fax10lem4_0 sup_set_class wceq fax10lem4_1 wal fax10lem4_1 sup_set_class fax10lem4_0 sup_set_class wceq fax10lem4_1 wal wn fax10lem4_0 sup_set_class fax10lem4_2 sup_set_class wceq fax10lem4_0 wal fax10lem4_1 sup_set_class fax10lem4_0 sup_set_class wceq fax10lem4_1 wal fax10lem4_1 sup_set_class fax10lem4_0 sup_set_class wceq fax10lem4_1 wal wn fax10lem4_0 sup_set_class fax10lem4_2 sup_set_class wceq fax10lem4_0 wal fax10lem4_1 sup_set_class fax10lem4_0 sup_set_class wceq fax10lem4_1 wal fax10lem4_1 sup_set_class fax10lem4_0 sup_set_class wceq fax10lem4_1 wal wn fax10lem4_0 sup_set_class fax10lem4_2 sup_set_class wceq fax10lem4_0 sup_set_class fax10lem4_2 sup_set_class wceq fax10lem4_0 wal fax10lem4_1 sup_set_class fax10lem4_0 sup_set_class wceq fax10lem4_1 wal wi fax10lem4_0 fax10lem4_0 sup_set_class fax10lem4_2 sup_set_class wceq fax10lem4_0 wal fax10lem4_1 sup_set_class fax10lem4_2 sup_set_class wceq fax10lem4_1 wal fax10lem4_1 sup_set_class fax10lem4_0 sup_set_class wceq fax10lem4_1 wal wn fax10lem4_0 sup_set_class fax10lem4_2 sup_set_class wceq fax10lem4_1 sup_set_class fax10lem4_0 sup_set_class wceq fax10lem4_1 wal fax10lem4_0 fax10lem4_1 fax10lem4_2 ax10lem1 fax10lem4_1 sup_set_class fax10lem4_0 sup_set_class wceq fax10lem4_1 wal wn fax10lem4_0 sup_set_class fax10lem4_2 sup_set_class wceq fax10lem4_0 sup_set_class fax10lem4_2 sup_set_class wceq fax10lem4_1 wal fax10lem4_1 sup_set_class fax10lem4_2 sup_set_class wceq fax10lem4_1 wal fax10lem4_1 sup_set_class fax10lem4_0 sup_set_class wceq fax10lem4_1 wal wi iax10lem4_0 sup_set_class fax10lem4_2 sup_set_class wceq fax10lem4_0 sup_set_class fax10lem4_2 sup_set_class wceq fax10lem4_1 fax10lem4_0 iax10lem4_0 iax10lem4_0 fax10lem4_0 fax10lem4_2 equequ1 dvelimv fax10lem4_0 sup_set_class fax10lem4_2 sup_set_class wceq fax10lem4_1 wal fax10lem4_1 sup_set_class fax10lem4_0 sup_set_class wceq fax10lem4_1 wal fax10lem4_1 sup_set_class fax10lem4_2 sup_set_class wceq fax10lem4_1 wal fax10lem4_0 sup_set_class fax10lem4_2 sup_set_class wceq fax10lem4_1 wal fax10lem4_1 sup_set_class fax10lem4_0 sup_set_class wceq fax10lem4_1 sup_set_class fax10lem4_2 sup_set_class wceq fax10lem4_1 fax10lem4_0 sup_set_class fax10lem4_2 sup_set_class wceq fax10lem4_1 hba1 fax10lem4_0 sup_set_class fax10lem4_2 sup_set_class wceq fax10lem4_1 sup_set_class fax10lem4_0 sup_set_class wceq fax10lem4_1 sup_set_class fax10lem4_2 sup_set_class wceq wb fax10lem4_1 fax10lem4_0 fax10lem4_2 fax10lem4_1 equequ2 sps albidh biimprd syl6 syl7 spsd pm2.43d com12 pm2.18d $.
$}
$( Lemma for ~ ax10 .  Change free and bound variables.  (Contributed by
       NM, 22-Jul-2015.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$v v $.
	$v u $.
	$d w z $.
	$d u v w $.
	$d v x $.
	$d v y $.
	iax10lem5_0 $f set v $.
	iax10lem5_1 $f set u $.
	fax10lem5_0 $f set x $.
	fax10lem5_1 $f set y $.
	fax10lem5_2 $f set z $.
	fax10lem5_3 $f set w $.
	ax10lem5 $p |- ( A. z z = w -> A. y y = x ) $= fax10lem5_2 sup_set_class fax10lem5_3 sup_set_class wceq fax10lem5_2 wal fax10lem5_0 sup_set_class iax10lem5_0 sup_set_class wceq fax10lem5_0 wal fax10lem5_1 sup_set_class fax10lem5_0 sup_set_class wceq fax10lem5_1 wal fax10lem5_2 sup_set_class fax10lem5_3 sup_set_class wceq fax10lem5_2 wal iax10lem5_1 sup_set_class iax10lem5_0 sup_set_class wceq iax10lem5_1 wal fax10lem5_0 sup_set_class iax10lem5_0 sup_set_class wceq fax10lem5_0 wal fax10lem5_2 sup_set_class fax10lem5_3 sup_set_class wceq fax10lem5_2 wal iax10lem5_0 sup_set_class fax10lem5_3 sup_set_class wceq iax10lem5_0 wal iax10lem5_1 sup_set_class iax10lem5_0 sup_set_class wceq iax10lem5_1 wal fax10lem5_2 iax10lem5_0 fax10lem5_3 ax10lem1 iax10lem5_0 iax10lem5_1 fax10lem5_3 ax10lem4 syl iax10lem5_1 fax10lem5_0 iax10lem5_0 ax10lem1 syl fax10lem5_0 fax10lem5_1 iax10lem5_0 ax10lem4 syl $.
$}
$( Lemma for ~ ax10 .  Similar to ~ ax10o but with reversed antecedent.
     (Contributed by NM, 25-Jul-2015.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	fax10lem6_0 $f wff ph $.
	fax10lem6_1 $f set x $.
	fax10lem6_2 $f set y $.
	ax10lem6 $p |- ( A. y y = x -> ( A. x ph -> A. y ph ) ) $= fax10lem6_2 sup_set_class fax10lem6_1 sup_set_class wceq fax10lem6_2 wal fax10lem6_0 fax10lem6_1 wal fax10lem6_2 sup_set_class fax10lem6_1 sup_set_class wceq fax10lem6_0 wi fax10lem6_2 wal fax10lem6_0 fax10lem6_2 wal fax10lem6_2 sup_set_class fax10lem6_1 sup_set_class wceq fax10lem6_0 fax10lem6_1 wal fax10lem6_2 sup_set_class fax10lem6_1 sup_set_class wceq fax10lem6_0 wi fax10lem6_2 wal wi fax10lem6_2 fax10lem6_0 fax10lem6_2 fax10lem6_1 ax-11 sps fax10lem6_2 sup_set_class fax10lem6_1 sup_set_class wceq fax10lem6_2 sup_set_class fax10lem6_1 sup_set_class wceq fax10lem6_0 wi fax10lem6_0 fax10lem6_2 fax10lem6_2 sup_set_class fax10lem6_1 sup_set_class wceq fax10lem6_0 pm2.27 al2imi syld $.
$}
$( Derive set.mm's original ~ ax-10 from others.  (Contributed by NM,
       25-Jul-2015.)  (Revised by NM, 7-Nov-2015.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$d x z $.
	$d y z $.
	iax10_0 $f set z $.
	fax10_0 $f set x $.
	fax10_1 $f set y $.
	ax10 $p |- ( A. x x = y -> A. y y = x ) $= fax10_0 sup_set_class fax10_1 sup_set_class wceq fax10_0 wal iax10_0 sup_set_class fax10_0 sup_set_class wceq wn iax10_0 wal wn fax10_1 sup_set_class fax10_0 sup_set_class wceq fax10_1 wal iax10_0 fax10_0 ax9v iax10_0 sup_set_class fax10_0 sup_set_class wceq wn iax10_0 wal wn iax10_0 sup_set_class fax10_0 sup_set_class wceq iax10_0 wex fax10_0 sup_set_class fax10_1 sup_set_class wceq fax10_0 wal fax10_1 sup_set_class fax10_0 sup_set_class wceq fax10_1 wal iax10_0 sup_set_class fax10_0 sup_set_class wceq iax10_0 df-ex fax10_0 sup_set_class fax10_1 sup_set_class wceq fax10_0 wal iax10_0 sup_set_class fax10_0 sup_set_class wceq fax10_1 sup_set_class fax10_0 sup_set_class wceq fax10_1 wal iax10_0 fax10_0 sup_set_class fax10_1 sup_set_class wceq fax10_0 wal iax10_0 sup_set_class fax10_0 sup_set_class wceq fax10_1 sup_set_class fax10_0 sup_set_class wceq fax10_1 wal wn fax10_1 sup_set_class fax10_0 sup_set_class wceq fax10_1 wal wi fax10_1 sup_set_class fax10_0 sup_set_class wceq fax10_1 wal fax10_0 sup_set_class fax10_1 sup_set_class wceq fax10_0 wal fax10_1 sup_set_class fax10_0 sup_set_class wceq fax10_1 wal wn iax10_0 sup_set_class fax10_0 sup_set_class wceq fax10_1 sup_set_class fax10_0 sup_set_class wceq fax10_1 wal fax10_1 sup_set_class fax10_0 sup_set_class wceq fax10_1 wal wn iax10_0 sup_set_class fax10_0 sup_set_class wceq wa iax10_0 sup_set_class fax10_0 sup_set_class wceq fax10_1 wal fax10_0 sup_set_class fax10_1 sup_set_class wceq fax10_0 wal fax10_0 sup_set_class iax10_0 sup_set_class wceq fax10_0 wal fax10_1 sup_set_class fax10_0 sup_set_class wceq fax10_1 wal fax10_1 sup_set_class fax10_0 sup_set_class wceq fax10_1 wal wn iax10_0 sup_set_class fax10_0 sup_set_class wceq iax10_0 sup_set_class fax10_0 sup_set_class wceq fax10_1 wal fax10_1 fax10_0 iax10_0 dveeq2 imp fax10_0 sup_set_class fax10_1 sup_set_class wceq fax10_0 wal iax10_0 sup_set_class fax10_0 sup_set_class wceq fax10_1 wal iax10_0 sup_set_class fax10_0 sup_set_class wceq fax10_0 wal fax10_0 sup_set_class iax10_0 sup_set_class wceq fax10_0 wal iax10_0 sup_set_class fax10_0 sup_set_class wceq fax10_1 fax10_0 ax10lem6 iax10_0 sup_set_class fax10_0 sup_set_class wceq fax10_0 sup_set_class iax10_0 sup_set_class wceq fax10_0 iax10_0 fax10_0 equcomi alimi syl6 fax10_0 fax10_1 fax10_0 iax10_0 ax10lem5 syl56 exp3acom23 fax10_1 sup_set_class fax10_0 sup_set_class wceq fax10_1 wal pm2.18 syl6 exlimdv syl5bir mpi $.
$}
$( Generalization of ~ ax16 .  (Contributed by NM, 25-Jul-2015.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d x y $.
	$d w ph $.
	$d w z $.
	ia16g_0 $f set w $.
	fa16g_0 $f wff ph $.
	fa16g_1 $f set x $.
	fa16g_2 $f set y $.
	fa16g_3 $f set z $.
	a16g $p |- ( A. x x = y -> ( ph -> A. z ph ) ) $= ia16g_0 sup_set_class fa16g_3 sup_set_class wceq ia16g_0 wex fa16g_1 sup_set_class fa16g_2 sup_set_class wceq fa16g_1 wal ia16g_0 sup_set_class fa16g_3 sup_set_class wceq ia16g_0 wal fa16g_0 fa16g_0 fa16g_3 wal wi ia16g_0 fa16g_3 a9ev fa16g_3 ia16g_0 fa16g_1 fa16g_2 ax10lem5 ia16g_0 sup_set_class fa16g_3 sup_set_class wceq ia16g_0 sup_set_class fa16g_3 sup_set_class wceq ia16g_0 wal fa16g_0 fa16g_0 fa16g_3 wal wi wi ia16g_0 ia16g_0 sup_set_class fa16g_3 sup_set_class wceq ia16g_0 wal fa16g_0 fa16g_0 fa16g_3 wal wi ia16g_0 sup_set_class fa16g_3 sup_set_class wceq ia16g_0 wal fa16g_0 fa16g_0 fa16g_3 wal wi wi ia16g_0 wal ia16g_0 sup_set_class fa16g_3 sup_set_class wceq ia16g_0 wal wn ia16g_0 sup_set_class fa16g_3 sup_set_class wceq ia16g_0 wal fa16g_0 fa16g_0 fa16g_3 wal wi wi ia16g_0 ia16g_0 sup_set_class fa16g_3 sup_set_class wceq ia16g_0 hbn1 ia16g_0 sup_set_class fa16g_3 sup_set_class wceq ia16g_0 wal fa16g_0 fa16g_0 fa16g_3 wal wi pm2.21 alrimih fa16g_0 fa16g_0 fa16g_3 wal wi ia16g_0 sup_set_class fa16g_3 sup_set_class wceq ia16g_0 wal fa16g_0 fa16g_0 fa16g_3 wal wi wi ia16g_0 fa16g_0 fa16g_0 fa16g_3 wal wi ia16g_0 ax-17 fa16g_0 fa16g_0 fa16g_3 wal wi ia16g_0 sup_set_class fa16g_3 sup_set_class wceq ia16g_0 wal ax-1 alrimih ja ia16g_0 sup_set_class fa16g_3 sup_set_class wceq ia16g_0 wal fa16g_3 sup_set_class ia16g_0 sup_set_class wceq fa16g_3 wal ia16g_0 sup_set_class fa16g_3 sup_set_class wceq fa16g_0 fa16g_0 fa16g_3 wal wi ia16g_0 fa16g_3 ia16g_0 fa16g_3 ax10lem5 ia16g_0 sup_set_class fa16g_3 sup_set_class wceq fa16g_0 fa16g_3 sup_set_class ia16g_0 sup_set_class wceq fa16g_3 wal fa16g_0 fa16g_3 wal ia16g_0 sup_set_class fa16g_3 sup_set_class wceq fa16g_0 fa16g_3 sup_set_class ia16g_0 sup_set_class wceq fa16g_0 wi fa16g_3 wal fa16g_3 sup_set_class ia16g_0 sup_set_class wceq fa16g_3 wal fa16g_0 fa16g_3 wal wi ia16g_0 sup_set_class fa16g_3 sup_set_class wceq fa16g_3 sup_set_class ia16g_0 sup_set_class wceq fa16g_0 fa16g_0 ia16g_0 wal fa16g_3 sup_set_class ia16g_0 sup_set_class wceq fa16g_0 wi fa16g_3 wal ia16g_0 fa16g_3 equcomi fa16g_0 ia16g_0 ax-17 fa16g_0 fa16g_3 ia16g_0 ax-11 syl2im fa16g_3 sup_set_class ia16g_0 sup_set_class wceq fa16g_0 fa16g_3 ax-5 syl6 com23 syl5 exlimih mpsyl $.
$}
$( Commutation law for identical variable specifiers.  The antecedent and
     consequent are true when ` x ` and ` y ` are substituted with the same
     variable.  Lemma L12 in [Megill] p. 445 (p. 12 of the preprint).
     (Contributed by NM, 5-Aug-1993.) $)
${
	$v x $.
	$v y $.
	faecom_0 $f set x $.
	faecom_1 $f set y $.
	aecom $p |- ( A. x x = y -> A. y y = x ) $= faecom_0 faecom_1 ax10 $.
$}
$( A commutation rule for identical variable specifiers.  (Contributed by
       NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	faecoms_0 $f wff ph $.
	faecoms_1 $f set x $.
	faecoms_2 $f set y $.
	eaecoms_0 $e |- ( A. x x = y -> ph ) $.
	aecoms $p |- ( A. y y = x -> ph ) $= faecoms_2 sup_set_class faecoms_1 sup_set_class wceq faecoms_2 wal faecoms_1 sup_set_class faecoms_2 sup_set_class wceq faecoms_1 wal faecoms_0 faecoms_2 faecoms_1 aecom eaecoms_0 syl $.
$}
$( A commutation rule for distinct variable specifiers.  (Contributed by
       NM, 2-Jan-2002.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	fnaecoms_0 $f wff ph $.
	fnaecoms_1 $f set x $.
	fnaecoms_2 $f set y $.
	enaecoms_0 $e |- ( -. A. x x = y -> ph ) $.
	naecoms $p |- ( -. A. y y = x -> ph ) $= fnaecoms_0 fnaecoms_2 sup_set_class fnaecoms_1 sup_set_class wceq fnaecoms_2 wal fnaecoms_1 sup_set_class fnaecoms_2 sup_set_class wceq fnaecoms_1 wal fnaecoms_2 sup_set_class fnaecoms_1 sup_set_class wceq fnaecoms_2 wal fnaecoms_0 fnaecoms_1 fnaecoms_2 aecom enaecoms_0 nsyl4 con1i $.
$}
$( Theorem showing that ~ ax-9 follows from the weaker version ~ ax9v .
       (Even though this theorem depends on ~ ax-9 , all references of ~ ax-9
       are made via ~ ax9v .  An earlier version stated ~ ax9v as a separate
       axiom, but having two axioms caused some confusion.)

       This theorem should be referenced in place of ~ ax-9 so that all proofs
       can be traced back to ~ ax9v .  (Contributed by NM, 12-Nov-2013.)
       (Revised by NM, 25-Jul-2015.) $)
${
	$v x $.
	$v y $.
	$v v $.
	$d x v $.
	$d y v $.
	iax9_0 $f set v $.
	fax9_0 $f set x $.
	fax9_1 $f set y $.
	ax9 $p |- -. A. x -. x = y $= fax9_0 sup_set_class fax9_1 sup_set_class wceq fax9_0 wal fax9_0 sup_set_class fax9_1 sup_set_class wceq wn fax9_0 wal wn fax9_0 sup_set_class fax9_1 sup_set_class wceq wn fax9_0 wal fax9_0 sup_set_class fax9_1 sup_set_class wceq fax9_0 sup_set_class fax9_1 sup_set_class wceq fax9_0 wal fax9_0 sup_set_class fax9_1 sup_set_class wceq wn fax9_0 sp fax9_0 sup_set_class fax9_1 sup_set_class wceq fax9_0 sp nsyl3 fax9_0 sup_set_class fax9_1 sup_set_class wceq fax9_0 wal wn fax9_0 sup_set_class fax9_1 sup_set_class wceq wn fax9_0 wal wn wi iax9_0 sup_set_class fax9_1 sup_set_class wceq wn iax9_0 wal iax9_0 fax9_1 ax9v fax9_0 sup_set_class fax9_1 sup_set_class wceq fax9_0 wal wn fax9_0 sup_set_class fax9_1 sup_set_class wceq wn fax9_0 wal wn wi wn iax9_0 sup_set_class fax9_1 sup_set_class wceq wn iax9_0 iax9_0 sup_set_class fax9_1 sup_set_class wceq fax9_0 sup_set_class fax9_1 sup_set_class wceq fax9_0 wal wn fax9_0 sup_set_class fax9_1 sup_set_class wceq wn fax9_0 wal wn wi fax9_0 sup_set_class fax9_1 sup_set_class wceq fax9_0 wal wn iax9_0 sup_set_class fax9_1 sup_set_class wceq iax9_0 sup_set_class fax9_1 sup_set_class wceq fax9_0 wal fax9_0 sup_set_class fax9_1 sup_set_class wceq wn fax9_0 wal wn fax9_0 fax9_1 iax9_0 dveeq2 iax9_0 sup_set_class fax9_1 sup_set_class wceq fax9_0 wal fax9_0 sup_set_class iax9_0 sup_set_class wceq wn fax9_0 wal fax9_0 sup_set_class fax9_1 sup_set_class wceq wn fax9_0 wal fax9_0 iax9_0 ax9v iax9_0 sup_set_class fax9_1 sup_set_class wceq fax9_0 wal fax9_0 sup_set_class iax9_0 sup_set_class wceq wn fax9_0 sup_set_class fax9_1 sup_set_class wceq wn fax9_0 iax9_0 sup_set_class fax9_1 sup_set_class wceq fax9_0 hba1 iax9_0 sup_set_class fax9_1 sup_set_class wceq fax9_0 wal fax9_0 sup_set_class iax9_0 sup_set_class wceq fax9_0 sup_set_class fax9_1 sup_set_class wceq iax9_0 sup_set_class fax9_1 sup_set_class wceq fax9_0 wal iax9_0 sup_set_class fax9_1 sup_set_class wceq fax9_0 sup_set_class iax9_0 sup_set_class wceq fax9_0 sup_set_class fax9_1 sup_set_class wceq wb iax9_0 sup_set_class fax9_1 sup_set_class wceq fax9_0 sp iax9_0 fax9_1 fax9_0 equequ2 syl notbid albidh mtbii syl6com con3i alrimiv mt3 pm2.61i $.
$}
$( Show that the original axiom ~ ax-9o can be derived from ~ ax9 and
     others.  See ~ ax9from9o for the rederivation of ~ ax9 from ~ ax-9o .

     Normally, ~ ax9o should be used rather than ~ ax-9o , except by theorems
     specifically studying the latter's properties.  (Contributed by NM,
     5-Aug-1993.)  (Proof modification is discouraged.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	fax9o_0 $f wff ph $.
	fax9o_1 $f set x $.
	fax9o_2 $f set y $.
	ax9o $p |- ( A. x ( x = y -> A. x ph ) -> ph ) $= fax9o_1 sup_set_class fax9o_2 sup_set_class wceq fax9o_0 fax9o_1 wal wi fax9o_1 wal fax9o_0 fax9o_1 wal wn fax9o_1 wal wn fax9o_0 fax9o_1 sup_set_class fax9o_2 sup_set_class wceq fax9o_0 fax9o_1 wal wi fax9o_1 wal fax9o_0 fax9o_1 wal wn fax9o_1 wal fax9o_1 sup_set_class fax9o_2 sup_set_class wceq wn fax9o_1 wal fax9o_1 fax9o_2 ax9 fax9o_1 sup_set_class fax9o_2 sup_set_class wceq fax9o_0 fax9o_1 wal wi fax9o_0 fax9o_1 wal wn fax9o_1 sup_set_class fax9o_2 sup_set_class wceq wn fax9o_1 fax9o_1 sup_set_class fax9o_2 sup_set_class wceq fax9o_0 fax9o_1 wal con3 al2imi mtoi fax9o_0 fax9o_1 ax6o syl $.
$}
$( At least one individual exists.  This is not a theorem of free logic,
     which is sound in empty domains.  For such a logic, we would add this
     theorem as an axiom of set theory (Axiom 0 of [Kunen] p. 10).  In the
     system consisting of ~ ax-5 through ~ ax-14 and ~ ax-17 , all axioms other
     than ~ ax9 are believed to be theorems of free logic, although the system
     without ~ ax9 is probably not complete in free logic.  (Contributed by NM,
     5-Aug-1993.) $)
${
	$v x $.
	$v y $.
	fa9e_0 $f set x $.
	fa9e_1 $f set y $.
	a9e $p |- E. x x = y $= fa9e_0 sup_set_class fa9e_1 sup_set_class wceq fa9e_0 wex fa9e_0 sup_set_class fa9e_1 sup_set_class wceq wn fa9e_0 wal wn fa9e_0 fa9e_1 ax9 fa9e_0 sup_set_class fa9e_1 sup_set_class wceq fa9e_0 df-ex mpbir $.
$}
$( Show that ~ ax-10o can be derived from ~ ax-10 in the form of ~ ax10 .
     Normally, ~ ax10o should be used rather than ~ ax-10o , except by theorems
     specifically studying the latter's properties.  (Contributed by NM,
     16-May-2008.)  (Proof modification is discouraged.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	fax10o_0 $f wff ph $.
	fax10o_1 $f set x $.
	fax10o_2 $f set y $.
	ax10o $p |- ( A. x x = y -> ( A. x ph -> A. y ph ) ) $= fax10o_1 sup_set_class fax10o_2 sup_set_class wceq fax10o_1 wal fax10o_2 sup_set_class fax10o_1 sup_set_class wceq fax10o_2 wal fax10o_0 fax10o_1 wal fax10o_2 sup_set_class fax10o_1 sup_set_class wceq fax10o_0 wi fax10o_2 wal fax10o_0 fax10o_2 wal fax10o_1 fax10o_2 ax10 fax10o_1 sup_set_class fax10o_2 sup_set_class wceq fax10o_0 fax10o_1 wal fax10o_2 sup_set_class fax10o_1 sup_set_class wceq fax10o_0 wi fax10o_2 wal wi fax10o_1 fax10o_0 fax10o_1 wal fax10o_2 sup_set_class fax10o_1 sup_set_class wceq fax10o_0 wi fax10o_2 wal wi fax10o_2 fax10o_1 fax10o_0 fax10o_2 fax10o_1 ax-11 equcoms sps fax10o_2 sup_set_class fax10o_1 sup_set_class wceq fax10o_2 sup_set_class fax10o_1 sup_set_class wceq fax10o_0 wi fax10o_0 fax10o_2 fax10o_2 sup_set_class fax10o_1 sup_set_class wceq fax10o_0 pm2.27 al2imi sylsyld $.
$}
$( All variables are effectively bound in an identical variable specifier.
     (Contributed by NM, 5-Aug-1993.) $)
${
	$v x $.
	$v y $.
	$v z $.
	fhbae_0 $f set x $.
	fhbae_1 $f set y $.
	fhbae_2 $f set z $.
	hbae $p |- ( A. x x = y -> A. z A. x x = y ) $= fhbae_0 sup_set_class fhbae_1 sup_set_class wceq fhbae_0 wal fhbae_0 sup_set_class fhbae_1 sup_set_class wceq fhbae_2 wal fhbae_0 wal fhbae_0 sup_set_class fhbae_1 sup_set_class wceq fhbae_0 wal fhbae_2 wal fhbae_0 sup_set_class fhbae_1 sup_set_class wceq fhbae_0 sup_set_class fhbae_1 sup_set_class wceq fhbae_2 wal fhbae_0 fhbae_2 sup_set_class fhbae_0 sup_set_class wceq fhbae_2 wal fhbae_2 sup_set_class fhbae_1 sup_set_class wceq fhbae_2 wal fhbae_0 sup_set_class fhbae_1 sup_set_class wceq fhbae_0 wal fhbae_0 sup_set_class fhbae_1 sup_set_class wceq fhbae_2 wal wi fhbae_0 sup_set_class fhbae_1 sup_set_class wceq fhbae_0 wal fhbae_0 sup_set_class fhbae_1 sup_set_class wceq fhbae_2 sup_set_class fhbae_0 sup_set_class wceq fhbae_2 wal wn fhbae_2 sup_set_class fhbae_1 sup_set_class wceq fhbae_2 wal wn fhbae_0 sup_set_class fhbae_1 sup_set_class wceq fhbae_2 wal fhbae_0 sup_set_class fhbae_1 sup_set_class wceq fhbae_0 sp fhbae_0 fhbae_1 fhbae_2 ax12o syl7 fhbae_0 sup_set_class fhbae_1 sup_set_class wceq fhbae_0 wal fhbae_0 sup_set_class fhbae_1 sup_set_class wceq fhbae_2 wal wi fhbae_0 fhbae_2 fhbae_0 sup_set_class fhbae_1 sup_set_class wceq fhbae_0 fhbae_2 ax10o aecoms fhbae_0 sup_set_class fhbae_1 sup_set_class wceq fhbae_0 wal fhbae_0 sup_set_class fhbae_1 sup_set_class wceq fhbae_2 wal wi fhbae_1 fhbae_2 fhbae_0 sup_set_class fhbae_1 sup_set_class wceq fhbae_0 wal fhbae_0 sup_set_class fhbae_1 sup_set_class wceq fhbae_1 wal fhbae_1 sup_set_class fhbae_2 sup_set_class wceq fhbae_1 wal fhbae_0 sup_set_class fhbae_1 sup_set_class wceq fhbae_2 wal fhbae_0 sup_set_class fhbae_1 sup_set_class wceq fhbae_0 wal fhbae_0 sup_set_class fhbae_1 sup_set_class wceq fhbae_1 wal fhbae_0 sup_set_class fhbae_1 sup_set_class wceq fhbae_0 fhbae_1 ax10o pm2.43i fhbae_0 sup_set_class fhbae_1 sup_set_class wceq fhbae_1 fhbae_2 ax10o syl5 aecoms pm2.61ii a5i fhbae_0 sup_set_class fhbae_1 sup_set_class wceq fhbae_0 fhbae_2 ax-7 syl $.
$}
$( All variables are effectively bound in an identical variable specifier.
     (Contributed by Mario Carneiro, 11-Aug-2016.) $)
${
	$v x $.
	$v y $.
	$v z $.
	fnfae_0 $f set x $.
	fnfae_1 $f set y $.
	fnfae_2 $f set z $.
	nfae $p |- F/ z A. x x = y $= fnfae_0 sup_set_class fnfae_1 sup_set_class wceq fnfae_0 wal fnfae_2 fnfae_0 fnfae_1 fnfae_2 hbae nfi $.
$}
$( All variables are effectively bound in a distinct variable specifier.
     Lemma L19 in [Megill] p. 446 (p. 14 of the preprint).  (Contributed by NM,
     5-Aug-1993.) $)
${
	$v x $.
	$v y $.
	$v z $.
	fhbnae_0 $f set x $.
	fhbnae_1 $f set y $.
	fhbnae_2 $f set z $.
	hbnae $p |- ( -. A. x x = y -> A. z -. A. x x = y ) $= fhbnae_0 sup_set_class fhbnae_1 sup_set_class wceq fhbnae_0 wal fhbnae_2 fhbnae_0 fhbnae_1 fhbnae_2 hbae hbn $.
$}
$( All variables are effectively bound in a distinct variable specifier.
     (Contributed by Mario Carneiro, 11-Aug-2016.) $)
${
	$v x $.
	$v y $.
	$v z $.
	fnfnae_0 $f set x $.
	fnfnae_1 $f set y $.
	fnfnae_2 $f set z $.
	nfnae $p |- F/ z -. A. x x = y $= fnfnae_0 sup_set_class fnfnae_1 sup_set_class wceq fnfnae_0 wal fnfnae_2 fnfnae_0 fnfnae_1 fnfnae_2 nfae nfn $.
$}
$( Rule that applies ~ hbnae to antecedent.  (Contributed by NM,
       5-Aug-1993.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	fhbnaes_0 $f wff ph $.
	fhbnaes_1 $f set x $.
	fhbnaes_2 $f set y $.
	fhbnaes_3 $f set z $.
	ehbnaes_0 $e |- ( A. z -. A. x x = y -> ph ) $.
	hbnaes $p |- ( -. A. x x = y -> ph ) $= fhbnaes_1 sup_set_class fhbnaes_2 sup_set_class wceq fhbnaes_1 wal wn fhbnaes_1 sup_set_class fhbnaes_2 sup_set_class wceq fhbnaes_1 wal wn fhbnaes_3 wal fhbnaes_0 fhbnaes_1 fhbnaes_2 fhbnaes_3 hbnae ehbnaes_0 syl $.
$}
$( A variable is effectively not free in an equality if it is not either of
     the involved variables. ` F/ ` version of ~ ax-12o .  (Contributed by
     Mario Carneiro, 6-Oct-2016.) $)
${
	$v x $.
	$v y $.
	$v z $.
	fnfeqf_0 $f set x $.
	fnfeqf_1 $f set y $.
	fnfeqf_2 $f set z $.
	nfeqf $p |- ( ( -. A. z z = x /\ -. A. z z = y ) -> F/ z x = y ) $= fnfeqf_2 sup_set_class fnfeqf_0 sup_set_class wceq fnfeqf_2 wal wn fnfeqf_2 sup_set_class fnfeqf_1 sup_set_class wceq fnfeqf_2 wal wn wa fnfeqf_0 sup_set_class fnfeqf_1 sup_set_class wceq fnfeqf_2 fnfeqf_2 sup_set_class fnfeqf_0 sup_set_class wceq fnfeqf_2 wal wn fnfeqf_2 sup_set_class fnfeqf_1 sup_set_class wceq fnfeqf_2 wal wn fnfeqf_2 fnfeqf_2 fnfeqf_0 fnfeqf_2 nfnae fnfeqf_2 fnfeqf_1 fnfeqf_2 nfnae nfan fnfeqf_2 sup_set_class fnfeqf_0 sup_set_class wceq fnfeqf_2 wal wn fnfeqf_2 sup_set_class fnfeqf_1 sup_set_class wceq fnfeqf_2 wal wn fnfeqf_0 sup_set_class fnfeqf_1 sup_set_class wceq fnfeqf_0 sup_set_class fnfeqf_1 sup_set_class wceq fnfeqf_2 wal wi fnfeqf_0 fnfeqf_1 fnfeqf_2 ax12o imp nfd $.
$}
$( Lemma used in proofs of substitution properties.  (Contributed by NM,
     5-Aug-1993.)  (Proof shortened by Mario Carneiro, 20-May-2014.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	fequs4_0 $f wff ph $.
	fequs4_1 $f set x $.
	fequs4_2 $f set y $.
	equs4 $p |- ( A. x ( x = y -> ph ) -> E. x ( x = y /\ ph ) ) $= fequs4_1 sup_set_class fequs4_2 sup_set_class wceq fequs4_0 wi fequs4_1 wal fequs4_1 sup_set_class fequs4_2 sup_set_class wceq fequs4_0 wi fequs4_1 sup_set_class fequs4_2 sup_set_class wceq wa fequs4_1 wex fequs4_1 sup_set_class fequs4_2 sup_set_class wceq fequs4_0 wa fequs4_1 wex fequs4_1 sup_set_class fequs4_2 sup_set_class wceq fequs4_0 wi fequs4_1 wal fequs4_1 sup_set_class fequs4_2 sup_set_class wceq fequs4_1 wex fequs4_1 sup_set_class fequs4_2 sup_set_class wceq fequs4_0 wi fequs4_1 sup_set_class fequs4_2 sup_set_class wceq wa fequs4_1 wex fequs4_1 fequs4_2 a9e fequs4_1 sup_set_class fequs4_2 sup_set_class wceq fequs4_0 wi fequs4_1 sup_set_class fequs4_2 sup_set_class wceq fequs4_1 19.29 mpan2 fequs4_1 sup_set_class fequs4_2 sup_set_class wceq fequs4_0 wi fequs4_1 sup_set_class fequs4_2 sup_set_class wceq wa fequs4_1 sup_set_class fequs4_2 sup_set_class wceq fequs4_0 wa fequs4_1 fequs4_1 sup_set_class fequs4_2 sup_set_class wceq fequs4_0 wi fequs4_1 sup_set_class fequs4_2 sup_set_class wceq fequs4_1 sup_set_class fequs4_2 sup_set_class wceq fequs4_0 wa fequs4_1 sup_set_class fequs4_2 sup_set_class wceq fequs4_0 ancl imp eximi syl $.
$}
$( A useful equivalence related to substitution.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Andrew Salmon, 12-Aug-2011.)  (Revised
       by Mario Carneiro, 3-Oct-2016.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	fequsal_0 $f wff ph $.
	fequsal_1 $f wff ps $.
	fequsal_2 $f set x $.
	fequsal_3 $f set y $.
	eequsal_0 $e |- F/ x ps $.
	eequsal_1 $e |- ( x = y -> ( ph <-> ps ) ) $.
	equsal $p |- ( A. x ( x = y -> ph ) <-> ps ) $= fequsal_2 sup_set_class fequsal_3 sup_set_class wceq fequsal_0 wi fequsal_2 wal fequsal_2 sup_set_class fequsal_3 sup_set_class wceq fequsal_1 fequsal_2 wal wi fequsal_2 wal fequsal_1 fequsal_2 sup_set_class fequsal_3 sup_set_class wceq fequsal_0 wi fequsal_2 sup_set_class fequsal_3 sup_set_class wceq fequsal_1 fequsal_2 wal wi fequsal_2 fequsal_2 sup_set_class fequsal_3 sup_set_class wceq fequsal_0 fequsal_1 fequsal_2 wal fequsal_2 sup_set_class fequsal_3 sup_set_class wceq fequsal_0 fequsal_1 fequsal_1 fequsal_2 wal eequsal_1 fequsal_1 fequsal_2 eequsal_0 19.3 syl6bbr pm5.74i albii fequsal_1 fequsal_2 sup_set_class fequsal_3 sup_set_class wceq fequsal_1 fequsal_2 wal wi fequsal_2 wal fequsal_1 fequsal_2 sup_set_class fequsal_3 sup_set_class wceq fequsal_1 fequsal_2 wal wi fequsal_2 eequsal_0 fequsal_1 fequsal_1 fequsal_2 wal fequsal_2 sup_set_class fequsal_3 sup_set_class wceq fequsal_1 fequsal_2 eequsal_0 nfri a1d alrimi fequsal_1 fequsal_2 fequsal_3 ax9o impbii bitr4i $.
$}
$( A useful equivalence related to substitution.  (Contributed by NM,
       5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	fequsalh_0 $f wff ph $.
	fequsalh_1 $f wff ps $.
	fequsalh_2 $f set x $.
	fequsalh_3 $f set y $.
	eequsalh_0 $e |- ( ps -> A. x ps ) $.
	eequsalh_1 $e |- ( x = y -> ( ph <-> ps ) ) $.
	equsalh $p |- ( A. x ( x = y -> ph ) <-> ps ) $= fequsalh_0 fequsalh_1 fequsalh_2 fequsalh_3 fequsalh_1 fequsalh_2 eequsalh_0 nfi eequsalh_1 equsal $.
$}
$( A useful equivalence related to substitution.  (Contributed by NM,
       5-Aug-1993.)  (Revised by Mario Carneiro, 3-Oct-2016.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	fequsex_0 $f wff ph $.
	fequsex_1 $f wff ps $.
	fequsex_2 $f set x $.
	fequsex_3 $f set y $.
	eequsex_0 $e |- F/ x ps $.
	eequsex_1 $e |- ( x = y -> ( ph <-> ps ) ) $.
	equsex $p |- ( E. x ( x = y /\ ph ) <-> ps ) $= fequsex_2 sup_set_class fequsex_3 sup_set_class wceq fequsex_0 wn wi wn fequsex_2 wex fequsex_2 sup_set_class fequsex_3 sup_set_class wceq fequsex_0 wn wi fequsex_2 wal wn fequsex_2 sup_set_class fequsex_3 sup_set_class wceq fequsex_0 wa fequsex_2 wex fequsex_1 fequsex_2 sup_set_class fequsex_3 sup_set_class wceq fequsex_0 wn wi fequsex_2 exnal fequsex_2 sup_set_class fequsex_3 sup_set_class wceq fequsex_0 wa fequsex_2 sup_set_class fequsex_3 sup_set_class wceq fequsex_0 wn wi wn fequsex_2 fequsex_2 sup_set_class fequsex_3 sup_set_class wceq fequsex_0 df-an exbii fequsex_2 sup_set_class fequsex_3 sup_set_class wceq fequsex_0 wn wi fequsex_2 wal fequsex_1 fequsex_0 wn fequsex_1 wn fequsex_2 fequsex_3 fequsex_1 fequsex_2 eequsex_0 nfn fequsex_2 sup_set_class fequsex_3 sup_set_class wceq fequsex_0 fequsex_1 eequsex_1 notbid equsal con2bii 3bitr4i $.
$}
$( A useful equivalence related to substitution.  (Contributed by NM,
       5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	fequsexh_0 $f wff ph $.
	fequsexh_1 $f wff ps $.
	fequsexh_2 $f set x $.
	fequsexh_3 $f set y $.
	eequsexh_0 $e |- ( ps -> A. x ps ) $.
	eequsexh_1 $e |- ( x = y -> ( ph <-> ps ) ) $.
	equsexh $p |- ( E. x ( x = y /\ ph ) <-> ps ) $= fequsexh_0 fequsexh_1 fequsexh_2 fequsexh_3 fequsexh_1 fequsexh_2 eequsexh_0 nfi eequsexh_1 equsex $.
$}
$( Version of ~ dvelim without any variable restrictions.  (Contributed by
       NM, 1-Oct-2002.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v z $.
	fdvelimh_0 $f wff ph $.
	fdvelimh_1 $f wff ps $.
	fdvelimh_2 $f set x $.
	fdvelimh_3 $f set y $.
	fdvelimh_4 $f set z $.
	edvelimh_0 $e |- ( ph -> A. x ph ) $.
	edvelimh_1 $e |- ( ps -> A. z ps ) $.
	edvelimh_2 $e |- ( z = y -> ( ph <-> ps ) ) $.
	dvelimh $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $= fdvelimh_2 sup_set_class fdvelimh_3 sup_set_class wceq fdvelimh_2 wal wn fdvelimh_4 sup_set_class fdvelimh_3 sup_set_class wceq fdvelimh_0 wi fdvelimh_4 wal fdvelimh_4 sup_set_class fdvelimh_3 sup_set_class wceq fdvelimh_0 wi fdvelimh_4 wal fdvelimh_2 wal fdvelimh_1 fdvelimh_1 fdvelimh_2 wal fdvelimh_2 sup_set_class fdvelimh_4 sup_set_class wceq fdvelimh_2 wal fdvelimh_2 sup_set_class fdvelimh_3 sup_set_class wceq fdvelimh_2 wal wn fdvelimh_4 sup_set_class fdvelimh_3 sup_set_class wceq fdvelimh_0 wi fdvelimh_4 wal fdvelimh_4 sup_set_class fdvelimh_3 sup_set_class wceq fdvelimh_0 wi fdvelimh_4 wal fdvelimh_2 wal wi wi fdvelimh_2 sup_set_class fdvelimh_4 sup_set_class wceq fdvelimh_2 wal fdvelimh_4 sup_set_class fdvelimh_3 sup_set_class wceq fdvelimh_0 wi fdvelimh_4 wal fdvelimh_4 sup_set_class fdvelimh_3 sup_set_class wceq fdvelimh_0 wi fdvelimh_4 wal fdvelimh_2 wal wi fdvelimh_2 sup_set_class fdvelimh_3 sup_set_class wceq fdvelimh_2 wal wn fdvelimh_4 sup_set_class fdvelimh_3 sup_set_class wceq fdvelimh_0 wi fdvelimh_4 wal fdvelimh_4 sup_set_class fdvelimh_3 sup_set_class wceq fdvelimh_0 wi fdvelimh_4 wal fdvelimh_4 wal fdvelimh_2 sup_set_class fdvelimh_4 sup_set_class wceq fdvelimh_2 wal fdvelimh_4 sup_set_class fdvelimh_3 sup_set_class wceq fdvelimh_0 wi fdvelimh_4 wal fdvelimh_2 wal fdvelimh_4 sup_set_class fdvelimh_3 sup_set_class wceq fdvelimh_0 wi fdvelimh_4 hba1 fdvelimh_4 sup_set_class fdvelimh_3 sup_set_class wceq fdvelimh_0 wi fdvelimh_4 wal fdvelimh_4 wal fdvelimh_4 sup_set_class fdvelimh_3 sup_set_class wceq fdvelimh_0 wi fdvelimh_4 wal fdvelimh_2 wal wi fdvelimh_4 fdvelimh_2 fdvelimh_4 sup_set_class fdvelimh_3 sup_set_class wceq fdvelimh_0 wi fdvelimh_4 wal fdvelimh_4 fdvelimh_2 ax10o aecoms syl5 a1d fdvelimh_2 sup_set_class fdvelimh_4 sup_set_class wceq fdvelimh_2 wal wn fdvelimh_2 sup_set_class fdvelimh_3 sup_set_class wceq fdvelimh_2 wal wn fdvelimh_4 sup_set_class fdvelimh_3 sup_set_class wceq fdvelimh_0 wi fdvelimh_4 wal fdvelimh_4 sup_set_class fdvelimh_3 sup_set_class wceq fdvelimh_0 wi fdvelimh_4 wal fdvelimh_2 wal wi fdvelimh_2 sup_set_class fdvelimh_4 sup_set_class wceq fdvelimh_2 wal wn fdvelimh_2 sup_set_class fdvelimh_3 sup_set_class wceq fdvelimh_2 wal wn wa fdvelimh_4 sup_set_class fdvelimh_3 sup_set_class wceq fdvelimh_0 wi fdvelimh_2 fdvelimh_4 fdvelimh_2 sup_set_class fdvelimh_4 sup_set_class wceq fdvelimh_2 wal wn fdvelimh_2 sup_set_class fdvelimh_3 sup_set_class wceq fdvelimh_2 wal wn fdvelimh_4 fdvelimh_2 fdvelimh_4 fdvelimh_4 hbnae fdvelimh_2 fdvelimh_3 fdvelimh_4 hbnae hban fdvelimh_2 sup_set_class fdvelimh_4 sup_set_class wceq fdvelimh_2 wal wn fdvelimh_2 sup_set_class fdvelimh_3 sup_set_class wceq fdvelimh_2 wal wn wa fdvelimh_4 sup_set_class fdvelimh_3 sup_set_class wceq fdvelimh_0 fdvelimh_2 fdvelimh_2 sup_set_class fdvelimh_4 sup_set_class wceq fdvelimh_2 wal wn fdvelimh_2 sup_set_class fdvelimh_3 sup_set_class wceq fdvelimh_2 wal wn fdvelimh_2 fdvelimh_2 fdvelimh_4 fdvelimh_2 hbnae fdvelimh_2 fdvelimh_3 fdvelimh_2 hbnae hban fdvelimh_2 sup_set_class fdvelimh_4 sup_set_class wceq fdvelimh_2 wal wn fdvelimh_2 sup_set_class fdvelimh_3 sup_set_class wceq fdvelimh_2 wal wn fdvelimh_4 sup_set_class fdvelimh_3 sup_set_class wceq fdvelimh_4 sup_set_class fdvelimh_3 sup_set_class wceq fdvelimh_2 wal wi fdvelimh_4 fdvelimh_3 fdvelimh_2 ax12o imp fdvelimh_0 fdvelimh_0 fdvelimh_2 wal wi fdvelimh_2 sup_set_class fdvelimh_4 sup_set_class wceq fdvelimh_2 wal wn fdvelimh_2 sup_set_class fdvelimh_3 sup_set_class wceq fdvelimh_2 wal wn wa edvelimh_0 a1i hbimd hbald ex pm2.61i fdvelimh_0 fdvelimh_1 fdvelimh_4 fdvelimh_3 edvelimh_1 edvelimh_2 equsalh fdvelimh_4 sup_set_class fdvelimh_3 sup_set_class wceq fdvelimh_0 wi fdvelimh_4 wal fdvelimh_1 fdvelimh_2 fdvelimh_0 fdvelimh_1 fdvelimh_4 fdvelimh_3 edvelimh_1 edvelimh_2 equsalh albii 3imtr3g $.
$}
$( Formula-building lemma for use with the Distinctor Reduction Theorem.
       Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).
       (Contributed by NM, 24-Nov-1994.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	fdral1_0 $f wff ph $.
	fdral1_1 $f wff ps $.
	fdral1_2 $f set x $.
	fdral1_3 $f set y $.
	edral1_0 $e |- ( A. x x = y -> ( ph <-> ps ) ) $.
	dral1 $p |- ( A. x x = y -> ( A. x ph <-> A. y ps ) ) $= fdral1_2 sup_set_class fdral1_3 sup_set_class wceq fdral1_2 wal fdral1_0 fdral1_2 wal fdral1_1 fdral1_3 wal fdral1_2 sup_set_class fdral1_3 sup_set_class wceq fdral1_2 wal fdral1_0 fdral1_2 wal fdral1_1 fdral1_2 wal fdral1_1 fdral1_3 wal fdral1_2 sup_set_class fdral1_3 sup_set_class wceq fdral1_2 wal fdral1_0 fdral1_1 fdral1_2 fdral1_2 fdral1_3 fdral1_2 hbae fdral1_2 sup_set_class fdral1_3 sup_set_class wceq fdral1_2 wal fdral1_0 fdral1_1 edral1_0 biimpd alimdh fdral1_1 fdral1_2 fdral1_3 ax10o syld fdral1_2 sup_set_class fdral1_3 sup_set_class wceq fdral1_2 wal fdral1_1 fdral1_3 wal fdral1_0 fdral1_3 wal fdral1_0 fdral1_2 wal fdral1_2 sup_set_class fdral1_3 sup_set_class wceq fdral1_2 wal fdral1_1 fdral1_0 fdral1_3 fdral1_2 fdral1_3 fdral1_3 hbae fdral1_2 sup_set_class fdral1_3 sup_set_class wceq fdral1_2 wal fdral1_0 fdral1_1 edral1_0 biimprd alimdh fdral1_0 fdral1_3 wal fdral1_0 fdral1_2 wal wi fdral1_3 fdral1_2 fdral1_0 fdral1_3 fdral1_2 ax10o aecoms syld impbid $.
$}
$( Formula-building lemma for use with the Distinctor Reduction Theorem.
       Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).
       (Contributed by NM, 27-Feb-2005.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v z $.
	fdral2_0 $f wff ph $.
	fdral2_1 $f wff ps $.
	fdral2_2 $f set x $.
	fdral2_3 $f set y $.
	fdral2_4 $f set z $.
	edral2_0 $e |- ( A. x x = y -> ( ph <-> ps ) ) $.
	dral2 $p |- ( A. x x = y -> ( A. z ph <-> A. z ps ) ) $= fdral2_2 sup_set_class fdral2_3 sup_set_class wceq fdral2_2 wal fdral2_0 fdral2_1 fdral2_4 fdral2_2 fdral2_3 fdral2_4 hbae edral2_0 albidh $.
$}
$( Formula-building lemma for use with the Distinctor Reduction Theorem.
       Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).
       (Contributed by NM, 27-Feb-2005.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	fdrex1_0 $f wff ph $.
	fdrex1_1 $f wff ps $.
	fdrex1_2 $f set x $.
	fdrex1_3 $f set y $.
	edrex1_0 $e |- ( A. x x = y -> ( ph <-> ps ) ) $.
	drex1 $p |- ( A. x x = y -> ( E. x ph <-> E. y ps ) ) $= fdrex1_2 sup_set_class fdrex1_3 sup_set_class wceq fdrex1_2 wal fdrex1_0 wn fdrex1_2 wal wn fdrex1_1 wn fdrex1_3 wal wn fdrex1_0 fdrex1_2 wex fdrex1_1 fdrex1_3 wex fdrex1_2 sup_set_class fdrex1_3 sup_set_class wceq fdrex1_2 wal fdrex1_0 wn fdrex1_2 wal fdrex1_1 wn fdrex1_3 wal fdrex1_0 wn fdrex1_1 wn fdrex1_2 fdrex1_3 fdrex1_2 sup_set_class fdrex1_3 sup_set_class wceq fdrex1_2 wal fdrex1_0 fdrex1_1 edrex1_0 notbid dral1 notbid fdrex1_0 fdrex1_2 df-ex fdrex1_1 fdrex1_3 df-ex 3bitr4g $.
$}
$( Formula-building lemma for use with the Distinctor Reduction Theorem.
       Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).
       (Contributed by NM, 27-Feb-2005.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v z $.
	fdrex2_0 $f wff ph $.
	fdrex2_1 $f wff ps $.
	fdrex2_2 $f set x $.
	fdrex2_3 $f set y $.
	fdrex2_4 $f set z $.
	edrex2_0 $e |- ( A. x x = y -> ( ph <-> ps ) ) $.
	drex2 $p |- ( A. x x = y -> ( E. z ph <-> E. z ps ) ) $= fdrex2_2 sup_set_class fdrex2_3 sup_set_class wceq fdrex2_2 wal fdrex2_0 fdrex2_1 fdrex2_4 fdrex2_2 fdrex2_3 fdrex2_4 hbae edrex2_0 exbidh $.
$}
$( Formula-building lemma for use with the Distinctor Reduction Theorem.
       (Contributed by Mario Carneiro, 4-Oct-2016.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	fdrnf1_0 $f wff ph $.
	fdrnf1_1 $f wff ps $.
	fdrnf1_2 $f set x $.
	fdrnf1_3 $f set y $.
	edrnf1_0 $e |- ( A. x x = y -> ( ph <-> ps ) ) $.
	drnf1 $p |- ( A. x x = y -> ( F/ x ph <-> F/ y ps ) ) $= fdrnf1_2 sup_set_class fdrnf1_3 sup_set_class wceq fdrnf1_2 wal fdrnf1_0 fdrnf1_0 fdrnf1_2 wal wi fdrnf1_2 wal fdrnf1_1 fdrnf1_1 fdrnf1_3 wal wi fdrnf1_3 wal fdrnf1_0 fdrnf1_2 wnf fdrnf1_1 fdrnf1_3 wnf fdrnf1_0 fdrnf1_0 fdrnf1_2 wal wi fdrnf1_1 fdrnf1_1 fdrnf1_3 wal wi fdrnf1_2 fdrnf1_3 fdrnf1_2 sup_set_class fdrnf1_3 sup_set_class wceq fdrnf1_2 wal fdrnf1_0 fdrnf1_1 fdrnf1_0 fdrnf1_2 wal fdrnf1_1 fdrnf1_3 wal edrnf1_0 fdrnf1_0 fdrnf1_1 fdrnf1_2 fdrnf1_3 edrnf1_0 dral1 imbi12d dral1 fdrnf1_0 fdrnf1_2 df-nf fdrnf1_1 fdrnf1_3 df-nf 3bitr4g $.
$}
$( Formula-building lemma for use with the Distinctor Reduction Theorem.
       (Contributed by Mario Carneiro, 4-Oct-2016.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v z $.
	fdrnf2_0 $f wff ph $.
	fdrnf2_1 $f wff ps $.
	fdrnf2_2 $f set x $.
	fdrnf2_3 $f set y $.
	fdrnf2_4 $f set z $.
	edrnf2_0 $e |- ( A. x x = y -> ( ph <-> ps ) ) $.
	drnf2 $p |- ( A. x x = y -> ( F/ z ph <-> F/ z ps ) ) $= fdrnf2_2 sup_set_class fdrnf2_3 sup_set_class wceq fdrnf2_2 wal fdrnf2_0 fdrnf2_0 fdrnf2_4 wal wi fdrnf2_4 wal fdrnf2_1 fdrnf2_1 fdrnf2_4 wal wi fdrnf2_4 wal fdrnf2_0 fdrnf2_4 wnf fdrnf2_1 fdrnf2_4 wnf fdrnf2_0 fdrnf2_0 fdrnf2_4 wal wi fdrnf2_1 fdrnf2_1 fdrnf2_4 wal wi fdrnf2_2 fdrnf2_3 fdrnf2_4 fdrnf2_2 sup_set_class fdrnf2_3 sup_set_class wceq fdrnf2_2 wal fdrnf2_0 fdrnf2_1 fdrnf2_0 fdrnf2_4 wal fdrnf2_1 fdrnf2_4 wal edrnf2_0 fdrnf2_0 fdrnf2_1 fdrnf2_2 fdrnf2_3 fdrnf2_4 edrnf2_0 dral2 imbi12d dral2 fdrnf2_0 fdrnf2_4 df-nf fdrnf2_1 fdrnf2_4 df-nf 3bitr4g $.
$}
$( Distribution of existential quantifiers, with a bound-variable
       hypothesis saying that ` y ` is not free in ` ph ` , but ` x ` can be
       free in ` ph ` (and there is no distinct variable condition on ` x ` and
       ` y ` ).  (Contributed by Mario Carneiro, 20-Mar-2013.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	fexdistrf_0 $f wff ph $.
	fexdistrf_1 $f wff ps $.
	fexdistrf_2 $f set x $.
	fexdistrf_3 $f set y $.
	eexdistrf_0 $e |- ( -. A. x x = y -> F/ y ph ) $.
	exdistrf $p |- ( E. x E. y ( ph /\ ps ) -> E. x ( ph /\ E. y ps ) ) $= fexdistrf_2 sup_set_class fexdistrf_3 sup_set_class wceq fexdistrf_2 wal fexdistrf_0 fexdistrf_1 wa fexdistrf_3 wex fexdistrf_2 wex fexdistrf_0 fexdistrf_1 fexdistrf_3 wex wa fexdistrf_2 wex wi fexdistrf_2 sup_set_class fexdistrf_3 sup_set_class wceq fexdistrf_2 wal fexdistrf_0 fexdistrf_1 wa fexdistrf_3 wex fexdistrf_2 wex fexdistrf_0 fexdistrf_1 wa fexdistrf_2 wex fexdistrf_2 wex fexdistrf_0 fexdistrf_1 fexdistrf_3 wex wa fexdistrf_2 wex fexdistrf_0 fexdistrf_1 wa fexdistrf_2 wex fexdistrf_0 fexdistrf_1 wa fexdistrf_3 wex fexdistrf_2 fexdistrf_3 fexdistrf_2 fexdistrf_0 fexdistrf_1 wa fexdistrf_0 fexdistrf_1 wa fexdistrf_2 fexdistrf_3 fexdistrf_2 sup_set_class fexdistrf_3 sup_set_class wceq fexdistrf_2 wal fexdistrf_0 fexdistrf_1 wa biidd drex1 drex2 fexdistrf_0 fexdistrf_1 wa fexdistrf_2 wex fexdistrf_2 wex fexdistrf_0 fexdistrf_1 wa fexdistrf_2 wex fexdistrf_0 fexdistrf_1 fexdistrf_3 wex wa fexdistrf_2 wex fexdistrf_0 fexdistrf_1 wa fexdistrf_2 wex fexdistrf_2 fexdistrf_0 fexdistrf_1 wa fexdistrf_2 nfe1 19.9 fexdistrf_0 fexdistrf_1 wa fexdistrf_0 fexdistrf_1 fexdistrf_3 wex wa fexdistrf_2 fexdistrf_1 fexdistrf_1 fexdistrf_3 wex fexdistrf_0 fexdistrf_1 fexdistrf_3 19.8a anim2i eximi sylbi syl6bir fexdistrf_2 sup_set_class fexdistrf_3 sup_set_class wceq fexdistrf_2 wal wn fexdistrf_0 fexdistrf_1 wa fexdistrf_3 wex fexdistrf_0 fexdistrf_1 fexdistrf_3 wex wa fexdistrf_2 fexdistrf_2 fexdistrf_3 fexdistrf_2 nfnae fexdistrf_0 fexdistrf_1 wa fexdistrf_3 wex fexdistrf_0 fexdistrf_3 wex fexdistrf_1 fexdistrf_3 wex wa fexdistrf_2 sup_set_class fexdistrf_3 sup_set_class wceq fexdistrf_2 wal wn fexdistrf_0 fexdistrf_1 fexdistrf_3 wex wa fexdistrf_0 fexdistrf_1 fexdistrf_3 19.40 fexdistrf_2 sup_set_class fexdistrf_3 sup_set_class wceq fexdistrf_2 wal wn fexdistrf_0 fexdistrf_3 wex fexdistrf_0 fexdistrf_1 fexdistrf_3 wex fexdistrf_0 fexdistrf_2 sup_set_class fexdistrf_3 sup_set_class wceq fexdistrf_2 wal wn fexdistrf_3 eexdistrf_0 19.9d anim1d syl5 eximd pm2.61i $.
$}
$( Variation on ~ nfald which adds the hypothesis that ` x ` and ` y ` are
       distinct in the inner subproof.  (Contributed by Mario Carneiro,
       8-Oct-2016.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	fnfald2_0 $f wff ph $.
	fnfald2_1 $f wff ps $.
	fnfald2_2 $f set x $.
	fnfald2_3 $f set y $.
	enfald2_0 $e |- F/ y ph $.
	enfald2_1 $e |- ( ( ph /\ -. A. x x = y ) -> F/ x ps ) $.
	nfald2 $p |- ( ph -> F/ x A. y ps ) $= fnfald2_0 fnfald2_2 sup_set_class fnfald2_3 sup_set_class wceq fnfald2_2 wal fnfald2_1 fnfald2_3 wal fnfald2_2 wnf fnfald2_0 fnfald2_2 sup_set_class fnfald2_3 sup_set_class wceq fnfald2_2 wal wn fnfald2_1 fnfald2_3 wal fnfald2_2 wnf fnfald2_0 fnfald2_2 sup_set_class fnfald2_3 sup_set_class wceq fnfald2_2 wal wn wa fnfald2_1 fnfald2_2 fnfald2_3 fnfald2_0 fnfald2_2 sup_set_class fnfald2_3 sup_set_class wceq fnfald2_2 wal wn fnfald2_3 enfald2_0 fnfald2_2 fnfald2_3 fnfald2_3 nfnae nfan enfald2_1 nfald ex fnfald2_2 sup_set_class fnfald2_3 sup_set_class wceq fnfald2_2 wal fnfald2_1 fnfald2_3 wal fnfald2_2 wnf fnfald2_1 fnfald2_3 wal fnfald2_3 wnf fnfald2_1 fnfald2_3 nfa1 fnfald2_1 fnfald2_3 wal fnfald2_1 fnfald2_3 wal fnfald2_2 fnfald2_3 fnfald2_2 sup_set_class fnfald2_3 sup_set_class wceq fnfald2_2 wal fnfald2_1 fnfald2_3 wal biidd drnf1 mpbiri pm2.61d2 $.
$}
$( Variation on ~ nfexd which adds the hypothesis that ` x ` and ` y ` are
       distinct in the inner subproof.  (Contributed by Mario Carneiro,
       8-Oct-2016.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	fnfexd2_0 $f wff ph $.
	fnfexd2_1 $f wff ps $.
	fnfexd2_2 $f set x $.
	fnfexd2_3 $f set y $.
	enfexd2_0 $e |- F/ y ph $.
	enfexd2_1 $e |- ( ( ph /\ -. A. x x = y ) -> F/ x ps ) $.
	nfexd2 $p |- ( ph -> F/ x E. y ps ) $= fnfexd2_1 fnfexd2_3 wex fnfexd2_1 wn fnfexd2_3 wal wn fnfexd2_0 fnfexd2_2 fnfexd2_1 fnfexd2_3 df-ex fnfexd2_0 fnfexd2_1 wn fnfexd2_3 wal fnfexd2_2 fnfexd2_0 fnfexd2_1 wn fnfexd2_2 fnfexd2_3 enfexd2_0 fnfexd2_0 fnfexd2_2 sup_set_class fnfexd2_3 sup_set_class wceq fnfexd2_2 wal wn wa fnfexd2_1 fnfexd2_2 enfexd2_1 nfnd nfald2 nfnd nfxfrd $.
$}
$( Closed theorem form of ~ spim .  (Contributed by NM, 15-Jan-2008.)
     (Revised by Mario Carneiro, 17-Oct-2016.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	fspimt_0 $f wff ph $.
	fspimt_1 $f wff ps $.
	fspimt_2 $f set x $.
	fspimt_3 $f set y $.
	spimt $p |- ( ( F/ x ps /\ A. x ( x = y -> ( ph -> ps ) ) ) -> ( A. x ph -> ps ) ) $= fspimt_1 fspimt_2 wnf fspimt_2 sup_set_class fspimt_3 sup_set_class wceq fspimt_0 fspimt_1 wi wi fspimt_2 wal wa fspimt_0 fspimt_2 wal fspimt_2 sup_set_class fspimt_3 sup_set_class wceq fspimt_1 fspimt_2 wal wi fspimt_2 wal fspimt_1 fspimt_1 fspimt_2 wnf fspimt_0 fspimt_2 wal fspimt_2 sup_set_class fspimt_3 sup_set_class wceq fspimt_0 fspimt_1 wi wi fspimt_2 wal fspimt_2 sup_set_class fspimt_3 sup_set_class wceq fspimt_1 fspimt_2 wal wi fspimt_2 wal fspimt_1 fspimt_2 wnf fspimt_0 fspimt_2 wal wa fspimt_2 sup_set_class fspimt_3 sup_set_class wceq fspimt_0 fspimt_1 wi wi fspimt_2 sup_set_class fspimt_3 sup_set_class wceq fspimt_1 fspimt_2 wal wi fspimt_2 fspimt_1 fspimt_2 wnf fspimt_0 fspimt_2 wal fspimt_2 fspimt_1 fspimt_2 nfnf1 fspimt_0 fspimt_2 nfa1 nfan fspimt_1 fspimt_2 wnf fspimt_0 fspimt_2 wal wa fspimt_0 fspimt_1 wi fspimt_1 fspimt_2 wal fspimt_2 sup_set_class fspimt_3 sup_set_class wceq fspimt_1 fspimt_2 wnf fspimt_0 fspimt_2 wal wa fspimt_0 fspimt_1 fspimt_1 fspimt_2 wal fspimt_0 fspimt_2 wal fspimt_0 fspimt_1 fspimt_2 wnf fspimt_0 fspimt_2 sp adantl fspimt_1 fspimt_2 wnf fspimt_1 fspimt_1 fspimt_2 wal wi fspimt_0 fspimt_2 wal fspimt_1 fspimt_2 nfr adantr embantd imim2d alimd impancom fspimt_1 fspimt_2 fspimt_3 ax9o syl6 $.
$}
$( Specialization, using implicit substitution.  Compare Lemma 14 of
       [Tarski] p. 70.  The ~ spim series of theorems requires that only one
       direction of the substitution hypothesis hold.  (Contributed by NM,
       5-Aug-1993.)  (Revised by Mario Carneiro, 3-Oct-2016.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	fspim_0 $f wff ph $.
	fspim_1 $f wff ps $.
	fspim_2 $f set x $.
	fspim_3 $f set y $.
	espim_0 $e |- F/ x ps $.
	espim_1 $e |- ( x = y -> ( ph -> ps ) ) $.
	spim $p |- ( A. x ph -> ps ) $= fspim_1 fspim_2 wnf fspim_2 sup_set_class fspim_3 sup_set_class wceq fspim_0 fspim_1 wi wi fspim_2 wal fspim_0 fspim_2 wal fspim_1 wi espim_0 fspim_2 sup_set_class fspim_3 sup_set_class wceq fspim_0 fspim_1 wi wi fspim_2 espim_1 ax-gen fspim_0 fspim_1 fspim_2 fspim_3 spimt mp2an $.
$}
$( Existential introduction, using implicit substitution.  Compare Lemma 14
       of [Tarski] p. 70.  (Contributed by NM, 7-Aug-1994.)  (Revised by Mario
       Carneiro, 3-Oct-2016.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	fspime_0 $f wff ph $.
	fspime_1 $f wff ps $.
	fspime_2 $f set x $.
	fspime_3 $f set y $.
	espime_0 $e |- F/ x ph $.
	espime_1 $e |- ( x = y -> ( ph -> ps ) ) $.
	spime $p |- ( ph -> E. x ps ) $= fspime_0 fspime_1 wn fspime_2 wal wn fspime_1 fspime_2 wex fspime_1 wn fspime_2 wal fspime_0 fspime_1 wn fspime_0 wn fspime_2 fspime_3 fspime_0 fspime_2 espime_0 nfn fspime_2 sup_set_class fspime_3 sup_set_class wceq fspime_0 fspime_1 espime_1 con3d spim con2i fspime_1 fspime_2 df-ex sylibr $.
$}
$( Deduction version of ~ spime .  (Contributed by NM, 5-Aug-1993.)
       (Revised by Mario Carneiro, 3-Oct-2016.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	$v y $.
	fspimed_0 $f wff ph $.
	fspimed_1 $f wff ps $.
	fspimed_2 $f wff ch $.
	fspimed_3 $f set x $.
	fspimed_4 $f set y $.
	espimed_0 $e |- ( ch -> F/ x ph ) $.
	espimed_1 $e |- ( x = y -> ( ph -> ps ) ) $.
	spimed $p |- ( ch -> ( ph -> E. x ps ) ) $= fspimed_2 fspimed_0 fspimed_3 wnf fspimed_0 fspimed_1 fspimed_3 wex wi espimed_0 fspimed_0 fspimed_3 wnf fspimed_0 fspimed_1 fspimed_3 wex fspimed_0 fspimed_3 wnf fspimed_0 wa fspimed_1 fspimed_3 fspimed_4 fspimed_0 fspimed_3 wnf fspimed_0 fspimed_3 fspimed_0 fspimed_3 nfnf1 fspimed_0 fspimed_3 wnf id nfan1 fspimed_3 sup_set_class fspimed_4 sup_set_class wceq fspimed_0 fspimed_1 fspimed_0 fspimed_3 wnf espimed_1 adantld spime ex syl $.
$}
$( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	$v y $.
	fcbv1h_0 $f wff ph $.
	fcbv1h_1 $f wff ps $.
	fcbv1h_2 $f wff ch $.
	fcbv1h_3 $f set x $.
	fcbv1h_4 $f set y $.
	ecbv1h_0 $e |- ( ph -> ( ps -> A. y ps ) ) $.
	ecbv1h_1 $e |- ( ph -> ( ch -> A. x ch ) ) $.
	ecbv1h_2 $e |- ( ph -> ( x = y -> ( ps -> ch ) ) ) $.
	cbv1h $p |- ( A. x A. y ph -> ( A. x ps -> A. y ch ) ) $= fcbv1h_0 fcbv1h_4 wal fcbv1h_3 wal fcbv1h_1 fcbv1h_3 wal fcbv1h_1 fcbv1h_3 wal fcbv1h_4 wal fcbv1h_2 fcbv1h_4 wal fcbv1h_0 fcbv1h_4 wal fcbv1h_3 wal fcbv1h_1 fcbv1h_3 wal fcbv1h_1 fcbv1h_4 wal fcbv1h_3 wal fcbv1h_1 fcbv1h_3 wal fcbv1h_4 wal fcbv1h_0 fcbv1h_4 wal fcbv1h_1 fcbv1h_1 fcbv1h_4 wal fcbv1h_3 fcbv1h_0 fcbv1h_1 fcbv1h_1 fcbv1h_4 wal wi fcbv1h_4 ecbv1h_0 sps al2imi fcbv1h_1 fcbv1h_3 fcbv1h_4 ax-7 syl6 fcbv1h_0 fcbv1h_1 fcbv1h_3 wal fcbv1h_4 wal fcbv1h_2 fcbv1h_4 wal wi fcbv1h_4 fcbv1h_3 fcbv1h_0 fcbv1h_3 wal fcbv1h_1 fcbv1h_3 wal fcbv1h_2 fcbv1h_4 fcbv1h_0 fcbv1h_3 wal fcbv1h_1 fcbv1h_3 wal fcbv1h_3 sup_set_class fcbv1h_4 sup_set_class wceq fcbv1h_2 fcbv1h_3 wal wi fcbv1h_3 wal fcbv1h_2 fcbv1h_0 fcbv1h_1 fcbv1h_3 sup_set_class fcbv1h_4 sup_set_class wceq fcbv1h_2 fcbv1h_3 wal wi fcbv1h_3 fcbv1h_0 fcbv1h_1 fcbv1h_3 sup_set_class fcbv1h_4 sup_set_class wceq fcbv1h_2 fcbv1h_2 fcbv1h_3 wal fcbv1h_0 fcbv1h_3 sup_set_class fcbv1h_4 sup_set_class wceq fcbv1h_1 fcbv1h_2 ecbv1h_2 com23 ecbv1h_1 syl6d al2imi fcbv1h_2 fcbv1h_3 fcbv1h_4 ax9o syl6 al2imi a7s syld $.
$}
$( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 5-Aug-1993.)  (Revised by Mario Carneiro,
       3-Oct-2016.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	$v y $.
	fcbv1_0 $f wff ph $.
	fcbv1_1 $f wff ps $.
	fcbv1_2 $f wff ch $.
	fcbv1_3 $f set x $.
	fcbv1_4 $f set y $.
	ecbv1_0 $e |- ( ph -> F/ y ps ) $.
	ecbv1_1 $e |- ( ph -> F/ x ch ) $.
	ecbv1_2 $e |- ( ph -> ( x = y -> ( ps -> ch ) ) ) $.
	cbv1 $p |- ( A. x A. y ph -> ( A. x ps -> A. y ch ) ) $= fcbv1_0 fcbv1_1 fcbv1_2 fcbv1_3 fcbv1_4 fcbv1_0 fcbv1_1 fcbv1_4 ecbv1_0 nfrd fcbv1_0 fcbv1_2 fcbv1_3 ecbv1_1 nfrd ecbv1_2 cbv1h $.
$}
$( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	$v y $.
	fcbv2h_0 $f wff ph $.
	fcbv2h_1 $f wff ps $.
	fcbv2h_2 $f wff ch $.
	fcbv2h_3 $f set x $.
	fcbv2h_4 $f set y $.
	ecbv2h_0 $e |- ( ph -> ( ps -> A. y ps ) ) $.
	ecbv2h_1 $e |- ( ph -> ( ch -> A. x ch ) ) $.
	ecbv2h_2 $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
	cbv2h $p |- ( A. x A. y ph -> ( A. x ps <-> A. y ch ) ) $= fcbv2h_0 fcbv2h_4 wal fcbv2h_3 wal fcbv2h_1 fcbv2h_3 wal fcbv2h_2 fcbv2h_4 wal fcbv2h_0 fcbv2h_1 fcbv2h_2 fcbv2h_3 fcbv2h_4 ecbv2h_0 ecbv2h_1 fcbv2h_0 fcbv2h_3 sup_set_class fcbv2h_4 sup_set_class wceq fcbv2h_1 fcbv2h_2 wb fcbv2h_1 fcbv2h_2 wi ecbv2h_2 fcbv2h_1 fcbv2h_2 bi1 syl6 cbv1h fcbv2h_0 fcbv2h_2 fcbv2h_4 wal fcbv2h_1 fcbv2h_3 wal wi fcbv2h_4 fcbv2h_3 fcbv2h_0 fcbv2h_2 fcbv2h_1 fcbv2h_4 fcbv2h_3 ecbv2h_1 ecbv2h_0 fcbv2h_4 sup_set_class fcbv2h_3 sup_set_class wceq fcbv2h_3 sup_set_class fcbv2h_4 sup_set_class wceq fcbv2h_0 fcbv2h_1 fcbv2h_2 wb fcbv2h_2 fcbv2h_1 wi fcbv2h_4 fcbv2h_3 equcomi ecbv2h_2 fcbv2h_1 fcbv2h_2 bi2 syl56 cbv1h a7s impbid $.
$}
$( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 5-Aug-1993.)  (Revised by Mario Carneiro,
       3-Oct-2016.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	$v y $.
	fcbv2_0 $f wff ph $.
	fcbv2_1 $f wff ps $.
	fcbv2_2 $f wff ch $.
	fcbv2_3 $f set x $.
	fcbv2_4 $f set y $.
	ecbv2_0 $e |- ( ph -> F/ y ps ) $.
	ecbv2_1 $e |- ( ph -> F/ x ch ) $.
	ecbv2_2 $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
	cbv2 $p |- ( A. x A. y ph -> ( A. x ps <-> A. y ch ) ) $= fcbv2_0 fcbv2_1 fcbv2_2 fcbv2_3 fcbv2_4 fcbv2_0 fcbv2_1 fcbv2_4 ecbv2_0 nfrd fcbv2_0 fcbv2_2 fcbv2_3 ecbv2_1 nfrd ecbv2_2 cbv2h $.
$}
$( Rule used to change bound variables, using implicit substitution, that
       does not use ~ ax-12o .  (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	fcbv3_0 $f wff ph $.
	fcbv3_1 $f wff ps $.
	fcbv3_2 $f set x $.
	fcbv3_3 $f set y $.
	ecbv3_0 $e |- F/ y ph $.
	ecbv3_1 $e |- F/ x ps $.
	ecbv3_2 $e |- ( x = y -> ( ph -> ps ) ) $.
	cbv3 $p |- ( A. x ph -> A. y ps ) $= wtru fcbv3_3 wal fcbv3_0 fcbv3_2 wal fcbv3_1 fcbv3_3 wal wi fcbv3_2 wtru fcbv3_0 fcbv3_1 fcbv3_2 fcbv3_3 fcbv3_0 fcbv3_3 wnf wtru ecbv3_0 a1i fcbv3_1 fcbv3_2 wnf wtru ecbv3_1 a1i fcbv3_2 sup_set_class fcbv3_3 sup_set_class wceq fcbv3_0 fcbv3_1 wi wi wtru ecbv3_2 a1i cbv1 wtru fcbv3_3 tru ax-gen mpg $.
$}
$( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew Salmon,
       25-May-2011.)  (Proof modification is discouraged.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	fcbv3h_0 $f wff ph $.
	fcbv3h_1 $f wff ps $.
	fcbv3h_2 $f set x $.
	fcbv3h_3 $f set y $.
	ecbv3h_0 $e |- ( ph -> A. y ph ) $.
	ecbv3h_1 $e |- ( ps -> A. x ps ) $.
	ecbv3h_2 $e |- ( x = y -> ( ph -> ps ) ) $.
	cbv3h $p |- ( A. x ph -> A. y ps ) $= fcbv3h_3 sup_set_class fcbv3h_3 sup_set_class wceq fcbv3h_3 wal fcbv3h_0 fcbv3h_2 wal fcbv3h_1 fcbv3h_3 wal wi fcbv3h_2 fcbv3h_3 sup_set_class fcbv3h_3 sup_set_class wceq fcbv3h_0 fcbv3h_1 fcbv3h_2 fcbv3h_3 fcbv3h_0 fcbv3h_0 fcbv3h_3 wal wi fcbv3h_3 sup_set_class fcbv3h_3 sup_set_class wceq ecbv3h_0 a1i fcbv3h_1 fcbv3h_1 fcbv3h_2 wal wi fcbv3h_3 sup_set_class fcbv3h_3 sup_set_class wceq ecbv3h_1 a1i fcbv3h_2 sup_set_class fcbv3h_3 sup_set_class wceq fcbv3h_0 fcbv3h_1 wi wi fcbv3h_3 sup_set_class fcbv3h_3 sup_set_class wceq ecbv3h_2 a1i cbv1h fcbv3h_3 stdpc6 mpg $.
$}
$( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 5-Aug-1993.)  (Revised by Mario Carneiro,
       3-Oct-2016.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	fcbval_0 $f wff ph $.
	fcbval_1 $f wff ps $.
	fcbval_2 $f set x $.
	fcbval_3 $f set y $.
	ecbval_0 $e |- F/ y ph $.
	ecbval_1 $e |- F/ x ps $.
	ecbval_2 $e |- ( x = y -> ( ph <-> ps ) ) $.
	cbval $p |- ( A. x ph <-> A. y ps ) $= fcbval_0 fcbval_2 wal fcbval_1 fcbval_3 wal fcbval_0 fcbval_1 fcbval_2 fcbval_3 ecbval_0 ecbval_1 fcbval_2 sup_set_class fcbval_3 sup_set_class wceq fcbval_0 fcbval_1 ecbval_2 biimpd cbv3 fcbval_1 fcbval_0 fcbval_3 fcbval_2 ecbval_1 ecbval_0 fcbval_1 fcbval_0 wi fcbval_2 fcbval_3 fcbval_2 sup_set_class fcbval_3 sup_set_class wceq fcbval_0 fcbval_1 ecbval_2 biimprd equcoms cbv3 impbii $.
$}
$( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	fcbvex_0 $f wff ph $.
	fcbvex_1 $f wff ps $.
	fcbvex_2 $f set x $.
	fcbvex_3 $f set y $.
	ecbvex_0 $e |- F/ y ph $.
	ecbvex_1 $e |- F/ x ps $.
	ecbvex_2 $e |- ( x = y -> ( ph <-> ps ) ) $.
	cbvex $p |- ( E. x ph <-> E. y ps ) $= fcbvex_0 wn fcbvex_2 wal wn fcbvex_1 wn fcbvex_3 wal wn fcbvex_0 fcbvex_2 wex fcbvex_1 fcbvex_3 wex fcbvex_0 wn fcbvex_2 wal fcbvex_1 wn fcbvex_3 wal fcbvex_0 wn fcbvex_1 wn fcbvex_2 fcbvex_3 fcbvex_0 fcbvex_3 ecbvex_0 nfn fcbvex_1 fcbvex_2 ecbvex_1 nfn fcbvex_2 sup_set_class fcbvex_3 sup_set_class wceq fcbvex_0 fcbvex_1 ecbvex_2 notbid cbval notbii fcbvex_0 fcbvex_2 df-ex fcbvex_1 fcbvex_3 df-ex 3bitr4i $.
$}
$( Implicit substitution of ` y ` for ` x ` into a theorem.  (Contributed
       by Raph Levien, 9-Jul-2003.)  (Revised by Mario Carneiro,
       3-Oct-2016.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	fchvar_0 $f wff ph $.
	fchvar_1 $f wff ps $.
	fchvar_2 $f set x $.
	fchvar_3 $f set y $.
	echvar_0 $e |- F/ x ps $.
	echvar_1 $e |- ( x = y -> ( ph <-> ps ) ) $.
	echvar_2 $e |- ph $.
	chvar $p |- ps $= fchvar_0 fchvar_1 fchvar_2 fchvar_0 fchvar_1 fchvar_2 fchvar_3 echvar_0 fchvar_2 sup_set_class fchvar_3 sup_set_class wceq fchvar_0 fchvar_1 echvar_1 biimpd spim echvar_2 mpg $.
$}
$( A variable introduction law for equality.  Lemma 15 of [Monk2] p. 109,
     however we do not require ` z ` to be distinct from ` x ` and ` y `
     (making the proof longer).  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Andrew Salmon, 25-May-2011.) $)
${
	$v x $.
	$v y $.
	$v z $.
	fequvini_0 $f set x $.
	fequvini_1 $f set y $.
	fequvini_2 $f set z $.
	equvini $p |- ( x = y -> E. z ( x = z /\ z = y ) ) $= fequvini_2 sup_set_class fequvini_0 sup_set_class wceq fequvini_2 wal fequvini_2 sup_set_class fequvini_1 sup_set_class wceq fequvini_2 wal fequvini_0 sup_set_class fequvini_1 sup_set_class wceq fequvini_0 sup_set_class fequvini_2 sup_set_class wceq fequvini_2 sup_set_class fequvini_1 sup_set_class wceq wa fequvini_2 wex wi fequvini_2 sup_set_class fequvini_0 sup_set_class wceq fequvini_2 wal fequvini_0 sup_set_class fequvini_1 sup_set_class wceq fequvini_0 sup_set_class fequvini_2 sup_set_class wceq fequvini_2 wal fequvini_2 sup_set_class fequvini_1 sup_set_class wceq fequvini_2 wex wa fequvini_0 sup_set_class fequvini_2 sup_set_class wceq fequvini_2 sup_set_class fequvini_1 sup_set_class wceq wa fequvini_2 wex fequvini_2 sup_set_class fequvini_0 sup_set_class wceq fequvini_2 wal fequvini_0 sup_set_class fequvini_2 sup_set_class wceq fequvini_2 wal fequvini_2 sup_set_class fequvini_1 sup_set_class wceq fequvini_2 wex wa fequvini_0 sup_set_class fequvini_1 sup_set_class wceq fequvini_2 sup_set_class fequvini_0 sup_set_class wceq fequvini_2 wal fequvini_0 sup_set_class fequvini_2 sup_set_class wceq fequvini_2 wal fequvini_2 sup_set_class fequvini_1 sup_set_class wceq fequvini_2 wex fequvini_2 sup_set_class fequvini_0 sup_set_class wceq fequvini_0 sup_set_class fequvini_2 sup_set_class wceq fequvini_2 fequvini_2 fequvini_0 equcomi alimi fequvini_2 fequvini_1 a9e jctir a1d fequvini_0 sup_set_class fequvini_2 sup_set_class wceq fequvini_2 sup_set_class fequvini_1 sup_set_class wceq fequvini_2 19.29 syl6 fequvini_2 sup_set_class fequvini_1 sup_set_class wceq fequvini_2 wal fequvini_0 sup_set_class fequvini_1 sup_set_class wceq fequvini_0 sup_set_class fequvini_2 sup_set_class wceq fequvini_2 wex fequvini_2 sup_set_class fequvini_1 sup_set_class wceq fequvini_2 wal wa fequvini_0 sup_set_class fequvini_2 sup_set_class wceq fequvini_2 sup_set_class fequvini_1 sup_set_class wceq wa fequvini_2 wex fequvini_2 sup_set_class fequvini_1 sup_set_class wceq fequvini_2 wal fequvini_0 sup_set_class fequvini_1 sup_set_class wceq fequvini_0 sup_set_class fequvini_2 sup_set_class wceq fequvini_2 wex fequvini_2 sup_set_class fequvini_1 sup_set_class wceq fequvini_2 wal fequvini_0 sup_set_class fequvini_1 sup_set_class wceq fequvini_0 sup_set_class fequvini_2 sup_set_class wceq fequvini_2 wex fequvini_2 sup_set_class fequvini_0 sup_set_class wceq fequvini_2 wex fequvini_0 sup_set_class fequvini_2 sup_set_class wceq fequvini_2 wex fequvini_2 fequvini_0 a9e fequvini_2 sup_set_class fequvini_0 sup_set_class wceq fequvini_0 sup_set_class fequvini_2 sup_set_class wceq fequvini_2 fequvini_2 fequvini_0 equcomi eximi ax-mp a1ii anc2ri fequvini_0 sup_set_class fequvini_2 sup_set_class wceq fequvini_2 sup_set_class fequvini_1 sup_set_class wceq fequvini_2 19.29r syl6 fequvini_2 sup_set_class fequvini_0 sup_set_class wceq fequvini_2 wal fequvini_2 sup_set_class fequvini_1 sup_set_class wceq fequvini_2 wal wo wn fequvini_2 sup_set_class fequvini_0 sup_set_class wceq fequvini_2 wal wn fequvini_2 sup_set_class fequvini_1 sup_set_class wceq fequvini_2 wal wn wa fequvini_0 sup_set_class fequvini_1 sup_set_class wceq fequvini_0 sup_set_class fequvini_2 sup_set_class wceq fequvini_2 sup_set_class fequvini_1 sup_set_class wceq wa fequvini_2 wex wi fequvini_2 sup_set_class fequvini_0 sup_set_class wceq fequvini_2 wal fequvini_2 sup_set_class fequvini_1 sup_set_class wceq fequvini_2 wal ioran fequvini_0 sup_set_class fequvini_1 sup_set_class wceq fequvini_0 sup_set_class fequvini_2 sup_set_class wceq fequvini_2 sup_set_class fequvini_1 sup_set_class wceq wa fequvini_2 sup_set_class fequvini_0 sup_set_class wceq fequvini_2 wal wn fequvini_2 sup_set_class fequvini_1 sup_set_class wceq fequvini_2 wal wn wa fequvini_2 fequvini_0 fequvini_0 fequvini_1 fequvini_2 nfeqf fequvini_0 sup_set_class fequvini_1 sup_set_class wceq fequvini_0 sup_set_class fequvini_2 sup_set_class wceq fequvini_2 sup_set_class fequvini_1 sup_set_class wceq wa wi fequvini_0 fequvini_2 fequvini_0 sup_set_class fequvini_2 sup_set_class wceq fequvini_0 sup_set_class fequvini_1 sup_set_class wceq fequvini_2 sup_set_class fequvini_1 sup_set_class wceq fequvini_0 fequvini_2 fequvini_1 ax-8 anc2li equcoms spimed sylbi ecase3 $.
$}
$( A variable elimination law for equality with no distinct variable
     requirements.  (Compare ~ equvini .)  (Contributed by NM, 1-Mar-2013.)
     (Proof shortened by Mario Carneiro, 17-Oct-2016.) $)
${
	$v x $.
	$v y $.
	$v z $.
	fequveli_0 $f set x $.
	fequveli_1 $f set y $.
	fequveli_2 $f set z $.
	equveli $p |- ( A. z ( z = x <-> z = y ) -> x = y ) $= fequveli_2 sup_set_class fequveli_0 sup_set_class wceq fequveli_2 sup_set_class fequveli_1 sup_set_class wceq wb fequveli_2 wal fequveli_2 sup_set_class fequveli_0 sup_set_class wceq fequveli_2 sup_set_class fequveli_1 sup_set_class wceq wi fequveli_2 wal fequveli_2 sup_set_class fequveli_1 sup_set_class wceq fequveli_2 sup_set_class fequveli_0 sup_set_class wceq wi fequveli_2 wal wa fequveli_0 sup_set_class fequveli_1 sup_set_class wceq fequveli_2 sup_set_class fequveli_0 sup_set_class wceq fequveli_2 sup_set_class fequveli_1 sup_set_class wceq fequveli_2 albiim fequveli_2 sup_set_class fequveli_1 sup_set_class wceq fequveli_2 wal fequveli_2 sup_set_class fequveli_0 sup_set_class wceq fequveli_2 sup_set_class fequveli_1 sup_set_class wceq wi fequveli_2 wal fequveli_2 sup_set_class fequveli_1 sup_set_class wceq fequveli_2 sup_set_class fequveli_0 sup_set_class wceq wi fequveli_2 wal wa fequveli_0 sup_set_class fequveli_1 sup_set_class wceq wi fequveli_2 sup_set_class fequveli_1 sup_set_class wceq fequveli_2 wal fequveli_2 sup_set_class fequveli_1 sup_set_class wceq fequveli_2 sup_set_class fequveli_0 sup_set_class wceq wi fequveli_2 wal fequveli_0 sup_set_class fequveli_1 sup_set_class wceq fequveli_2 sup_set_class fequveli_0 sup_set_class wceq fequveli_2 sup_set_class fequveli_1 sup_set_class wceq wi fequveli_2 wal fequveli_2 sup_set_class fequveli_1 sup_set_class wceq fequveli_2 wal fequveli_2 sup_set_class fequveli_1 sup_set_class wceq fequveli_2 sup_set_class fequveli_0 sup_set_class wceq wi fequveli_2 wal fequveli_1 sup_set_class fequveli_1 sup_set_class wceq fequveli_1 sup_set_class fequveli_0 sup_set_class wceq wi fequveli_1 wal fequveli_0 sup_set_class fequveli_1 sup_set_class wceq fequveli_2 sup_set_class fequveli_1 sup_set_class wceq fequveli_2 sup_set_class fequveli_0 sup_set_class wceq wi fequveli_1 sup_set_class fequveli_1 sup_set_class wceq fequveli_1 sup_set_class fequveli_0 sup_set_class wceq wi fequveli_2 fequveli_1 fequveli_2 sup_set_class fequveli_1 sup_set_class wceq fequveli_2 sup_set_class fequveli_1 sup_set_class wceq fequveli_2 sup_set_class fequveli_0 sup_set_class wceq wi fequveli_1 sup_set_class fequveli_1 sup_set_class wceq fequveli_1 sup_set_class fequveli_0 sup_set_class wceq wi wb fequveli_2 fequveli_2 sup_set_class fequveli_1 sup_set_class wceq fequveli_2 sup_set_class fequveli_1 sup_set_class wceq fequveli_1 sup_set_class fequveli_1 sup_set_class wceq fequveli_2 sup_set_class fequveli_0 sup_set_class wceq fequveli_1 sup_set_class fequveli_0 sup_set_class wceq fequveli_2 fequveli_1 fequveli_1 equequ1 fequveli_2 fequveli_1 fequveli_0 equequ1 imbi12d sps dral1 fequveli_1 sup_set_class fequveli_1 sup_set_class wceq fequveli_1 sup_set_class fequveli_0 sup_set_class wceq wi fequveli_1 wal fequveli_1 sup_set_class fequveli_0 sup_set_class wceq fequveli_0 sup_set_class fequveli_1 sup_set_class wceq fequveli_1 sup_set_class fequveli_1 sup_set_class wceq fequveli_1 sup_set_class fequveli_0 sup_set_class wceq wi fequveli_1 wal fequveli_1 sup_set_class fequveli_1 sup_set_class wceq fequveli_1 sup_set_class fequveli_0 sup_set_class wceq fequveli_1 equid fequveli_1 sup_set_class fequveli_1 sup_set_class wceq fequveli_1 sup_set_class fequveli_0 sup_set_class wceq wi fequveli_1 sp mpi fequveli_1 fequveli_0 equcomi syl syl6bi adantld fequveli_2 sup_set_class fequveli_1 sup_set_class wceq fequveli_2 wal wn fequveli_2 sup_set_class fequveli_0 sup_set_class wceq fequveli_2 sup_set_class fequveli_1 sup_set_class wceq wi fequveli_2 wal fequveli_0 sup_set_class fequveli_1 sup_set_class wceq fequveli_2 sup_set_class fequveli_1 sup_set_class wceq fequveli_2 sup_set_class fequveli_0 sup_set_class wceq wi fequveli_2 wal fequveli_2 sup_set_class fequveli_0 sup_set_class wceq fequveli_2 wal fequveli_2 sup_set_class fequveli_1 sup_set_class wceq fequveli_2 wal wn fequveli_2 sup_set_class fequveli_0 sup_set_class wceq fequveli_2 sup_set_class fequveli_1 sup_set_class wceq wi fequveli_2 wal fequveli_0 sup_set_class fequveli_1 sup_set_class wceq wi wi fequveli_2 sup_set_class fequveli_0 sup_set_class wceq fequveli_2 wal fequveli_2 sup_set_class fequveli_0 sup_set_class wceq fequveli_2 sup_set_class fequveli_1 sup_set_class wceq wi fequveli_2 wal fequveli_0 sup_set_class fequveli_1 sup_set_class wceq wi fequveli_2 sup_set_class fequveli_1 sup_set_class wceq fequveli_2 wal wn fequveli_2 sup_set_class fequveli_0 sup_set_class wceq fequveli_2 wal fequveli_2 sup_set_class fequveli_0 sup_set_class wceq fequveli_2 sup_set_class fequveli_1 sup_set_class wceq wi fequveli_2 wal fequveli_0 sup_set_class fequveli_0 sup_set_class wceq fequveli_0 sup_set_class fequveli_1 sup_set_class wceq wi fequveli_2 wal fequveli_0 sup_set_class fequveli_1 sup_set_class wceq fequveli_2 sup_set_class fequveli_0 sup_set_class wceq fequveli_2 sup_set_class fequveli_1 sup_set_class wceq wi fequveli_0 sup_set_class fequveli_0 sup_set_class wceq fequveli_0 sup_set_class fequveli_1 sup_set_class wceq wi fequveli_2 fequveli_0 fequveli_2 fequveli_2 sup_set_class fequveli_0 sup_set_class wceq fequveli_2 sup_set_class fequveli_0 sup_set_class wceq fequveli_2 sup_set_class fequveli_1 sup_set_class wceq wi fequveli_0 sup_set_class fequveli_0 sup_set_class wceq fequveli_0 sup_set_class fequveli_1 sup_set_class wceq wi wb fequveli_2 fequveli_2 sup_set_class fequveli_0 sup_set_class wceq fequveli_2 sup_set_class fequveli_0 sup_set_class wceq fequveli_0 sup_set_class fequveli_0 sup_set_class wceq fequveli_2 sup_set_class fequveli_1 sup_set_class wceq fequveli_0 sup_set_class fequveli_1 sup_set_class wceq fequveli_2 fequveli_0 fequveli_0 equequ1 fequveli_2 fequveli_0 fequveli_1 equequ1 imbi12d sps dral2 fequveli_0 sup_set_class fequveli_0 sup_set_class wceq fequveli_0 sup_set_class fequveli_1 sup_set_class wceq wi fequveli_0 sup_set_class fequveli_1 sup_set_class wceq fequveli_2 fequveli_0 sup_set_class fequveli_1 sup_set_class wceq fequveli_0 sup_set_class fequveli_0 sup_set_class wceq fequveli_0 sup_set_class fequveli_1 sup_set_class wceq wi fequveli_0 sup_set_class fequveli_0 sup_set_class wceq fequveli_0 sup_set_class fequveli_1 sup_set_class wceq fequveli_0 equid a1bi biimpri sps syl6bi a1d fequveli_2 sup_set_class fequveli_0 sup_set_class wceq fequveli_2 wal wn fequveli_2 sup_set_class fequveli_1 sup_set_class wceq fequveli_2 wal wn fequveli_2 sup_set_class fequveli_0 sup_set_class wceq fequveli_2 sup_set_class fequveli_1 sup_set_class wceq wi fequveli_2 wal fequveli_0 sup_set_class fequveli_1 sup_set_class wceq wi fequveli_2 sup_set_class fequveli_0 sup_set_class wceq fequveli_2 wal wn fequveli_2 sup_set_class fequveli_1 sup_set_class wceq fequveli_2 wal wn wa fequveli_0 sup_set_class fequveli_1 sup_set_class wceq fequveli_2 wnf fequveli_2 sup_set_class fequveli_0 sup_set_class wceq fequveli_2 sup_set_class fequveli_0 sup_set_class wceq fequveli_2 sup_set_class fequveli_1 sup_set_class wceq wi fequveli_0 sup_set_class fequveli_1 sup_set_class wceq wi wi fequveli_2 wal fequveli_2 sup_set_class fequveli_0 sup_set_class wceq fequveli_2 sup_set_class fequveli_1 sup_set_class wceq wi fequveli_2 wal fequveli_0 sup_set_class fequveli_1 sup_set_class wceq wi fequveli_0 fequveli_1 fequveli_2 nfeqf fequveli_2 sup_set_class fequveli_0 sup_set_class wceq fequveli_2 sup_set_class fequveli_0 sup_set_class wceq fequveli_2 sup_set_class fequveli_1 sup_set_class wceq wi fequveli_0 sup_set_class fequveli_1 sup_set_class wceq wi wi fequveli_2 fequveli_2 sup_set_class fequveli_0 sup_set_class wceq fequveli_2 sup_set_class fequveli_0 sup_set_class wceq fequveli_2 sup_set_class fequveli_1 sup_set_class wceq wi fequveli_0 sup_set_class fequveli_0 sup_set_class wceq fequveli_0 sup_set_class fequveli_1 sup_set_class wceq fequveli_0 equid fequveli_2 sup_set_class fequveli_0 sup_set_class wceq fequveli_0 sup_set_class fequveli_0 sup_set_class wceq fequveli_2 sup_set_class fequveli_0 sup_set_class wceq fequveli_2 sup_set_class fequveli_1 sup_set_class wceq fequveli_0 sup_set_class fequveli_1 sup_set_class wceq fequveli_2 fequveli_0 fequveli_0 equtr fequveli_2 fequveli_0 fequveli_1 ax-8 imim12d mpii ax-gen fequveli_2 sup_set_class fequveli_0 sup_set_class wceq fequveli_2 sup_set_class fequveli_1 sup_set_class wceq wi fequveli_0 sup_set_class fequveli_1 sup_set_class wceq fequveli_2 fequveli_0 spimt sylancl ex pm2.61i adantrd pm2.61i sylbi $.
$}
$( Two ways of expressing substitution when ` y ` is not free in ` ph ` .
       (Contributed by NM, 25-Apr-2008.)  (Revised by Mario Carneiro,
       4-Oct-2016.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	fequs45f_0 $f wff ph $.
	fequs45f_1 $f set x $.
	fequs45f_2 $f set y $.
	eequs45f_0 $e |- F/ y ph $.
	equs45f $p |- ( E. x ( x = y /\ ph ) <-> A. x ( x = y -> ph ) ) $= fequs45f_1 sup_set_class fequs45f_2 sup_set_class wceq fequs45f_0 wa fequs45f_1 wex fequs45f_1 sup_set_class fequs45f_2 sup_set_class wceq fequs45f_0 wi fequs45f_1 wal fequs45f_1 sup_set_class fequs45f_2 sup_set_class wceq fequs45f_0 wa fequs45f_1 wex fequs45f_1 sup_set_class fequs45f_2 sup_set_class wceq fequs45f_0 fequs45f_2 wal wa fequs45f_1 wex fequs45f_1 sup_set_class fequs45f_2 sup_set_class wceq fequs45f_0 wi fequs45f_1 wal fequs45f_1 sup_set_class fequs45f_2 sup_set_class wceq fequs45f_0 wa fequs45f_1 sup_set_class fequs45f_2 sup_set_class wceq fequs45f_0 fequs45f_2 wal wa fequs45f_1 fequs45f_0 fequs45f_0 fequs45f_2 wal fequs45f_1 sup_set_class fequs45f_2 sup_set_class wceq fequs45f_0 fequs45f_2 eequs45f_0 nfri anim2i eximi fequs45f_0 fequs45f_1 fequs45f_2 equs5a syl fequs45f_0 fequs45f_1 fequs45f_2 equs4 impbii $.
$}
$( A version of ~ spim with a distinct variable requirement instead of a
       bound variable hypothesis.  (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$d x ps $.
	fspimv_0 $f wff ph $.
	fspimv_1 $f wff ps $.
	fspimv_2 $f set x $.
	fspimv_3 $f set y $.
	espimv_0 $e |- ( x = y -> ( ph -> ps ) ) $.
	spimv $p |- ( A. x ph -> ps ) $= fspimv_0 fspimv_1 fspimv_2 fspimv_3 fspimv_1 fspimv_2 nfv espimv_0 spim $.
$}
$( A "distinctor elimination" lemma with no restrictions on variables in
       the consequent.  (Contributed by NM, 8-Nov-2006.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$v v $.
	$v u $.
	$d u v $.
	$d u x y $.
	$d u w $.
	iaev_0 $f set u $.
	faev_0 $f set x $.
	faev_1 $f set y $.
	faev_2 $f set z $.
	faev_3 $f set w $.
	faev_4 $f set v $.
	aev $p |- ( A. x x = y -> A. z w = v ) $= faev_0 sup_set_class faev_1 sup_set_class wceq faev_0 wal faev_3 sup_set_class faev_4 sup_set_class wceq faev_2 faev_0 faev_1 faev_2 hbae faev_0 sup_set_class faev_1 sup_set_class wceq faev_0 wal iaev_0 sup_set_class faev_4 sup_set_class wceq iaev_0 wal faev_3 sup_set_class faev_4 sup_set_class wceq faev_4 iaev_0 faev_0 faev_1 ax10lem5 iaev_0 sup_set_class faev_4 sup_set_class wceq faev_3 sup_set_class faev_4 sup_set_class wceq iaev_0 faev_3 iaev_0 faev_3 faev_4 ax-8 spimv syl alrimih $.
$}
$( Recovery of ~ ax-11o from ~ ax11v .  This proof uses ~ ax-10 and
       ~ ax-11 .  TODO: figure out if this is useful, or if it should be
       simplified or eliminated.  (Contributed by NM, 2-Feb-2007.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$d x z $.
	$d y z $.
	$d z ph $.
	fax11v2_0 $f wff ph $.
	fax11v2_1 $f set x $.
	fax11v2_2 $f set y $.
	fax11v2_3 $f set z $.
	eax11v2_0 $e |- ( x = z -> ( ph -> A. x ( x = z -> ph ) ) ) $.
	ax11v2 $p |- ( -. A. x x = y -> ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $= fax11v2_1 sup_set_class fax11v2_2 sup_set_class wceq fax11v2_1 wal wn fax11v2_3 sup_set_class fax11v2_2 sup_set_class wceq fax11v2_3 wex fax11v2_1 sup_set_class fax11v2_2 sup_set_class wceq fax11v2_0 fax11v2_1 sup_set_class fax11v2_2 sup_set_class wceq fax11v2_0 wi fax11v2_1 wal wi wi fax11v2_3 fax11v2_2 a9ev fax11v2_1 sup_set_class fax11v2_2 sup_set_class wceq fax11v2_1 wal wn fax11v2_3 sup_set_class fax11v2_2 sup_set_class wceq fax11v2_1 sup_set_class fax11v2_2 sup_set_class wceq fax11v2_0 fax11v2_1 sup_set_class fax11v2_2 sup_set_class wceq fax11v2_0 wi fax11v2_1 wal wi wi fax11v2_3 fax11v2_1 sup_set_class fax11v2_2 sup_set_class wceq fax11v2_1 wal wn fax11v2_3 sup_set_class fax11v2_2 sup_set_class wceq fax11v2_1 sup_set_class fax11v2_2 sup_set_class wceq fax11v2_0 fax11v2_1 sup_set_class fax11v2_2 sup_set_class wceq fax11v2_0 wi fax11v2_1 wal wi wi fax11v2_1 sup_set_class fax11v2_2 sup_set_class wceq fax11v2_1 wal wn fax11v2_3 sup_set_class fax11v2_2 sup_set_class wceq wa fax11v2_1 sup_set_class fax11v2_3 sup_set_class wceq fax11v2_0 fax11v2_1 sup_set_class fax11v2_3 sup_set_class wceq fax11v2_0 wi fax11v2_1 wal wi wi fax11v2_1 sup_set_class fax11v2_2 sup_set_class wceq fax11v2_0 fax11v2_1 sup_set_class fax11v2_2 sup_set_class wceq fax11v2_0 wi fax11v2_1 wal wi wi eax11v2_0 fax11v2_1 sup_set_class fax11v2_2 sup_set_class wceq fax11v2_1 wal wn fax11v2_3 sup_set_class fax11v2_2 sup_set_class wceq wa fax11v2_1 sup_set_class fax11v2_3 sup_set_class wceq fax11v2_1 sup_set_class fax11v2_2 sup_set_class wceq fax11v2_0 fax11v2_1 sup_set_class fax11v2_3 sup_set_class wceq fax11v2_0 wi fax11v2_1 wal wi fax11v2_0 fax11v2_1 sup_set_class fax11v2_2 sup_set_class wceq fax11v2_0 wi fax11v2_1 wal wi fax11v2_3 sup_set_class fax11v2_2 sup_set_class wceq fax11v2_1 sup_set_class fax11v2_3 sup_set_class wceq fax11v2_1 sup_set_class fax11v2_2 sup_set_class wceq wb fax11v2_1 sup_set_class fax11v2_2 sup_set_class wceq fax11v2_1 wal wn fax11v2_3 fax11v2_2 fax11v2_1 equequ2 adantl fax11v2_1 sup_set_class fax11v2_2 sup_set_class wceq fax11v2_1 wal wn fax11v2_3 sup_set_class fax11v2_2 sup_set_class wceq wa fax11v2_1 sup_set_class fax11v2_3 sup_set_class wceq fax11v2_0 wi fax11v2_1 wal fax11v2_1 sup_set_class fax11v2_2 sup_set_class wceq fax11v2_0 wi fax11v2_1 wal fax11v2_0 fax11v2_1 sup_set_class fax11v2_2 sup_set_class wceq fax11v2_1 wal wn fax11v2_3 sup_set_class fax11v2_2 sup_set_class wceq wa fax11v2_3 sup_set_class fax11v2_2 sup_set_class wceq fax11v2_1 wal fax11v2_1 sup_set_class fax11v2_3 sup_set_class wceq fax11v2_0 wi fax11v2_1 wal fax11v2_1 sup_set_class fax11v2_2 sup_set_class wceq fax11v2_0 wi fax11v2_1 wal wb fax11v2_1 sup_set_class fax11v2_2 sup_set_class wceq fax11v2_1 wal wn fax11v2_3 sup_set_class fax11v2_2 sup_set_class wceq fax11v2_3 sup_set_class fax11v2_2 sup_set_class wceq fax11v2_1 wal fax11v2_1 fax11v2_2 fax11v2_3 dveeq2 imp fax11v2_3 sup_set_class fax11v2_2 sup_set_class wceq fax11v2_1 wal fax11v2_1 sup_set_class fax11v2_3 sup_set_class wceq fax11v2_0 wi fax11v2_1 sup_set_class fax11v2_2 sup_set_class wceq fax11v2_0 wi fax11v2_1 fax11v2_3 sup_set_class fax11v2_2 sup_set_class wceq fax11v2_1 nfa1 fax11v2_3 sup_set_class fax11v2_2 sup_set_class wceq fax11v2_1 sup_set_class fax11v2_3 sup_set_class wceq fax11v2_0 wi fax11v2_1 sup_set_class fax11v2_2 sup_set_class wceq fax11v2_0 wi wb fax11v2_1 fax11v2_3 sup_set_class fax11v2_2 sup_set_class wceq fax11v2_1 sup_set_class fax11v2_3 sup_set_class wceq fax11v2_1 sup_set_class fax11v2_2 sup_set_class wceq fax11v2_0 fax11v2_3 fax11v2_2 fax11v2_1 equequ2 imbi1d sps albid syl imbi2d imbi12d mpbii ex exlimdv mpi $.
$}
$( Derive ~ ax-11o from a hypothesis in the form of ~ ax-11 . ~ ax-10 and
       ~ ax-11 are used by the proof, but not ~ ax-10o or ~ ax-11o .  TODO:
       figure out if this is useful, or if it should be simplified or
       eliminated.  (Contributed by NM, 2-Feb-2007.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$d x z $.
	$d y z $.
	$d z ph $.
	fax11a2_0 $f wff ph $.
	fax11a2_1 $f set x $.
	fax11a2_2 $f set y $.
	fax11a2_3 $f set z $.
	eax11a2_0 $e |- ( x = z -> ( A. z ph -> A. x ( x = z -> ph ) ) ) $.
	ax11a2 $p |- ( -. A. x x = y -> ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $= fax11a2_0 fax11a2_1 fax11a2_2 fax11a2_3 fax11a2_0 fax11a2_0 fax11a2_3 wal fax11a2_1 sup_set_class fax11a2_3 sup_set_class wceq fax11a2_1 sup_set_class fax11a2_3 sup_set_class wceq fax11a2_0 wi fax11a2_1 wal fax11a2_0 fax11a2_3 ax-17 eax11a2_0 syl5 ax11v2 $.
$}
$( Derivation of set.mm's original ~ ax-11o from ~ ax-10 and the shorter
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
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$d x z $.
	$d y z $.
	$d z ph $.
	iax11o_0 $f set z $.
	fax11o_0 $f wff ph $.
	fax11o_1 $f set x $.
	fax11o_2 $f set y $.
	ax11o $p |- ( -. A. x x = y -> ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $= fax11o_0 fax11o_1 fax11o_2 iax11o_0 fax11o_0 fax11o_1 iax11o_0 ax-11 ax11a2 $.
$}
$( A bidirectional version of ~ ax11o .  (Contributed by NM, 30-Jun-2006.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	fax11b_0 $f wff ph $.
	fax11b_1 $f set x $.
	fax11b_2 $f set y $.
	ax11b $p |- ( ( -. A. x x = y /\ x = y ) -> ( ph <-> A. x ( x = y -> ph ) ) ) $= fax11b_1 sup_set_class fax11b_2 sup_set_class wceq fax11b_1 wal wn fax11b_1 sup_set_class fax11b_2 sup_set_class wceq wa fax11b_0 fax11b_1 sup_set_class fax11b_2 sup_set_class wceq fax11b_0 wi fax11b_1 wal fax11b_1 sup_set_class fax11b_2 sup_set_class wceq fax11b_1 wal wn fax11b_1 sup_set_class fax11b_2 sup_set_class wceq fax11b_0 fax11b_1 sup_set_class fax11b_2 sup_set_class wceq fax11b_0 wi fax11b_1 wal wi fax11b_0 fax11b_1 fax11b_2 ax11o imp fax11b_1 sup_set_class fax11b_2 sup_set_class wceq fax11b_1 sup_set_class fax11b_2 sup_set_class wceq fax11b_0 wi fax11b_1 wal fax11b_0 wi fax11b_1 sup_set_class fax11b_2 sup_set_class wceq fax11b_1 wal wn fax11b_1 sup_set_class fax11b_2 sup_set_class wceq fax11b_0 wi fax11b_1 wal fax11b_1 sup_set_class fax11b_2 sup_set_class wceq fax11b_0 fax11b_1 sup_set_class fax11b_2 sup_set_class wceq fax11b_0 wi fax11b_1 sp com12 adantl impbid $.
$}
$( Lemma used in proofs of substitution properties.  (Contributed by NM,
     5-Aug-1993.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	fequs5_0 $f wff ph $.
	fequs5_1 $f set x $.
	fequs5_2 $f set y $.
	equs5 $p |- ( -. A. x x = y -> ( E. x ( x = y /\ ph ) -> A. x ( x = y -> ph ) ) ) $= fequs5_1 sup_set_class fequs5_2 sup_set_class wceq fequs5_1 wal wn fequs5_1 sup_set_class fequs5_2 sup_set_class wceq fequs5_0 wa fequs5_1 sup_set_class fequs5_2 sup_set_class wceq fequs5_0 wi fequs5_1 wal fequs5_1 fequs5_1 fequs5_2 fequs5_1 nfnae fequs5_1 sup_set_class fequs5_2 sup_set_class wceq fequs5_0 wi fequs5_1 nfa1 fequs5_1 sup_set_class fequs5_2 sup_set_class wceq fequs5_1 wal wn fequs5_1 sup_set_class fequs5_2 sup_set_class wceq fequs5_0 fequs5_1 sup_set_class fequs5_2 sup_set_class wceq fequs5_0 wi fequs5_1 wal fequs5_0 fequs5_1 fequs5_2 ax11o imp3a exlimd $.
$}
$( Version of ~ dvelimv without any variable restrictions.  (Contributed by
       NM, 1-Oct-2002.)  (Revised by Mario Carneiro, 6-Oct-2016.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v z $.
	fdvelimf_0 $f wff ph $.
	fdvelimf_1 $f wff ps $.
	fdvelimf_2 $f set x $.
	fdvelimf_3 $f set y $.
	fdvelimf_4 $f set z $.
	edvelimf_0 $e |- F/ x ph $.
	edvelimf_1 $e |- F/ z ps $.
	edvelimf_2 $e |- ( z = y -> ( ph <-> ps ) ) $.
	dvelimf $p |- ( -. A. x x = y -> F/ x ps ) $= fdvelimf_1 fdvelimf_4 sup_set_class fdvelimf_3 sup_set_class wceq fdvelimf_0 wi fdvelimf_4 wal fdvelimf_2 sup_set_class fdvelimf_3 sup_set_class wceq fdvelimf_2 wal wn fdvelimf_2 fdvelimf_4 sup_set_class fdvelimf_3 sup_set_class wceq fdvelimf_0 wi fdvelimf_4 wal fdvelimf_1 fdvelimf_0 fdvelimf_1 fdvelimf_4 fdvelimf_3 edvelimf_1 edvelimf_2 equsal bicomi fdvelimf_2 sup_set_class fdvelimf_3 sup_set_class wceq fdvelimf_2 wal wn fdvelimf_4 sup_set_class fdvelimf_3 sup_set_class wceq fdvelimf_0 wi fdvelimf_2 fdvelimf_4 fdvelimf_2 fdvelimf_3 fdvelimf_4 nfnae fdvelimf_2 sup_set_class fdvelimf_3 sup_set_class wceq fdvelimf_2 wal wn fdvelimf_2 sup_set_class fdvelimf_4 sup_set_class wceq fdvelimf_2 wal wn wa fdvelimf_4 sup_set_class fdvelimf_3 sup_set_class wceq fdvelimf_0 fdvelimf_2 fdvelimf_2 sup_set_class fdvelimf_3 sup_set_class wceq fdvelimf_2 wal wn fdvelimf_2 sup_set_class fdvelimf_4 sup_set_class wceq fdvelimf_2 wal wn wa fdvelimf_4 sup_set_class fdvelimf_3 sup_set_class wceq fdvelimf_2 fdvelimf_2 sup_set_class fdvelimf_3 sup_set_class wceq fdvelimf_2 wal wn fdvelimf_2 sup_set_class fdvelimf_4 sup_set_class wceq fdvelimf_2 wal wn fdvelimf_2 fdvelimf_2 fdvelimf_3 fdvelimf_2 nfnae fdvelimf_2 fdvelimf_4 fdvelimf_2 nfnae nfan fdvelimf_2 sup_set_class fdvelimf_4 sup_set_class wceq fdvelimf_2 wal wn fdvelimf_2 sup_set_class fdvelimf_3 sup_set_class wceq fdvelimf_2 wal wn fdvelimf_4 sup_set_class fdvelimf_3 sup_set_class wceq fdvelimf_4 sup_set_class fdvelimf_3 sup_set_class wceq fdvelimf_2 wal wi fdvelimf_4 fdvelimf_3 fdvelimf_2 ax12o impcom nfd fdvelimf_0 fdvelimf_2 wnf fdvelimf_2 sup_set_class fdvelimf_3 sup_set_class wceq fdvelimf_2 wal wn fdvelimf_2 sup_set_class fdvelimf_4 sup_set_class wceq fdvelimf_2 wal wn wa edvelimf_0 a1i nfimd nfald2 nfxfrd $.
$}
$( Specialization, using implicit substitution.  (Contributed by NM,
       30-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$d x ps $.
	fspv_0 $f wff ph $.
	fspv_1 $f wff ps $.
	fspv_2 $f set x $.
	fspv_3 $f set y $.
	espv_0 $e |- ( x = y -> ( ph <-> ps ) ) $.
	spv $p |- ( A. x ph -> ps ) $= fspv_0 fspv_1 fspv_2 fspv_3 fspv_2 sup_set_class fspv_3 sup_set_class wceq fspv_0 fspv_1 espv_0 biimpd spimv $.
$}
$( Distinct-variable version of ~ spime .  (Contributed by NM,
       5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$d x ph $.
	fspimev_0 $f wff ph $.
	fspimev_1 $f wff ps $.
	fspimev_2 $f set x $.
	fspimev_3 $f set y $.
	espimev_0 $e |- ( x = y -> ( ph -> ps ) ) $.
	spimev $p |- ( ph -> E. x ps ) $= fspimev_0 fspimev_1 fspimev_2 fspimev_3 fspimev_0 fspimev_2 nfv espimev_0 spime $.
$}
$( Inference from existential specialization, using implicit substitution.
       (Contributed by NM, 19-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$d x ps $.
	fspeiv_0 $f wff ph $.
	fspeiv_1 $f wff ps $.
	fspeiv_2 $f set x $.
	fspeiv_3 $f set y $.
	espeiv_0 $e |- ( x = y -> ( ph <-> ps ) ) $.
	espeiv_1 $e |- ps $.
	speiv $p |- E. x ph $= fspeiv_1 fspeiv_0 fspeiv_2 wex espeiv_1 fspeiv_1 fspeiv_0 fspeiv_2 fspeiv_3 fspeiv_2 sup_set_class fspeiv_3 sup_set_class wceq fspeiv_0 fspeiv_1 espeiv_0 biimprd spimev ax-mp $.
$}
$( A variable introduction law for equality.  Lemma 15 of [Monk2] p. 109.
       (Contributed by NM, 5-Aug-1993.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$d x z $.
	$d y z $.
	fequvin_0 $f set x $.
	fequvin_1 $f set y $.
	fequvin_2 $f set z $.
	equvin $p |- ( x = y <-> E. z ( x = z /\ z = y ) ) $= fequvin_0 sup_set_class fequvin_1 sup_set_class wceq fequvin_0 sup_set_class fequvin_2 sup_set_class wceq fequvin_2 sup_set_class fequvin_1 sup_set_class wceq wa fequvin_2 wex fequvin_0 fequvin_1 fequvin_2 equvini fequvin_0 sup_set_class fequvin_2 sup_set_class wceq fequvin_2 sup_set_class fequvin_1 sup_set_class wceq wa fequvin_0 sup_set_class fequvin_1 sup_set_class wceq fequvin_2 fequvin_0 sup_set_class fequvin_2 sup_set_class wceq fequvin_2 sup_set_class fequvin_1 sup_set_class wceq fequvin_0 sup_set_class fequvin_1 sup_set_class wceq fequvin_0 fequvin_2 fequvin_1 equtr imp exlimiv impbii $.
$}
$( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$d y ph $.
	$d x ps $.
	fcbvalv_0 $f wff ph $.
	fcbvalv_1 $f wff ps $.
	fcbvalv_2 $f set x $.
	fcbvalv_3 $f set y $.
	ecbvalv_0 $e |- ( x = y -> ( ph <-> ps ) ) $.
	cbvalv $p |- ( A. x ph <-> A. y ps ) $= fcbvalv_0 fcbvalv_1 fcbvalv_2 fcbvalv_3 fcbvalv_0 fcbvalv_3 nfv fcbvalv_1 fcbvalv_2 nfv ecbvalv_0 cbval $.
$}
$( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$d y ph $.
	$d x ps $.
	fcbvexv_0 $f wff ph $.
	fcbvexv_1 $f wff ps $.
	fcbvexv_2 $f set x $.
	fcbvexv_3 $f set y $.
	ecbvexv_0 $e |- ( x = y -> ( ph <-> ps ) ) $.
	cbvexv $p |- ( E. x ph <-> E. y ps ) $= fcbvexv_0 fcbvexv_1 fcbvexv_2 fcbvexv_3 fcbvexv_0 fcbvexv_3 nfv fcbvexv_1 fcbvexv_2 nfv ecbvexv_0 cbvex $.
$}
$( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 22-Dec-2003.)  (Revised by Mario Carneiro,
       6-Oct-2016.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d y x $.
	$d y z $.
	$d w x $.
	$d w z $.
	fcbval2_0 $f wff ph $.
	fcbval2_1 $f wff ps $.
	fcbval2_2 $f set x $.
	fcbval2_3 $f set y $.
	fcbval2_4 $f set z $.
	fcbval2_5 $f set w $.
	ecbval2_0 $e |- F/ z ph $.
	ecbval2_1 $e |- F/ w ph $.
	ecbval2_2 $e |- F/ x ps $.
	ecbval2_3 $e |- F/ y ps $.
	ecbval2_4 $e |- ( ( x = z /\ y = w ) -> ( ph <-> ps ) ) $.
	cbval2 $p |- ( A. x A. y ph <-> A. z A. w ps ) $= fcbval2_0 fcbval2_3 wal fcbval2_1 fcbval2_5 wal fcbval2_2 fcbval2_4 fcbval2_0 fcbval2_4 fcbval2_3 ecbval2_0 nfal fcbval2_1 fcbval2_2 fcbval2_5 ecbval2_2 nfal fcbval2_2 sup_set_class fcbval2_4 sup_set_class wceq fcbval2_0 fcbval2_3 wal fcbval2_1 fcbval2_5 wal wb wi fcbval2_2 sup_set_class fcbval2_4 sup_set_class wceq fcbval2_0 fcbval2_3 wal wa fcbval2_2 sup_set_class fcbval2_4 sup_set_class wceq fcbval2_1 fcbval2_5 wal wa wb fcbval2_2 sup_set_class fcbval2_4 sup_set_class wceq fcbval2_0 wa fcbval2_3 wal fcbval2_2 sup_set_class fcbval2_4 sup_set_class wceq fcbval2_1 wa fcbval2_5 wal fcbval2_2 sup_set_class fcbval2_4 sup_set_class wceq fcbval2_0 fcbval2_3 wal wa fcbval2_2 sup_set_class fcbval2_4 sup_set_class wceq fcbval2_1 fcbval2_5 wal wa fcbval2_2 sup_set_class fcbval2_4 sup_set_class wceq fcbval2_0 wa fcbval2_2 sup_set_class fcbval2_4 sup_set_class wceq fcbval2_1 wa fcbval2_3 fcbval2_5 fcbval2_2 sup_set_class fcbval2_4 sup_set_class wceq fcbval2_0 fcbval2_5 fcbval2_2 sup_set_class fcbval2_4 sup_set_class wceq fcbval2_5 nfv ecbval2_1 nfan fcbval2_2 sup_set_class fcbval2_4 sup_set_class wceq fcbval2_1 fcbval2_3 fcbval2_2 sup_set_class fcbval2_4 sup_set_class wceq fcbval2_3 nfv ecbval2_3 nfan fcbval2_3 sup_set_class fcbval2_5 sup_set_class wceq fcbval2_2 sup_set_class fcbval2_4 sup_set_class wceq fcbval2_0 fcbval2_1 fcbval2_2 sup_set_class fcbval2_4 sup_set_class wceq fcbval2_3 sup_set_class fcbval2_5 sup_set_class wceq fcbval2_0 fcbval2_1 wb ecbval2_4 expcom pm5.32d cbval fcbval2_2 sup_set_class fcbval2_4 sup_set_class wceq fcbval2_0 fcbval2_3 19.28v fcbval2_2 sup_set_class fcbval2_4 sup_set_class wceq fcbval2_1 fcbval2_5 19.28v 3bitr3i fcbval2_2 sup_set_class fcbval2_4 sup_set_class wceq fcbval2_0 fcbval2_3 wal fcbval2_1 fcbval2_5 wal pm5.32 mpbir cbval $.
$}
$( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 14-Sep-2003.)  (Revised by Mario Carneiro,
       6-Oct-2016.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d y x $.
	$d y z $.
	$d w x $.
	$d w z $.
	fcbvex2_0 $f wff ph $.
	fcbvex2_1 $f wff ps $.
	fcbvex2_2 $f set x $.
	fcbvex2_3 $f set y $.
	fcbvex2_4 $f set z $.
	fcbvex2_5 $f set w $.
	ecbvex2_0 $e |- F/ z ph $.
	ecbvex2_1 $e |- F/ w ph $.
	ecbvex2_2 $e |- F/ x ps $.
	ecbvex2_3 $e |- F/ y ps $.
	ecbvex2_4 $e |- ( ( x = z /\ y = w ) -> ( ph <-> ps ) ) $.
	cbvex2 $p |- ( E. x E. y ph <-> E. z E. w ps ) $= fcbvex2_0 fcbvex2_3 wex fcbvex2_1 fcbvex2_5 wex fcbvex2_2 fcbvex2_4 fcbvex2_0 fcbvex2_4 fcbvex2_3 ecbvex2_0 nfex fcbvex2_1 fcbvex2_2 fcbvex2_5 ecbvex2_2 nfex fcbvex2_2 sup_set_class fcbvex2_4 sup_set_class wceq fcbvex2_0 fcbvex2_3 wex fcbvex2_1 fcbvex2_5 wex wb wi fcbvex2_2 sup_set_class fcbvex2_4 sup_set_class wceq fcbvex2_0 fcbvex2_3 wex wa fcbvex2_2 sup_set_class fcbvex2_4 sup_set_class wceq fcbvex2_1 fcbvex2_5 wex wa wb fcbvex2_2 sup_set_class fcbvex2_4 sup_set_class wceq fcbvex2_0 wa fcbvex2_3 wex fcbvex2_2 sup_set_class fcbvex2_4 sup_set_class wceq fcbvex2_1 wa fcbvex2_5 wex fcbvex2_2 sup_set_class fcbvex2_4 sup_set_class wceq fcbvex2_0 fcbvex2_3 wex wa fcbvex2_2 sup_set_class fcbvex2_4 sup_set_class wceq fcbvex2_1 fcbvex2_5 wex wa fcbvex2_2 sup_set_class fcbvex2_4 sup_set_class wceq fcbvex2_0 wa fcbvex2_2 sup_set_class fcbvex2_4 sup_set_class wceq fcbvex2_1 wa fcbvex2_3 fcbvex2_5 fcbvex2_2 sup_set_class fcbvex2_4 sup_set_class wceq fcbvex2_0 fcbvex2_5 fcbvex2_2 sup_set_class fcbvex2_4 sup_set_class wceq fcbvex2_5 nfv ecbvex2_1 nfan fcbvex2_2 sup_set_class fcbvex2_4 sup_set_class wceq fcbvex2_1 fcbvex2_3 fcbvex2_2 sup_set_class fcbvex2_4 sup_set_class wceq fcbvex2_3 nfv ecbvex2_3 nfan fcbvex2_3 sup_set_class fcbvex2_5 sup_set_class wceq fcbvex2_2 sup_set_class fcbvex2_4 sup_set_class wceq fcbvex2_0 fcbvex2_1 fcbvex2_2 sup_set_class fcbvex2_4 sup_set_class wceq fcbvex2_3 sup_set_class fcbvex2_5 sup_set_class wceq fcbvex2_0 fcbvex2_1 wb ecbvex2_4 expcom pm5.32d cbvex fcbvex2_2 sup_set_class fcbvex2_4 sup_set_class wceq fcbvex2_0 fcbvex2_3 19.42v fcbvex2_2 sup_set_class fcbvex2_4 sup_set_class wceq fcbvex2_1 fcbvex2_5 19.42v 3bitr3i fcbvex2_2 sup_set_class fcbvex2_4 sup_set_class wceq fcbvex2_0 fcbvex2_3 wex fcbvex2_1 fcbvex2_5 wex pm5.32 mpbir cbvex $.
$}
$( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 4-Feb-2005.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d z w ph $.
	$d x y ps $.
	$d x w $.
	$d z y $.
	fcbval2v_0 $f wff ph $.
	fcbval2v_1 $f wff ps $.
	fcbval2v_2 $f set x $.
	fcbval2v_3 $f set y $.
	fcbval2v_4 $f set z $.
	fcbval2v_5 $f set w $.
	ecbval2v_0 $e |- ( ( x = z /\ y = w ) -> ( ph <-> ps ) ) $.
	cbval2v $p |- ( A. x A. y ph <-> A. z A. w ps ) $= fcbval2v_0 fcbval2v_1 fcbval2v_2 fcbval2v_3 fcbval2v_4 fcbval2v_5 fcbval2v_0 fcbval2v_4 nfv fcbval2v_0 fcbval2v_5 nfv fcbval2v_1 fcbval2v_2 nfv fcbval2v_1 fcbval2v_3 nfv ecbval2v_0 cbval2 $.
$}
$( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 26-Jul-1995.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d z w ph $.
	$d x y ps $.
	$d x w $.
	$d z y $.
	fcbvex2v_0 $f wff ph $.
	fcbvex2v_1 $f wff ps $.
	fcbvex2v_2 $f set x $.
	fcbvex2v_3 $f set y $.
	fcbvex2v_4 $f set z $.
	fcbvex2v_5 $f set w $.
	ecbvex2v_0 $e |- ( ( x = z /\ y = w ) -> ( ph <-> ps ) ) $.
	cbvex2v $p |- ( E. x E. y ph <-> E. z E. w ps ) $= fcbvex2v_0 fcbvex2v_1 fcbvex2v_2 fcbvex2v_3 fcbvex2v_4 fcbvex2v_5 fcbvex2v_0 fcbvex2v_4 nfv fcbvex2v_0 fcbvex2v_5 nfv fcbvex2v_1 fcbvex2v_2 nfv fcbvex2v_1 fcbvex2v_3 nfv ecbvex2v_0 cbvex2 $.
$}
$( Deduction used to change bound variables, using implicit substitution,
       particularly useful in conjunction with ~ dvelim .  (Contributed by NM,
       2-Jan-2002.)  (Revised by Mario Carneiro, 6-Oct-2016.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	$v y $.
	$d x ph $.
	$d x ch $.
	fcbvald_0 $f wff ph $.
	fcbvald_1 $f wff ps $.
	fcbvald_2 $f wff ch $.
	fcbvald_3 $f set x $.
	fcbvald_4 $f set y $.
	ecbvald_0 $e |- F/ y ph $.
	ecbvald_1 $e |- ( ph -> F/ y ps ) $.
	ecbvald_2 $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
	cbvald $p |- ( ph -> ( A. x ps <-> A. y ch ) ) $= fcbvald_0 fcbvald_0 fcbvald_4 wal fcbvald_3 wal fcbvald_1 fcbvald_3 wal fcbvald_2 fcbvald_4 wal wb fcbvald_0 fcbvald_0 fcbvald_4 wal fcbvald_3 fcbvald_0 fcbvald_4 ecbvald_0 nfri alrimiv fcbvald_0 fcbvald_1 fcbvald_2 fcbvald_3 fcbvald_4 ecbvald_1 fcbvald_0 fcbvald_2 fcbvald_3 nfvd ecbvald_2 cbv2 syl $.
$}
$( Deduction used to change bound variables, using implicit substitution,
       particularly useful in conjunction with ~ dvelim .  (Contributed by NM,
       2-Jan-2002.)  (Revised by Mario Carneiro, 6-Oct-2016.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	$v y $.
	$d x ph $.
	$d x ch $.
	fcbvexd_0 $f wff ph $.
	fcbvexd_1 $f wff ps $.
	fcbvexd_2 $f wff ch $.
	fcbvexd_3 $f set x $.
	fcbvexd_4 $f set y $.
	ecbvexd_0 $e |- F/ y ph $.
	ecbvexd_1 $e |- ( ph -> F/ y ps ) $.
	ecbvexd_2 $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
	cbvexd $p |- ( ph -> ( E. x ps <-> E. y ch ) ) $= fcbvexd_0 fcbvexd_1 wn fcbvexd_3 wal wn fcbvexd_2 wn fcbvexd_4 wal wn fcbvexd_1 fcbvexd_3 wex fcbvexd_2 fcbvexd_4 wex fcbvexd_0 fcbvexd_1 wn fcbvexd_3 wal fcbvexd_2 wn fcbvexd_4 wal fcbvexd_0 fcbvexd_1 wn fcbvexd_2 wn fcbvexd_3 fcbvexd_4 ecbvexd_0 fcbvexd_0 fcbvexd_1 fcbvexd_4 ecbvexd_1 nfnd fcbvexd_0 fcbvexd_3 sup_set_class fcbvexd_4 sup_set_class wceq fcbvexd_1 fcbvexd_2 wb fcbvexd_1 wn fcbvexd_2 wn wb ecbvexd_2 fcbvexd_1 fcbvexd_2 notbi syl6ib cbvald notbid fcbvexd_1 fcbvexd_3 df-ex fcbvexd_2 fcbvexd_4 df-ex 3bitr4g $.
$}
$( Rule used to change the bound variable in a universal quantifier with
       implicit substitution.  Deduction form.  (Contributed by David Moews,
       1-May-2017.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	$v y $.
	$d ps y $.
	$d ch x $.
	$d ph x $.
	$d ph y $.
	fcbvaldva_0 $f wff ph $.
	fcbvaldva_1 $f wff ps $.
	fcbvaldva_2 $f wff ch $.
	fcbvaldva_3 $f set x $.
	fcbvaldva_4 $f set y $.
	ecbvaldva_0 $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
	cbvaldva $p |- ( ph -> ( A. x ps <-> A. y ch ) ) $= fcbvaldva_0 fcbvaldva_1 fcbvaldva_2 fcbvaldva_3 fcbvaldva_4 fcbvaldva_0 fcbvaldva_4 nfv fcbvaldva_0 fcbvaldva_1 fcbvaldva_4 nfvd fcbvaldva_0 fcbvaldva_3 sup_set_class fcbvaldva_4 sup_set_class wceq fcbvaldva_1 fcbvaldva_2 wb ecbvaldva_0 ex cbvald $.
$}
$( Rule used to change the bound variable in an existential quantifier with
       implicit substitution.  Deduction form.  (Contributed by David Moews,
       1-May-2017.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	$v y $.
	$d ps y $.
	$d ch x $.
	$d ph x $.
	$d ph y $.
	fcbvexdva_0 $f wff ph $.
	fcbvexdva_1 $f wff ps $.
	fcbvexdva_2 $f wff ch $.
	fcbvexdva_3 $f set x $.
	fcbvexdva_4 $f set y $.
	ecbvexdva_0 $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
	cbvexdva $p |- ( ph -> ( E. x ps <-> E. y ch ) ) $= fcbvexdva_0 fcbvexdva_1 fcbvexdva_2 fcbvexdva_3 fcbvexdva_4 fcbvexdva_0 fcbvexdva_4 nfv fcbvexdva_0 fcbvexdva_1 fcbvexdva_4 nfvd fcbvexdva_0 fcbvexdva_3 sup_set_class fcbvexdva_4 sup_set_class wceq fcbvexdva_1 fcbvexdva_2 wb ecbvexdva_0 ex cbvexd $.
$}
$( Define temporary individual variables. $)
$( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 26-Jul-1995.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$v v $.
	$v u $.
	$v f $.
	$v g $.
	$d w z ch $.
	$d u v ph $.
	$d x y ps $.
	$d f g ps $.
	$d f w $.
	$d g z $.
	$d u v w x y z $.
	fcbvex4v_0 $f wff ph $.
	fcbvex4v_1 $f wff ps $.
	fcbvex4v_2 $f wff ch $.
	fcbvex4v_3 $f set x $.
	fcbvex4v_4 $f set y $.
	fcbvex4v_5 $f set z $.
	fcbvex4v_6 $f set w $.
	fcbvex4v_7 $f set v $.
	fcbvex4v_8 $f set u $.
	fcbvex4v_9 $f set f $.
	fcbvex4v_10 $f set g $.
	ecbvex4v_0 $e |- ( ( x = v /\ y = u ) -> ( ph <-> ps ) ) $.
	ecbvex4v_1 $e |- ( ( z = f /\ w = g ) -> ( ps <-> ch ) ) $.
	cbvex4v $p |- ( E. x E. y E. z E. w ph <-> E. v E. u E. f E. g ch ) $= fcbvex4v_0 fcbvex4v_6 wex fcbvex4v_5 wex fcbvex4v_4 wex fcbvex4v_3 wex fcbvex4v_1 fcbvex4v_6 wex fcbvex4v_5 wex fcbvex4v_8 wex fcbvex4v_7 wex fcbvex4v_2 fcbvex4v_10 wex fcbvex4v_9 wex fcbvex4v_8 wex fcbvex4v_7 wex fcbvex4v_0 fcbvex4v_6 wex fcbvex4v_5 wex fcbvex4v_1 fcbvex4v_6 wex fcbvex4v_5 wex fcbvex4v_3 fcbvex4v_4 fcbvex4v_7 fcbvex4v_8 fcbvex4v_3 sup_set_class fcbvex4v_7 sup_set_class wceq fcbvex4v_4 sup_set_class fcbvex4v_8 sup_set_class wceq wa fcbvex4v_0 fcbvex4v_1 fcbvex4v_5 fcbvex4v_6 ecbvex4v_0 2exbidv cbvex2v fcbvex4v_1 fcbvex4v_6 wex fcbvex4v_5 wex fcbvex4v_2 fcbvex4v_10 wex fcbvex4v_9 wex fcbvex4v_7 fcbvex4v_8 fcbvex4v_1 fcbvex4v_2 fcbvex4v_5 fcbvex4v_6 fcbvex4v_9 fcbvex4v_10 ecbvex4v_1 cbvex2v 2exbii bitri $.
$}
$( Implicit substitution of ` y ` for ` x ` into a theorem.  (Contributed
       by NM, 20-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$d x ps $.
	fchvarv_0 $f wff ph $.
	fchvarv_1 $f wff ps $.
	fchvarv_2 $f set x $.
	fchvarv_3 $f set y $.
	echvarv_0 $e |- ( x = y -> ( ph <-> ps ) ) $.
	echvarv_1 $e |- ph $.
	chvarv $p |- ps $= fchvarv_0 fchvarv_1 fchvarv_2 fchvarv_0 fchvarv_1 fchvarv_2 fchvarv_3 echvarv_0 spv echvarv_1 mpg $.
$}
$( When the class variables in definition ~ df-clel are replaced with set
       variables, this theorem of predicate calculus is the result.  This
       theorem provides part of the justification for the consistency of that
       definition, which "overloads" the set variables in ~ wel with the class
       variables in ~ wcel .  Note:  This proof is referenced on the Metamath
       Proof Explorer Home Page and shouldn't be changed.  (Contributed by NM,
       28-Jan-2004.)  (Proof modification is discouraged.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$d x z $.
	$d y z $.
	fcleljust_0 $f set x $.
	fcleljust_1 $f set y $.
	fcleljust_2 $f set z $.
	cleljust $p |- ( x e. y <-> E. z ( z = x /\ z e. y ) ) $= fcleljust_2 sup_set_class fcleljust_0 sup_set_class wceq fcleljust_2 sup_set_class fcleljust_1 sup_set_class wcel wa fcleljust_2 wex fcleljust_0 sup_set_class fcleljust_1 sup_set_class wcel fcleljust_2 sup_set_class fcleljust_1 sup_set_class wcel fcleljust_0 sup_set_class fcleljust_1 sup_set_class wcel fcleljust_2 fcleljust_0 fcleljust_0 sup_set_class fcleljust_1 sup_set_class wcel fcleljust_2 ax-17 fcleljust_2 fcleljust_0 fcleljust_1 elequ1 equsexh bicomi $.
$}
$( When the class variables in definition ~ df-clel are replaced with set
       variables, this theorem of predicate calculus is the result.  This
       theorem provides part of the justification for the consistency of that
       definition, which "overloads" the set variables in ~ wel with the class
       variables in ~ wcel .  (Contributed by NM, 28-Jan-2004.)  (Revised by
       Mario Carneiro, 21-Dec-2016.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$d x z $.
	$d y z $.
	fcleljustALT_0 $f set x $.
	fcleljustALT_1 $f set y $.
	fcleljustALT_2 $f set z $.
	cleljustALT $p |- ( x e. y <-> E. z ( z = x /\ z e. y ) ) $= fcleljustALT_2 sup_set_class fcleljustALT_0 sup_set_class wceq fcleljustALT_2 sup_set_class fcleljustALT_1 sup_set_class wcel wa fcleljustALT_2 wex fcleljustALT_0 sup_set_class fcleljustALT_1 sup_set_class wcel fcleljustALT_2 sup_set_class fcleljustALT_1 sup_set_class wcel fcleljustALT_0 sup_set_class fcleljustALT_1 sup_set_class wcel fcleljustALT_2 fcleljustALT_0 fcleljustALT_0 sup_set_class fcleljustALT_1 sup_set_class wcel fcleljustALT_2 nfv fcleljustALT_2 fcleljustALT_0 fcleljustALT_1 elequ1 equsex bicomi $.
$}
$( This theorem can be used to eliminate a distinct variable restriction on
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
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v z $.
	$d z ps $.
	fdvelim_0 $f wff ph $.
	fdvelim_1 $f wff ps $.
	fdvelim_2 $f set x $.
	fdvelim_3 $f set y $.
	fdvelim_4 $f set z $.
	edvelim_0 $e |- ( ph -> A. x ph ) $.
	edvelim_1 $e |- ( z = y -> ( ph <-> ps ) ) $.
	dvelim $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $= fdvelim_0 fdvelim_1 fdvelim_2 fdvelim_3 fdvelim_4 edvelim_0 fdvelim_1 fdvelim_4 ax-17 edvelim_1 dvelimh $.
$}
$( Version of ~ dvelim using "not free" notation.  (Contributed by Mario
       Carneiro, 9-Oct-2016.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v z $.
	$d z ps $.
	fdvelimnf_0 $f wff ph $.
	fdvelimnf_1 $f wff ps $.
	fdvelimnf_2 $f set x $.
	fdvelimnf_3 $f set y $.
	fdvelimnf_4 $f set z $.
	edvelimnf_0 $e |- F/ x ph $.
	edvelimnf_1 $e |- ( z = y -> ( ph <-> ps ) ) $.
	dvelimnf $p |- ( -. A. x x = y -> F/ x ps ) $= fdvelimnf_0 fdvelimnf_1 fdvelimnf_2 fdvelimnf_3 fdvelimnf_4 edvelimnf_0 fdvelimnf_1 fdvelimnf_4 nfv edvelimnf_1 dvelimf $.
$}
$( Quantifier introduction when one pair of variables is distinct.
       (Contributed by NM, 2-Jan-2002.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d w z x $.
	$d w y $.
	idveeq1_0 $f set w $.
	fdveeq1_0 $f set x $.
	fdveeq1_1 $f set y $.
	fdveeq1_2 $f set z $.
	dveeq1 $p |- ( -. A. x x = y -> ( y = z -> A. x y = z ) ) $= idveeq1_0 sup_set_class fdveeq1_2 sup_set_class wceq fdveeq1_1 sup_set_class fdveeq1_2 sup_set_class wceq fdveeq1_0 fdveeq1_1 idveeq1_0 idveeq1_0 fdveeq1_1 fdveeq1_2 equequ1 dvelimv $.
$}
$( Quantifier introduction when one pair of variables is distinct.
       (Contributed by NM, 2-Jan-2002.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d w z x $.
	$d w y $.
	idveel1_0 $f set w $.
	fdveel1_0 $f set x $.
	fdveel1_1 $f set y $.
	fdveel1_2 $f set z $.
	dveel1 $p |- ( -. A. x x = y -> ( y e. z -> A. x y e. z ) ) $= idveel1_0 sup_set_class fdveel1_2 sup_set_class wcel fdveel1_1 sup_set_class fdveel1_2 sup_set_class wcel fdveel1_0 fdveel1_1 idveel1_0 idveel1_0 fdveel1_1 fdveel1_2 elequ1 dvelimv $.
$}
$( Quantifier introduction when one pair of variables is distinct.
       (Contributed by NM, 2-Jan-2002.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d w z x $.
	$d w y $.
	idveel2_0 $f set w $.
	fdveel2_0 $f set x $.
	fdveel2_1 $f set y $.
	fdveel2_2 $f set z $.
	dveel2 $p |- ( -. A. x x = y -> ( z e. y -> A. x z e. y ) ) $= fdveel2_2 sup_set_class idveel2_0 sup_set_class wcel fdveel2_2 sup_set_class fdveel2_1 sup_set_class wcel fdveel2_0 fdveel2_1 idveel2_0 idveel2_0 fdveel2_1 fdveel2_2 elequ2 dvelimv $.
$}
$( ` w ` is dummy. $)
$( Axiom ~ ax-15 is redundant if we assume ~ ax-17 .  Remark 9.6 in
       [Megill] p. 448 (p. 16 of the preprint), regarding axiom scheme C14'.

       Note that ` w ` is a dummy variable introduced in the proof.  On the web
       page, it is implicitly assumed to be distinct from all other variables.
       (This is made explicit in the database file set.mm).  Its purpose is to
       satisfy the distinct variable requirements of ~ dveel2 and ~ ax-17 .  By
       the end of the proof it has vanished, and the final theorem has no
       distinct variable requirements.  (Contributed by NM, 29-Jun-1995.)
       (Proof modification is discouraged.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d w y $.
	$d w z $.
	$d w x $.
	iax15_0 $f set w $.
	fax15_0 $f set x $.
	fax15_1 $f set y $.
	fax15_2 $f set z $.
	ax15 $p |- ( -. A. z z = x -> ( -. A. z z = y -> ( x e. y -> A. z x e. y ) ) ) $= fax15_2 sup_set_class fax15_0 sup_set_class wceq fax15_2 wal wn fax15_2 sup_set_class fax15_1 sup_set_class wceq fax15_2 wal wn fax15_0 sup_set_class fax15_1 sup_set_class wcel fax15_0 sup_set_class fax15_1 sup_set_class wcel fax15_2 wal fax15_2 sup_set_class fax15_0 sup_set_class wceq fax15_2 wal wn fax15_2 sup_set_class fax15_1 sup_set_class wceq fax15_2 wal wn fax15_0 sup_set_class fax15_1 sup_set_class wcel wi fax15_2 sup_set_class fax15_1 sup_set_class wceq fax15_2 wal wn fax15_0 sup_set_class fax15_1 sup_set_class wcel wi fax15_2 wal fax15_2 sup_set_class fax15_1 sup_set_class wceq fax15_2 wal wn fax15_0 sup_set_class fax15_1 sup_set_class wcel fax15_2 wal wi fax15_2 sup_set_class fax15_1 sup_set_class wceq fax15_2 wal wn iax15_0 sup_set_class fax15_1 sup_set_class wcel wi fax15_2 sup_set_class fax15_1 sup_set_class wceq fax15_2 wal wn fax15_0 sup_set_class fax15_1 sup_set_class wcel wi fax15_2 fax15_0 iax15_0 fax15_2 sup_set_class fax15_1 sup_set_class wceq fax15_2 wal wn iax15_0 sup_set_class fax15_1 sup_set_class wcel fax15_2 fax15_2 sup_set_class fax15_1 sup_set_class wceq fax15_2 hbn1 fax15_2 fax15_1 iax15_0 dveel2 hbim1 iax15_0 sup_set_class fax15_0 sup_set_class wceq iax15_0 sup_set_class fax15_1 sup_set_class wcel fax15_0 sup_set_class fax15_1 sup_set_class wcel fax15_2 sup_set_class fax15_1 sup_set_class wceq fax15_2 wal wn iax15_0 fax15_0 fax15_1 elequ1 imbi2d dvelim fax15_2 sup_set_class fax15_1 sup_set_class wceq fax15_2 wal wn fax15_0 sup_set_class fax15_1 sup_set_class wcel fax15_2 fax15_2 sup_set_class fax15_1 sup_set_class wceq fax15_2 wal fax15_2 fax15_2 sup_set_class fax15_1 sup_set_class wceq fax15_2 nfa1 nfn 19.21 syl6ib pm2.86d $.
$}
$( Formula-building lemma for use with the Distinctor Reduction Theorem.
     Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).  (Contributed
     by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	fdrsb1_0 $f wff ph $.
	fdrsb1_1 $f set x $.
	fdrsb1_2 $f set y $.
	fdrsb1_3 $f set z $.
	drsb1 $p |- ( A. x x = y -> ( [ z / x ] ph <-> [ z / y ] ph ) ) $= fdrsb1_1 sup_set_class fdrsb1_2 sup_set_class wceq fdrsb1_1 wal fdrsb1_1 sup_set_class fdrsb1_3 sup_set_class wceq fdrsb1_0 wi fdrsb1_1 sup_set_class fdrsb1_3 sup_set_class wceq fdrsb1_0 wa fdrsb1_1 wex wa fdrsb1_2 sup_set_class fdrsb1_3 sup_set_class wceq fdrsb1_0 wi fdrsb1_2 sup_set_class fdrsb1_3 sup_set_class wceq fdrsb1_0 wa fdrsb1_2 wex wa fdrsb1_0 fdrsb1_1 fdrsb1_3 wsb fdrsb1_0 fdrsb1_2 fdrsb1_3 wsb fdrsb1_1 sup_set_class fdrsb1_2 sup_set_class wceq fdrsb1_1 wal fdrsb1_1 sup_set_class fdrsb1_3 sup_set_class wceq fdrsb1_0 wi fdrsb1_2 sup_set_class fdrsb1_3 sup_set_class wceq fdrsb1_0 wi fdrsb1_1 sup_set_class fdrsb1_3 sup_set_class wceq fdrsb1_0 wa fdrsb1_1 wex fdrsb1_2 sup_set_class fdrsb1_3 sup_set_class wceq fdrsb1_0 wa fdrsb1_2 wex fdrsb1_1 sup_set_class fdrsb1_2 sup_set_class wceq fdrsb1_1 wal fdrsb1_1 sup_set_class fdrsb1_3 sup_set_class wceq fdrsb1_2 sup_set_class fdrsb1_3 sup_set_class wceq fdrsb1_0 fdrsb1_1 sup_set_class fdrsb1_2 sup_set_class wceq fdrsb1_1 sup_set_class fdrsb1_3 sup_set_class wceq fdrsb1_2 sup_set_class fdrsb1_3 sup_set_class wceq wb fdrsb1_1 fdrsb1_1 fdrsb1_2 fdrsb1_3 equequ1 sps imbi1d fdrsb1_1 sup_set_class fdrsb1_3 sup_set_class wceq fdrsb1_0 wa fdrsb1_2 sup_set_class fdrsb1_3 sup_set_class wceq fdrsb1_0 wa fdrsb1_1 fdrsb1_2 fdrsb1_1 sup_set_class fdrsb1_2 sup_set_class wceq fdrsb1_1 wal fdrsb1_1 sup_set_class fdrsb1_3 sup_set_class wceq fdrsb1_2 sup_set_class fdrsb1_3 sup_set_class wceq fdrsb1_0 fdrsb1_1 sup_set_class fdrsb1_2 sup_set_class wceq fdrsb1_1 sup_set_class fdrsb1_3 sup_set_class wceq fdrsb1_2 sup_set_class fdrsb1_3 sup_set_class wceq wb fdrsb1_1 fdrsb1_1 fdrsb1_2 fdrsb1_3 equequ1 sps anbi1d drex1 anbi12d fdrsb1_0 fdrsb1_1 fdrsb1_3 df-sb fdrsb1_0 fdrsb1_2 fdrsb1_3 df-sb 3bitr4g $.
$}
$( One direction of a simplified definition of substitution.  (Contributed by
     NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	fsb2_0 $f wff ph $.
	fsb2_1 $f set x $.
	fsb2_2 $f set y $.
	sb2 $p |- ( A. x ( x = y -> ph ) -> [ y / x ] ph ) $= fsb2_1 sup_set_class fsb2_2 sup_set_class wceq fsb2_0 wi fsb2_1 wal fsb2_1 sup_set_class fsb2_2 sup_set_class wceq fsb2_0 wi fsb2_1 sup_set_class fsb2_2 sup_set_class wceq fsb2_0 wa fsb2_1 wex fsb2_0 fsb2_1 fsb2_2 wsb fsb2_1 sup_set_class fsb2_2 sup_set_class wceq fsb2_0 wi fsb2_1 sp fsb2_0 fsb2_1 fsb2_2 equs4 fsb2_0 fsb2_1 fsb2_2 df-sb sylanbrc $.
$}
$( The specialization axiom of standard predicate calculus.  It states that
     if a statement ` ph ` holds for all ` x ` , then it also holds for the
     specific case of ` y ` (properly) substituted for ` x ` .  Translated to
     traditional notation, it can be read:  " ` A. x ph ( x ) -> ph ( y ) ` ,
     provided that ` y ` is free for ` x ` in ` ph ( x ) ` ."  Axiom 4 of
     [Mendelson] p. 69.  See also ~ spsbc and ~ rspsbc .  (Contributed by NM,
     5-Aug-1993.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	fstdpc4_0 $f wff ph $.
	fstdpc4_1 $f set x $.
	fstdpc4_2 $f set y $.
	stdpc4 $p |- ( A. x ph -> [ y / x ] ph ) $= fstdpc4_0 fstdpc4_1 wal fstdpc4_1 sup_set_class fstdpc4_2 sup_set_class wceq fstdpc4_0 wi fstdpc4_1 wal fstdpc4_0 fstdpc4_1 fstdpc4_2 wsb fstdpc4_0 fstdpc4_1 sup_set_class fstdpc4_2 sup_set_class wceq fstdpc4_0 wi fstdpc4_1 fstdpc4_0 fstdpc4_1 sup_set_class fstdpc4_2 sup_set_class wceq ax-1 alimi fstdpc4_0 fstdpc4_1 fstdpc4_2 sb2 syl $.
$}
$( Substitution has no effect on a non-free variable.  (Contributed by NM,
     30-May-2009.)  (Revised by Mario Carneiro, 12-Oct-2016.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	fsbft_0 $f wff ph $.
	fsbft_1 $f set x $.
	fsbft_2 $f set y $.
	sbft $p |- ( F/ x ph -> ( [ y / x ] ph <-> ph ) ) $= fsbft_0 fsbft_1 wnf fsbft_0 fsbft_1 fsbft_2 wsb fsbft_0 fsbft_0 fsbft_1 fsbft_2 wsb fsbft_1 sup_set_class fsbft_2 sup_set_class wceq fsbft_0 wa fsbft_1 wex fsbft_0 fsbft_1 wnf fsbft_0 fsbft_0 fsbft_1 fsbft_2 sb1 fsbft_0 fsbft_1 wnf fsbft_1 sup_set_class fsbft_2 sup_set_class wceq fsbft_0 wa fsbft_0 wi fsbft_1 wal fsbft_1 sup_set_class fsbft_2 sup_set_class wceq fsbft_0 wa fsbft_1 wex fsbft_0 wi fsbft_1 sup_set_class fsbft_2 sup_set_class wceq fsbft_0 wa fsbft_0 wi fsbft_1 fsbft_1 sup_set_class fsbft_2 sup_set_class wceq fsbft_0 simpr ax-gen fsbft_1 sup_set_class fsbft_2 sup_set_class wceq fsbft_0 wa fsbft_0 fsbft_1 19.23t mpbii syl5 fsbft_0 fsbft_1 wnf fsbft_0 fsbft_0 fsbft_1 wal fsbft_0 fsbft_1 fsbft_2 wsb fsbft_0 fsbft_1 nfr fsbft_0 fsbft_1 fsbft_2 stdpc4 syl6 impbid $.
$}
$( Substitution for a variable not free in a wff does not affect it.
       (Contributed by NM, 5-Aug-1993.)  (Revised by Mario Carneiro,
       4-Oct-2016.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	fsbf_0 $f wff ph $.
	fsbf_1 $f set x $.
	fsbf_2 $f set y $.
	esbf_0 $e |- F/ x ph $.
	sbf $p |- ( [ y / x ] ph <-> ph ) $= fsbf_0 fsbf_1 wnf fsbf_0 fsbf_1 fsbf_2 wsb fsbf_0 wb esbf_0 fsbf_0 fsbf_1 fsbf_2 sbft ax-mp $.
$}
$( Substitution for a variable not free in a wff does not affect it.
       (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	fsbh_0 $f wff ph $.
	fsbh_1 $f set x $.
	fsbh_2 $f set y $.
	esbh_0 $e |- ( ph -> A. x ph ) $.
	sbh $p |- ( [ y / x ] ph <-> ph ) $= fsbh_0 fsbh_1 fsbh_2 fsbh_0 fsbh_1 esbh_0 nfi sbf $.
$}
$( Substitution has no effect on a bound variable.  (Contributed by NM,
     1-Jul-2005.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	fsbf2_0 $f wff ph $.
	fsbf2_1 $f set x $.
	fsbf2_2 $f set y $.
	sbf2 $p |- ( [ y / x ] A. x ph <-> A. x ph ) $= fsbf2_0 fsbf2_1 wal fsbf2_1 fsbf2_2 fsbf2_0 fsbf2_1 nfa1 sbf $.
$}
$( Equivalence involving substitution for a variable not free.
       (Contributed by NM, 5-Aug-1993.)  (Revised by Mario Carneiro,
       4-Oct-2016.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	fsb6x_0 $f wff ph $.
	fsb6x_1 $f set x $.
	fsb6x_2 $f set y $.
	esb6x_0 $e |- F/ x ph $.
	sb6x $p |- ( [ y / x ] ph <-> A. x ( x = y -> ph ) ) $= fsb6x_0 fsb6x_1 fsb6x_2 wsb fsb6x_0 fsb6x_1 sup_set_class fsb6x_2 sup_set_class wceq fsb6x_0 wi fsb6x_1 wal fsb6x_0 fsb6x_1 fsb6x_2 esb6x_0 sbf fsb6x_0 fsb6x_0 fsb6x_1 fsb6x_2 esb6x_0 fsb6x_1 sup_set_class fsb6x_2 sup_set_class wceq fsb6x_0 biidd equsal bitr4i $.
$}
$( If ` x ` is not free in ` ph ` , it is not free in ` [ y / x ] ph ` .
       (Contributed by Mario Carneiro, 11-Aug-2016.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	fnfs1f_0 $f wff ph $.
	fnfs1f_1 $f set x $.
	fnfs1f_2 $f set y $.
	enfs1f_0 $e |- F/ x ph $.
	nfs1f $p |- F/ x [ y / x ] ph $= fnfs1f_0 fnfs1f_1 fnfs1f_2 wsb fnfs1f_0 fnfs1f_1 fnfs1f_0 fnfs1f_1 fnfs1f_2 enfs1f_0 sbf enfs1f_0 nfxfr $.
$}
$( Substitution does not change an identical variable specifier.
     (Contributed by NM, 5-Aug-1993.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	fsbequ5_0 $f set x $.
	fsbequ5_1 $f set y $.
	fsbequ5_2 $f set z $.
	fsbequ5_3 $f set w $.
	sbequ5 $p |- ( [ w / z ] A. x x = y <-> A. x x = y ) $= fsbequ5_0 sup_set_class fsbequ5_1 sup_set_class wceq fsbequ5_0 wal fsbequ5_2 fsbequ5_3 fsbequ5_0 fsbequ5_1 fsbequ5_2 nfae sbf $.
$}
$( Substitution does not change a distinctor.  (Contributed by NM,
     5-Aug-1993.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	fsbequ6_0 $f set x $.
	fsbequ6_1 $f set y $.
	fsbequ6_2 $f set z $.
	fsbequ6_3 $f set w $.
	sbequ6 $p |- ( [ w / z ] -. A. x x = y <-> -. A. x x = y ) $= fsbequ6_0 sup_set_class fsbequ6_1 sup_set_class wceq fsbequ6_0 wal wn fsbequ6_2 fsbequ6_3 fsbequ6_0 fsbequ6_1 fsbequ6_2 nfnae sbf $.
$}
$( A substitution into a theorem remains true.  (See ~ chvar and ~ chvarv
       for versions using implicit substitution.)  (Contributed by NM,
       21-Jan-2004.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	fsbt_0 $f wff ph $.
	fsbt_1 $f set x $.
	fsbt_2 $f set y $.
	esbt_0 $e |- ph $.
	sbt $p |- [ y / x ] ph $= fsbt_0 fsbt_1 fsbt_2 wsb fsbt_0 esbt_0 fsbt_0 fsbt_1 fsbt_2 fsbt_0 fsbt_1 esbt_0 nfth sbf mpbir $.
$}
$( Substitution applied to an atomic wff.  (Contributed by NM,
     5-Aug-1993.) $)
${
	$v x $.
	$v y $.
	fequsb1_0 $f set x $.
	fequsb1_1 $f set y $.
	equsb1 $p |- [ y / x ] x = y $= fequsb1_0 sup_set_class fequsb1_1 sup_set_class wceq fequsb1_0 sup_set_class fequsb1_1 sup_set_class wceq wi fequsb1_0 sup_set_class fequsb1_1 sup_set_class wceq fequsb1_0 fequsb1_1 wsb fequsb1_0 fequsb1_0 sup_set_class fequsb1_1 sup_set_class wceq fequsb1_0 fequsb1_1 sb2 fequsb1_0 sup_set_class fequsb1_1 sup_set_class wceq id mpg $.
$}
$( Substitution applied to an atomic wff.  (Contributed by NM,
     5-Aug-1993.) $)
${
	$v x $.
	$v y $.
	fequsb2_0 $f set x $.
	fequsb2_1 $f set y $.
	equsb2 $p |- [ y / x ] y = x $= fequsb2_0 sup_set_class fequsb2_1 sup_set_class wceq fequsb2_1 sup_set_class fequsb2_0 sup_set_class wceq wi fequsb2_1 sup_set_class fequsb2_0 sup_set_class wceq fequsb2_0 fequsb2_1 wsb fequsb2_0 fequsb2_1 sup_set_class fequsb2_0 sup_set_class wceq fequsb2_0 fequsb2_1 sb2 fequsb2_0 fequsb2_1 equcomi mpg $.
$}
$( Conversion of implicit substitution to explicit substitution (deduction
       version of ~ sbie ).  (Contributed by NM, 30-Jun-1994.)  (Revised by
       Mario Carneiro, 4-Oct-2016.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	$v y $.
	fsbied_0 $f wff ph $.
	fsbied_1 $f wff ps $.
	fsbied_2 $f wff ch $.
	fsbied_3 $f set x $.
	fsbied_4 $f set y $.
	esbied_0 $e |- F/ x ph $.
	esbied_1 $e |- ( ph -> F/ x ch ) $.
	esbied_2 $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
	sbied $p |- ( ph -> ( [ y / x ] ps <-> ch ) ) $= fsbied_0 fsbied_1 fsbied_3 fsbied_4 wsb fsbied_2 fsbied_0 fsbied_1 fsbied_3 fsbied_4 wsb fsbied_2 fsbied_3 wex fsbied_2 fsbied_1 fsbied_3 fsbied_4 wsb fsbied_3 sup_set_class fsbied_4 sup_set_class wceq fsbied_1 wa fsbied_3 wex fsbied_0 fsbied_2 fsbied_3 wex fsbied_1 fsbied_3 fsbied_4 sb1 fsbied_0 fsbied_3 sup_set_class fsbied_4 sup_set_class wceq fsbied_1 wa fsbied_2 fsbied_3 esbied_0 fsbied_0 fsbied_3 sup_set_class fsbied_4 sup_set_class wceq fsbied_1 fsbied_2 fsbied_0 fsbied_3 sup_set_class fsbied_4 sup_set_class wceq fsbied_1 fsbied_2 wb fsbied_1 fsbied_2 wi esbied_2 fsbied_1 fsbied_2 bi1 syl6 imp3a eximd syl5 fsbied_2 fsbied_0 fsbied_3 esbied_1 19.9d syld fsbied_0 fsbied_2 fsbied_2 fsbied_3 wal fsbied_1 fsbied_3 fsbied_4 wsb fsbied_0 fsbied_2 fsbied_3 esbied_1 nfrd fsbied_0 fsbied_2 fsbied_3 wal fsbied_3 sup_set_class fsbied_4 sup_set_class wceq fsbied_1 wi fsbied_3 wal fsbied_1 fsbied_3 fsbied_4 wsb fsbied_0 fsbied_2 fsbied_3 sup_set_class fsbied_4 sup_set_class wceq fsbied_1 wi fsbied_3 esbied_0 fsbied_0 fsbied_3 sup_set_class fsbied_4 sup_set_class wceq fsbied_2 fsbied_1 fsbied_0 fsbied_3 sup_set_class fsbied_4 sup_set_class wceq fsbied_1 fsbied_2 wb fsbied_2 fsbied_1 wi esbied_2 fsbied_1 fsbied_2 bi2 syl6 com23 alimd fsbied_1 fsbied_3 fsbied_4 sb2 syl6 syld impbid $.
$}
$( Conversion of implicit substitution to explicit substitution (deduction
       version of ~ sbie ).  (Contributed by NM, 7-Jan-2017.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	$v y $.
	$d x ph $.
	$d x ch $.
	fsbiedv_0 $f wff ph $.
	fsbiedv_1 $f wff ps $.
	fsbiedv_2 $f wff ch $.
	fsbiedv_3 $f set x $.
	fsbiedv_4 $f set y $.
	esbiedv_0 $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
	sbiedv $p |- ( ph -> ( [ y / x ] ps <-> ch ) ) $= fsbiedv_0 fsbiedv_1 fsbiedv_2 fsbiedv_3 fsbiedv_4 fsbiedv_0 fsbiedv_3 nfv fsbiedv_0 fsbiedv_2 fsbiedv_3 nfvd fsbiedv_0 fsbiedv_3 sup_set_class fsbiedv_4 sup_set_class wceq fsbiedv_1 fsbiedv_2 wb esbiedv_0 ex sbied $.
$}
$( Conversion of implicit substitution to explicit substitution.
       (Contributed by NM, 30-Jun-1994.)  (Revised by Mario Carneiro,
       4-Oct-2016.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	fsbie_0 $f wff ph $.
	fsbie_1 $f wff ps $.
	fsbie_2 $f set x $.
	fsbie_3 $f set y $.
	esbie_0 $e |- F/ x ps $.
	esbie_1 $e |- ( x = y -> ( ph <-> ps ) ) $.
	sbie $p |- ( [ y / x ] ph <-> ps ) $= fsbie_0 fsbie_2 fsbie_3 wsb fsbie_1 wb wtru fsbie_0 fsbie_1 fsbie_2 fsbie_3 fsbie_2 nftru fsbie_1 fsbie_2 wnf wtru esbie_0 a1i fsbie_2 sup_set_class fsbie_3 sup_set_class wceq fsbie_0 fsbie_1 wb wi wtru esbie_1 a1i sbied trud $.
$}
$( Equivalence for substitution when ` y ` is not free in ` ph ` .
       (Contributed by NM, 5-Aug-1993.)  (Revised by Mario Carneiro,
       4-Oct-2016.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	fsb6f_0 $f wff ph $.
	fsb6f_1 $f set x $.
	fsb6f_2 $f set y $.
	esb6f_0 $e |- F/ y ph $.
	sb6f $p |- ( [ y / x ] ph <-> A. x ( x = y -> ph ) ) $= fsb6f_0 fsb6f_1 fsb6f_2 wsb fsb6f_1 sup_set_class fsb6f_2 sup_set_class wceq fsb6f_0 wi fsb6f_1 wal fsb6f_0 fsb6f_1 fsb6f_2 wsb fsb6f_0 fsb6f_2 wal fsb6f_1 fsb6f_2 wsb fsb6f_1 sup_set_class fsb6f_2 sup_set_class wceq fsb6f_0 wi fsb6f_1 wal fsb6f_0 fsb6f_0 fsb6f_2 wal fsb6f_1 fsb6f_2 fsb6f_0 fsb6f_2 esb6f_0 nfri sbimi fsb6f_0 fsb6f_1 fsb6f_2 sb4a syl fsb6f_0 fsb6f_1 fsb6f_2 sb2 impbii $.
$}
$( Equivalence for substitution when ` y ` is not free in ` ph ` .
       (Contributed by NM, 5-Aug-1993.)  (Revised by Mario Carneiro,
       4-Oct-2016.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	fsb5f_0 $f wff ph $.
	fsb5f_1 $f set x $.
	fsb5f_2 $f set y $.
	esb5f_0 $e |- F/ y ph $.
	sb5f $p |- ( [ y / x ] ph <-> E. x ( x = y /\ ph ) ) $= fsb5f_0 fsb5f_1 fsb5f_2 wsb fsb5f_1 sup_set_class fsb5f_2 sup_set_class wceq fsb5f_0 wi fsb5f_1 wal fsb5f_1 sup_set_class fsb5f_2 sup_set_class wceq fsb5f_0 wa fsb5f_1 wex fsb5f_0 fsb5f_1 fsb5f_2 esb5f_0 sb6f fsb5f_0 fsb5f_1 fsb5f_2 esb5f_0 equs45f bitr4i $.
$}
$( Special case of a bound-variable hypothesis builder for substitution.
     (Contributed by NM, 2-Feb-2007.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	fhbsb2a_0 $f wff ph $.
	fhbsb2a_1 $f set x $.
	fhbsb2a_2 $f set y $.
	hbsb2a $p |- ( [ y / x ] A. y ph -> A. x [ y / x ] ph ) $= fhbsb2a_0 fhbsb2a_2 wal fhbsb2a_1 fhbsb2a_2 wsb fhbsb2a_1 sup_set_class fhbsb2a_2 sup_set_class wceq fhbsb2a_0 wi fhbsb2a_1 wal fhbsb2a_0 fhbsb2a_1 fhbsb2a_2 wsb fhbsb2a_1 wal fhbsb2a_0 fhbsb2a_1 fhbsb2a_2 sb4a fhbsb2a_1 sup_set_class fhbsb2a_2 sup_set_class wceq fhbsb2a_0 wi fhbsb2a_0 fhbsb2a_1 fhbsb2a_2 wsb fhbsb2a_1 fhbsb2a_0 fhbsb2a_1 fhbsb2a_2 sb2 a5i syl $.
$}
$( Special case of a bound-variable hypothesis builder for substitution.
     (Contributed by NM, 2-Feb-2007.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	fhbsb2e_0 $f wff ph $.
	fhbsb2e_1 $f set x $.
	fhbsb2e_2 $f set y $.
	hbsb2e $p |- ( [ y / x ] ph -> A. x [ y / x ] E. y ph ) $= fhbsb2e_0 fhbsb2e_1 fhbsb2e_2 wsb fhbsb2e_1 sup_set_class fhbsb2e_2 sup_set_class wceq fhbsb2e_0 fhbsb2e_2 wex wi fhbsb2e_1 wal fhbsb2e_0 fhbsb2e_2 wex fhbsb2e_1 fhbsb2e_2 wsb fhbsb2e_1 wal fhbsb2e_0 fhbsb2e_1 fhbsb2e_2 sb4e fhbsb2e_1 sup_set_class fhbsb2e_2 sup_set_class wceq fhbsb2e_0 fhbsb2e_2 wex wi fhbsb2e_0 fhbsb2e_2 wex fhbsb2e_1 fhbsb2e_2 wsb fhbsb2e_1 fhbsb2e_0 fhbsb2e_2 wex fhbsb2e_1 fhbsb2e_2 sb2 a5i syl $.
$}
$( If ` y ` is not free in ` ph ` , ` x ` is not free in
       ` [ y / x ] ph ` .  (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	fhbsb3_0 $f wff ph $.
	fhbsb3_1 $f set x $.
	fhbsb3_2 $f set y $.
	ehbsb3_0 $e |- ( ph -> A. y ph ) $.
	hbsb3 $p |- ( [ y / x ] ph -> A. x [ y / x ] ph ) $= fhbsb3_0 fhbsb3_1 fhbsb3_2 wsb fhbsb3_0 fhbsb3_2 wal fhbsb3_1 fhbsb3_2 wsb fhbsb3_0 fhbsb3_1 fhbsb3_2 wsb fhbsb3_1 wal fhbsb3_0 fhbsb3_0 fhbsb3_2 wal fhbsb3_1 fhbsb3_2 ehbsb3_0 sbimi fhbsb3_0 fhbsb3_1 fhbsb3_2 hbsb2a syl $.
$}
$( If ` y ` is not free in ` ph ` , ` x ` is not free in
       ` [ y / x ] ph ` .  (Contributed by Mario Carneiro, 11-Aug-2016.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	fnfs1_0 $f wff ph $.
	fnfs1_1 $f set x $.
	fnfs1_2 $f set y $.
	enfs1_0 $e |- F/ y ph $.
	nfs1 $p |- F/ x [ y / x ] ph $= fnfs1_0 fnfs1_1 fnfs1_2 wsb fnfs1_1 fnfs1_0 fnfs1_1 fnfs1_2 fnfs1_0 fnfs1_2 enfs1_0 nfri hbsb3 nfi $.
$}
$( Proof of older axiom ~ ax-16 .  (Contributed by NM, 8-Nov-2006.)
       (Revised by NM, 22-Sep-2017.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$d x y $.
	fax16_0 $f wff ph $.
	fax16_1 $f set x $.
	fax16_2 $f set y $.
	ax16 $p |- ( A. x x = y -> ( ph -> A. x ph ) ) $= fax16_0 fax16_1 fax16_2 fax16_1 a16g $.
$}
$( Inference with ~ ax16 as its conclusion.  (Contributed by NM,
       20-May-2008.)  (Proof modification is discouraged.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v z $.
	$d x y z $.
	$d z ph $.
	fax16i_0 $f wff ph $.
	fax16i_1 $f wff ps $.
	fax16i_2 $f set x $.
	fax16i_3 $f set y $.
	fax16i_4 $f set z $.
	eax16i_0 $e |- ( x = z -> ( ph <-> ps ) ) $.
	eax16i_1 $e |- ( ps -> A. x ps ) $.
	ax16i $p |- ( A. x x = y -> ( ph -> A. x ph ) ) $= fax16i_2 sup_set_class fax16i_3 sup_set_class wceq fax16i_2 wal fax16i_4 sup_set_class fax16i_3 sup_set_class wceq fax16i_4 wal fax16i_2 sup_set_class fax16i_4 sup_set_class wceq fax16i_4 wal fax16i_0 fax16i_0 fax16i_2 wal wi fax16i_2 sup_set_class fax16i_3 sup_set_class wceq fax16i_4 sup_set_class fax16i_3 sup_set_class wceq fax16i_2 fax16i_4 fax16i_2 sup_set_class fax16i_3 sup_set_class wceq fax16i_4 nfv fax16i_4 sup_set_class fax16i_3 sup_set_class wceq fax16i_2 nfv fax16i_2 fax16i_4 fax16i_3 ax-8 cbv3 fax16i_4 sup_set_class fax16i_3 sup_set_class wceq fax16i_4 wal fax16i_4 sup_set_class fax16i_2 sup_set_class wceq fax16i_4 wal fax16i_2 sup_set_class fax16i_4 sup_set_class wceq fax16i_4 wal fax16i_2 sup_set_class fax16i_3 sup_set_class wceq fax16i_4 sup_set_class fax16i_3 sup_set_class wceq fax16i_4 wal fax16i_4 sup_set_class fax16i_2 sup_set_class wceq fax16i_4 wal fax16i_4 sup_set_class fax16i_3 sup_set_class wceq fax16i_2 sup_set_class fax16i_3 sup_set_class wceq fax16i_4 fax16i_2 fax16i_4 fax16i_2 fax16i_3 ax-8 spimv fax16i_2 sup_set_class fax16i_3 sup_set_class wceq fax16i_4 sup_set_class fax16i_3 sup_set_class wceq fax16i_4 sup_set_class fax16i_2 sup_set_class wceq fax16i_4 fax16i_2 sup_set_class fax16i_3 sup_set_class wceq fax16i_3 sup_set_class fax16i_2 sup_set_class wceq fax16i_4 sup_set_class fax16i_3 sup_set_class wceq fax16i_4 sup_set_class fax16i_2 sup_set_class wceq fax16i_2 fax16i_3 equcomi fax16i_4 sup_set_class fax16i_3 sup_set_class wceq fax16i_3 sup_set_class fax16i_4 sup_set_class wceq fax16i_3 sup_set_class fax16i_2 sup_set_class wceq fax16i_4 sup_set_class fax16i_2 sup_set_class wceq wi fax16i_4 fax16i_3 equcomi fax16i_3 fax16i_4 fax16i_2 ax-8 syl syl5com alimdv mpcom fax16i_4 sup_set_class fax16i_2 sup_set_class wceq fax16i_2 sup_set_class fax16i_4 sup_set_class wceq fax16i_4 fax16i_4 fax16i_2 equcomi alimi syl fax16i_0 fax16i_2 sup_set_class fax16i_4 sup_set_class wceq fax16i_4 wal fax16i_1 fax16i_4 wal fax16i_0 fax16i_2 wal fax16i_0 fax16i_2 sup_set_class fax16i_4 sup_set_class wceq fax16i_1 fax16i_4 fax16i_2 sup_set_class fax16i_4 sup_set_class wceq fax16i_0 fax16i_1 eax16i_0 biimpcd alimdv fax16i_1 fax16i_0 fax16i_4 fax16i_2 fax16i_1 fax16i_2 eax16i_1 nfi fax16i_0 fax16i_4 nfv fax16i_4 sup_set_class fax16i_2 sup_set_class wceq fax16i_2 sup_set_class fax16i_4 sup_set_class wceq fax16i_1 fax16i_0 wi fax16i_4 fax16i_2 equcomi fax16i_2 sup_set_class fax16i_4 sup_set_class wceq fax16i_0 fax16i_1 eax16i_0 biimprd syl cbv3 syl6com 3syl $.
$}
$( Alternate proof of ~ ax16 .  (Contributed by NM, 17-May-2008.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$d x y z $.
	$d z ph $.
	iax16ALT_0 $f set z $.
	fax16ALT_0 $f wff ph $.
	fax16ALT_1 $f set x $.
	fax16ALT_2 $f set y $.
	ax16ALT $p |- ( A. x x = y -> ( ph -> A. x ph ) ) $= fax16ALT_0 fax16ALT_0 fax16ALT_1 iax16ALT_0 wsb fax16ALT_1 fax16ALT_2 iax16ALT_0 fax16ALT_0 fax16ALT_1 iax16ALT_0 sbequ12 fax16ALT_0 fax16ALT_1 iax16ALT_0 fax16ALT_0 iax16ALT_0 ax-17 hbsb3 ax16i $.
$}
$( Alternate proof of ~ ax16 .  (Contributed by NM, 8-Nov-2006.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$d x y $.
	$d z ph $.
	iax16ALT2_0 $f set z $.
	fax16ALT2_0 $f wff ph $.
	fax16ALT2_1 $f set x $.
	fax16ALT2_2 $f set y $.
	ax16ALT2 $p |- ( A. x x = y -> ( ph -> A. x ph ) ) $= fax16ALT2_1 sup_set_class fax16ALT2_2 sup_set_class wceq fax16ALT2_1 wal fax16ALT2_1 sup_set_class iax16ALT2_0 sup_set_class wceq iax16ALT2_0 wal fax16ALT2_0 fax16ALT2_0 fax16ALT2_1 wal wi fax16ALT2_1 fax16ALT2_2 iax16ALT2_0 fax16ALT2_1 iax16ALT2_0 aev fax16ALT2_0 fax16ALT2_1 sup_set_class iax16ALT2_0 sup_set_class wceq iax16ALT2_0 wal fax16ALT2_0 fax16ALT2_1 iax16ALT2_0 wsb iax16ALT2_0 wal fax16ALT2_0 fax16ALT2_1 wal fax16ALT2_0 fax16ALT2_1 sup_set_class iax16ALT2_0 sup_set_class wceq fax16ALT2_0 fax16ALT2_1 iax16ALT2_0 wsb iax16ALT2_0 fax16ALT2_1 sup_set_class iax16ALT2_0 sup_set_class wceq fax16ALT2_0 fax16ALT2_0 fax16ALT2_1 iax16ALT2_0 wsb fax16ALT2_0 fax16ALT2_1 iax16ALT2_0 sbequ12 biimpcd alimdv fax16ALT2_0 fax16ALT2_1 iax16ALT2_0 wsb fax16ALT2_0 iax16ALT2_0 fax16ALT2_1 fax16ALT2_0 fax16ALT2_1 iax16ALT2_0 fax16ALT2_0 iax16ALT2_0 nfv nfs1 fax16ALT2_0 iax16ALT2_0 nfv fax16ALT2_0 iax16ALT2_0 fax16ALT2_1 stdpc7 cbv3 syl6com syl $.
$}
$( A generalization of axiom ~ ax-16 .  Alternate proof of ~ a16g that uses
       ~ df-sb .  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew
       Salmon, 25-May-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$d x y $.
	fa16gALT_0 $f wff ph $.
	fa16gALT_1 $f set x $.
	fa16gALT_2 $f set y $.
	fa16gALT_3 $f set z $.
	a16gALT $p |- ( A. x x = y -> ( ph -> A. z ph ) ) $= fa16gALT_1 sup_set_class fa16gALT_2 sup_set_class wceq fa16gALT_1 wal fa16gALT_3 sup_set_class fa16gALT_1 sup_set_class wceq fa16gALT_3 wal fa16gALT_0 fa16gALT_0 fa16gALT_1 wal fa16gALT_0 fa16gALT_3 wal fa16gALT_1 fa16gALT_2 fa16gALT_3 fa16gALT_3 fa16gALT_1 aev fa16gALT_0 fa16gALT_1 fa16gALT_2 ax16ALT2 fa16gALT_3 sup_set_class fa16gALT_1 sup_set_class wceq fa16gALT_3 wal fa16gALT_0 fa16gALT_3 wal fa16gALT_0 fa16gALT_1 wal fa16gALT_0 fa16gALT_0 fa16gALT_3 fa16gALT_1 fa16gALT_3 sup_set_class fa16gALT_1 sup_set_class wceq fa16gALT_3 wal fa16gALT_0 biidd dral1 biimprd sylsyld $.
$}
$( A generalization of axiom ~ ax-16 .  (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$d x y $.
	fa16gb_0 $f wff ph $.
	fa16gb_1 $f set x $.
	fa16gb_2 $f set y $.
	fa16gb_3 $f set z $.
	a16gb $p |- ( A. x x = y -> ( ph <-> A. z ph ) ) $= fa16gb_1 sup_set_class fa16gb_2 sup_set_class wceq fa16gb_1 wal fa16gb_0 fa16gb_0 fa16gb_3 wal fa16gb_0 fa16gb_1 fa16gb_2 fa16gb_3 a16g fa16gb_0 fa16gb_3 sp impbid1 $.
$}
$( If ~ dtru is false, then there is only one element in the universe, so
       everything satisfies ` F/ ` .  (Contributed by Mario Carneiro,
       7-Oct-2016.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$d x y $.
	fa16nf_0 $f wff ph $.
	fa16nf_1 $f set x $.
	fa16nf_2 $f set y $.
	fa16nf_3 $f set z $.
	a16nf $p |- ( A. x x = y -> F/ z ph ) $= fa16nf_1 sup_set_class fa16nf_2 sup_set_class wceq fa16nf_1 wal fa16nf_0 fa16nf_3 fa16nf_1 fa16nf_2 fa16nf_3 nfae fa16nf_0 fa16nf_1 fa16nf_2 fa16nf_3 a16g nfd $.
$}
$( One direction of a simplified definition of substitution when variables
     are distinct.  (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	fsb3_0 $f wff ph $.
	fsb3_1 $f set x $.
	fsb3_2 $f set y $.
	sb3 $p |- ( -. A. x x = y -> ( E. x ( x = y /\ ph ) -> [ y / x ] ph ) ) $= fsb3_1 sup_set_class fsb3_2 sup_set_class wceq fsb3_1 wal wn fsb3_1 sup_set_class fsb3_2 sup_set_class wceq fsb3_0 wa fsb3_1 wex fsb3_1 sup_set_class fsb3_2 sup_set_class wceq fsb3_0 wi fsb3_1 wal fsb3_0 fsb3_1 fsb3_2 wsb fsb3_0 fsb3_1 fsb3_2 equs5 fsb3_0 fsb3_1 fsb3_2 sb2 syl6 $.
$}
$( One direction of a simplified definition of substitution when variables
     are distinct.  (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	fsb4_0 $f wff ph $.
	fsb4_1 $f set x $.
	fsb4_2 $f set y $.
	sb4 $p |- ( -. A. x x = y -> ( [ y / x ] ph -> A. x ( x = y -> ph ) ) ) $= fsb4_0 fsb4_1 fsb4_2 wsb fsb4_1 sup_set_class fsb4_2 sup_set_class wceq fsb4_0 wa fsb4_1 wex fsb4_1 sup_set_class fsb4_2 sup_set_class wceq fsb4_1 wal wn fsb4_1 sup_set_class fsb4_2 sup_set_class wceq fsb4_0 wi fsb4_1 wal fsb4_0 fsb4_1 fsb4_2 sb1 fsb4_0 fsb4_1 fsb4_2 equs5 syl5 $.
$}
$( Simplified definition of substitution when variables are distinct.
     (Contributed by NM, 27-May-1997.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	fsb4b_0 $f wff ph $.
	fsb4b_1 $f set x $.
	fsb4b_2 $f set y $.
	sb4b $p |- ( -. A. x x = y -> ( [ y / x ] ph <-> A. x ( x = y -> ph ) ) ) $= fsb4b_1 sup_set_class fsb4b_2 sup_set_class wceq fsb4b_1 wal wn fsb4b_0 fsb4b_1 fsb4b_2 wsb fsb4b_1 sup_set_class fsb4b_2 sup_set_class wceq fsb4b_0 wi fsb4b_1 wal fsb4b_0 fsb4b_1 fsb4b_2 sb4 fsb4b_0 fsb4b_1 fsb4b_2 sb2 impbid1 $.
$}
$( An alternate definition of proper substitution that, like ~ df-sb , mixes
     free and bound variables to avoid distinct variable requirements.
     (Contributed by NM, 17-Feb-2005.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	fdfsb2_0 $f wff ph $.
	fdfsb2_1 $f set x $.
	fdfsb2_2 $f set y $.
	dfsb2 $p |- ( [ y / x ] ph <-> ( ( x = y /\ ph ) \/ A. x ( x = y -> ph ) ) ) $= fdfsb2_0 fdfsb2_1 fdfsb2_2 wsb fdfsb2_1 sup_set_class fdfsb2_2 sup_set_class wceq fdfsb2_0 wa fdfsb2_1 sup_set_class fdfsb2_2 sup_set_class wceq fdfsb2_0 wi fdfsb2_1 wal wo fdfsb2_1 sup_set_class fdfsb2_2 sup_set_class wceq fdfsb2_1 wal fdfsb2_0 fdfsb2_1 fdfsb2_2 wsb fdfsb2_1 sup_set_class fdfsb2_2 sup_set_class wceq fdfsb2_0 wa fdfsb2_1 sup_set_class fdfsb2_2 sup_set_class wceq fdfsb2_0 wi fdfsb2_1 wal wo wi fdfsb2_1 sup_set_class fdfsb2_2 sup_set_class wceq fdfsb2_1 wal fdfsb2_1 sup_set_class fdfsb2_2 sup_set_class wceq fdfsb2_0 fdfsb2_1 fdfsb2_2 wsb fdfsb2_0 fdfsb2_1 sup_set_class fdfsb2_2 sup_set_class wceq fdfsb2_0 wa fdfsb2_1 sup_set_class fdfsb2_2 sup_set_class wceq fdfsb2_0 wi fdfsb2_1 wal wo fdfsb2_1 sup_set_class fdfsb2_2 sup_set_class wceq fdfsb2_1 sp fdfsb2_1 sup_set_class fdfsb2_2 sup_set_class wceq fdfsb2_0 fdfsb2_1 fdfsb2_2 wsb fdfsb2_0 wi fdfsb2_1 fdfsb2_0 fdfsb2_1 fdfsb2_2 sbequ2 sps fdfsb2_1 sup_set_class fdfsb2_2 sup_set_class wceq fdfsb2_0 wa fdfsb2_1 sup_set_class fdfsb2_2 sup_set_class wceq fdfsb2_0 wi fdfsb2_1 wal orc ee12an fdfsb2_1 sup_set_class fdfsb2_2 sup_set_class wceq fdfsb2_1 wal wn fdfsb2_0 fdfsb2_1 fdfsb2_2 wsb fdfsb2_1 sup_set_class fdfsb2_2 sup_set_class wceq fdfsb2_0 wi fdfsb2_1 wal fdfsb2_1 sup_set_class fdfsb2_2 sup_set_class wceq fdfsb2_0 wa fdfsb2_1 sup_set_class fdfsb2_2 sup_set_class wceq fdfsb2_0 wi fdfsb2_1 wal wo fdfsb2_0 fdfsb2_1 fdfsb2_2 sb4 fdfsb2_1 sup_set_class fdfsb2_2 sup_set_class wceq fdfsb2_0 wi fdfsb2_1 wal fdfsb2_1 sup_set_class fdfsb2_2 sup_set_class wceq fdfsb2_0 wa olc syl6 pm2.61i fdfsb2_1 sup_set_class fdfsb2_2 sup_set_class wceq fdfsb2_0 wa fdfsb2_0 fdfsb2_1 fdfsb2_2 wsb fdfsb2_1 sup_set_class fdfsb2_2 sup_set_class wceq fdfsb2_0 wi fdfsb2_1 wal fdfsb2_1 sup_set_class fdfsb2_2 sup_set_class wceq fdfsb2_0 fdfsb2_0 fdfsb2_1 fdfsb2_2 wsb fdfsb2_0 fdfsb2_1 fdfsb2_2 sbequ1 imp fdfsb2_0 fdfsb2_1 fdfsb2_2 sb2 jaoi impbii $.
$}
$( An alternate definition of proper substitution ~ df-sb that uses only
     primitive connectives (no defined terms) on the right-hand side.
     (Contributed by NM, 6-Mar-2007.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	fdfsb3_0 $f wff ph $.
	fdfsb3_1 $f set x $.
	fdfsb3_2 $f set y $.
	dfsb3 $p |- ( [ y / x ] ph <-> ( ( x = y -> -. ph ) -> A. x ( x = y -> ph ) ) ) $= fdfsb3_1 sup_set_class fdfsb3_2 sup_set_class wceq fdfsb3_0 wa fdfsb3_1 sup_set_class fdfsb3_2 sup_set_class wceq fdfsb3_0 wi fdfsb3_1 wal wo fdfsb3_1 sup_set_class fdfsb3_2 sup_set_class wceq fdfsb3_0 wa wn fdfsb3_1 sup_set_class fdfsb3_2 sup_set_class wceq fdfsb3_0 wi fdfsb3_1 wal wi fdfsb3_0 fdfsb3_1 fdfsb3_2 wsb fdfsb3_1 sup_set_class fdfsb3_2 sup_set_class wceq fdfsb3_0 wn wi fdfsb3_1 sup_set_class fdfsb3_2 sup_set_class wceq fdfsb3_0 wi fdfsb3_1 wal wi fdfsb3_1 sup_set_class fdfsb3_2 sup_set_class wceq fdfsb3_0 wa fdfsb3_1 sup_set_class fdfsb3_2 sup_set_class wceq fdfsb3_0 wi fdfsb3_1 wal df-or fdfsb3_0 fdfsb3_1 fdfsb3_2 dfsb2 fdfsb3_1 sup_set_class fdfsb3_2 sup_set_class wceq fdfsb3_0 wn wi fdfsb3_1 sup_set_class fdfsb3_2 sup_set_class wceq fdfsb3_0 wa wn fdfsb3_1 sup_set_class fdfsb3_2 sup_set_class wceq fdfsb3_0 wi fdfsb3_1 wal fdfsb3_1 sup_set_class fdfsb3_2 sup_set_class wceq fdfsb3_0 imnan imbi1i 3bitr4i $.
$}
$( Bound-variable hypothesis builder for substitution.  (Contributed by NM,
     5-Aug-1993.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	fhbsb2_0 $f wff ph $.
	fhbsb2_1 $f set x $.
	fhbsb2_2 $f set y $.
	hbsb2 $p |- ( -. A. x x = y -> ( [ y / x ] ph -> A. x [ y / x ] ph ) ) $= fhbsb2_1 sup_set_class fhbsb2_2 sup_set_class wceq fhbsb2_1 wal wn fhbsb2_0 fhbsb2_1 fhbsb2_2 wsb fhbsb2_1 sup_set_class fhbsb2_2 sup_set_class wceq fhbsb2_0 wi fhbsb2_1 wal fhbsb2_0 fhbsb2_1 fhbsb2_2 wsb fhbsb2_1 wal fhbsb2_0 fhbsb2_1 fhbsb2_2 sb4 fhbsb2_1 sup_set_class fhbsb2_2 sup_set_class wceq fhbsb2_0 wi fhbsb2_0 fhbsb2_1 fhbsb2_2 wsb fhbsb2_1 fhbsb2_0 fhbsb2_1 fhbsb2_2 sb2 a5i syl6 $.
$}
$( Bound-variable hypothesis builder for substitution.  (Contributed by Mario
     Carneiro, 4-Oct-2016.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	fnfsb2_0 $f wff ph $.
	fnfsb2_1 $f set x $.
	fnfsb2_2 $f set y $.
	nfsb2 $p |- ( -. A. x x = y -> F/ x [ y / x ] ph ) $= fnfsb2_1 sup_set_class fnfsb2_2 sup_set_class wceq fnfsb2_1 wal wn fnfsb2_0 fnfsb2_1 fnfsb2_2 wsb fnfsb2_1 fnfsb2_1 fnfsb2_2 fnfsb2_1 nfnae fnfsb2_0 fnfsb2_1 fnfsb2_2 hbsb2 nfd $.
$}
$( An equality theorem for substitution.  (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	fsbequi_0 $f wff ph $.
	fsbequi_1 $f set x $.
	fsbequi_2 $f set y $.
	fsbequi_3 $f set z $.
	sbequi $p |- ( x = y -> ( [ x / z ] ph -> [ y / z ] ph ) ) $= fsbequi_3 sup_set_class fsbequi_1 sup_set_class wceq fsbequi_3 wal fsbequi_3 sup_set_class fsbequi_2 sup_set_class wceq fsbequi_3 wal fsbequi_1 sup_set_class fsbequi_2 sup_set_class wceq fsbequi_0 fsbequi_3 fsbequi_1 wsb fsbequi_0 fsbequi_3 fsbequi_2 wsb wi wi fsbequi_3 sup_set_class fsbequi_1 sup_set_class wceq fsbequi_3 wal wn fsbequi_1 sup_set_class fsbequi_2 sup_set_class wceq fsbequi_3 sup_set_class fsbequi_2 sup_set_class wceq fsbequi_3 wal wn fsbequi_0 fsbequi_3 fsbequi_1 wsb fsbequi_0 fsbequi_3 fsbequi_2 wsb wi fsbequi_3 sup_set_class fsbequi_1 sup_set_class wceq fsbequi_3 wal wn fsbequi_1 sup_set_class fsbequi_2 sup_set_class wceq fsbequi_3 sup_set_class fsbequi_2 sup_set_class wceq fsbequi_3 wal wn fsbequi_0 fsbequi_3 fsbequi_1 wsb fsbequi_0 fsbequi_3 fsbequi_2 wsb wi wi fsbequi_3 sup_set_class fsbequi_1 sup_set_class wceq fsbequi_3 wal wn fsbequi_1 sup_set_class fsbequi_2 sup_set_class wceq wa fsbequi_0 fsbequi_3 fsbequi_1 wsb fsbequi_0 fsbequi_3 fsbequi_2 wsb fsbequi_3 wex fsbequi_3 sup_set_class fsbequi_2 sup_set_class wceq fsbequi_3 wal wn fsbequi_0 fsbequi_3 fsbequi_2 wsb fsbequi_3 sup_set_class fsbequi_1 sup_set_class wceq fsbequi_3 wal wn fsbequi_0 fsbequi_3 fsbequi_1 wsb fsbequi_0 fsbequi_3 fsbequi_1 wsb fsbequi_3 wal fsbequi_1 sup_set_class fsbequi_2 sup_set_class wceq fsbequi_0 fsbequi_3 fsbequi_2 wsb fsbequi_3 wex fsbequi_0 fsbequi_3 fsbequi_1 hbsb2 fsbequi_1 sup_set_class fsbequi_2 sup_set_class wceq fsbequi_0 fsbequi_3 fsbequi_1 wsb fsbequi_0 fsbequi_3 fsbequi_2 wsb wi fsbequi_3 wex fsbequi_0 fsbequi_3 fsbequi_1 wsb fsbequi_3 wal fsbequi_0 fsbequi_3 fsbequi_2 wsb fsbequi_3 wex wi fsbequi_1 sup_set_class fsbequi_2 sup_set_class wceq fsbequi_1 sup_set_class fsbequi_3 sup_set_class wceq fsbequi_3 sup_set_class fsbequi_2 sup_set_class wceq wa fsbequi_3 wex fsbequi_0 fsbequi_3 fsbequi_1 wsb fsbequi_0 fsbequi_3 fsbequi_2 wsb wi fsbequi_3 wex fsbequi_1 fsbequi_2 fsbequi_3 equvini fsbequi_1 sup_set_class fsbequi_3 sup_set_class wceq fsbequi_3 sup_set_class fsbequi_2 sup_set_class wceq wa fsbequi_0 fsbequi_3 fsbequi_1 wsb fsbequi_0 fsbequi_3 fsbequi_2 wsb wi fsbequi_3 fsbequi_1 sup_set_class fsbequi_3 sup_set_class wceq fsbequi_0 fsbequi_3 fsbequi_1 wsb fsbequi_0 fsbequi_3 sup_set_class fsbequi_2 sup_set_class wceq fsbequi_0 fsbequi_3 fsbequi_2 wsb fsbequi_0 fsbequi_1 fsbequi_3 stdpc7 fsbequi_0 fsbequi_3 fsbequi_2 sbequ1 sylan9 eximi syl fsbequi_0 fsbequi_3 fsbequi_1 wsb fsbequi_0 fsbequi_3 fsbequi_2 wsb fsbequi_3 19.35 sylib sylan9 fsbequi_0 fsbequi_3 fsbequi_2 wsb fsbequi_3 sup_set_class fsbequi_2 sup_set_class wceq fsbequi_3 wal wn fsbequi_3 fsbequi_0 fsbequi_3 fsbequi_2 nfsb2 19.9d syl9 ex com23 fsbequi_3 sup_set_class fsbequi_1 sup_set_class wceq fsbequi_3 wal fsbequi_1 sup_set_class fsbequi_2 sup_set_class wceq fsbequi_0 fsbequi_3 fsbequi_1 wsb fsbequi_0 fsbequi_3 fsbequi_2 wsb wi fsbequi_3 sup_set_class fsbequi_1 sup_set_class wceq fsbequi_3 wal fsbequi_1 sup_set_class fsbequi_2 sup_set_class wceq wa fsbequi_0 fsbequi_3 fsbequi_1 wsb fsbequi_0 fsbequi_0 fsbequi_3 fsbequi_2 wsb fsbequi_3 sup_set_class fsbequi_1 sup_set_class wceq fsbequi_3 wal fsbequi_0 fsbequi_3 fsbequi_1 wsb fsbequi_0 wi fsbequi_1 sup_set_class fsbequi_2 sup_set_class wceq fsbequi_3 sup_set_class fsbequi_1 sup_set_class wceq fsbequi_0 fsbequi_3 fsbequi_1 wsb fsbequi_0 wi fsbequi_3 fsbequi_0 fsbequi_3 fsbequi_1 sbequ2 sps adantr fsbequi_1 sup_set_class fsbequi_2 sup_set_class wceq fsbequi_0 fsbequi_0 fsbequi_1 fsbequi_2 wsb fsbequi_3 sup_set_class fsbequi_1 sup_set_class wceq fsbequi_3 wal fsbequi_0 fsbequi_3 fsbequi_2 wsb fsbequi_0 fsbequi_1 fsbequi_2 sbequ1 fsbequi_3 sup_set_class fsbequi_1 sup_set_class wceq fsbequi_3 wal fsbequi_0 fsbequi_3 fsbequi_2 wsb fsbequi_0 fsbequi_1 fsbequi_2 wsb fsbequi_0 fsbequi_3 fsbequi_1 fsbequi_2 drsb1 biimprd sylan9r syld ex fsbequi_3 sup_set_class fsbequi_2 sup_set_class wceq fsbequi_3 wal fsbequi_1 sup_set_class fsbequi_2 sup_set_class wceq fsbequi_0 fsbequi_3 fsbequi_1 wsb fsbequi_0 fsbequi_3 fsbequi_2 wsb wi fsbequi_3 sup_set_class fsbequi_2 sup_set_class wceq fsbequi_3 wal fsbequi_1 sup_set_class fsbequi_2 sup_set_class wceq wa fsbequi_0 fsbequi_3 fsbequi_1 wsb fsbequi_0 fsbequi_0 fsbequi_3 fsbequi_2 wsb fsbequi_3 sup_set_class fsbequi_2 sup_set_class wceq fsbequi_3 wal fsbequi_0 fsbequi_3 fsbequi_1 wsb fsbequi_0 fsbequi_2 fsbequi_1 wsb fsbequi_1 sup_set_class fsbequi_2 sup_set_class wceq fsbequi_0 fsbequi_3 sup_set_class fsbequi_2 sup_set_class wceq fsbequi_3 wal fsbequi_0 fsbequi_3 fsbequi_1 wsb fsbequi_0 fsbequi_2 fsbequi_1 wsb fsbequi_0 fsbequi_3 fsbequi_2 fsbequi_1 drsb1 biimpd fsbequi_0 fsbequi_1 fsbequi_2 stdpc7 sylan9 fsbequi_3 sup_set_class fsbequi_2 sup_set_class wceq fsbequi_3 wal fsbequi_0 fsbequi_0 fsbequi_3 fsbequi_2 wsb wi fsbequi_1 sup_set_class fsbequi_2 sup_set_class wceq fsbequi_3 sup_set_class fsbequi_2 sup_set_class wceq fsbequi_0 fsbequi_0 fsbequi_3 fsbequi_2 wsb wi fsbequi_3 fsbequi_0 fsbequi_3 fsbequi_2 sbequ1 sps adantr syld ex pm2.61ii $.
$}
$( An equality theorem for substitution.  Used in proof of Theorem 9.7 in
     [Megill] p. 449 (p. 16 of the preprint).  (Contributed by NM,
     5-Aug-1993.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	fsbequ_0 $f wff ph $.
	fsbequ_1 $f set x $.
	fsbequ_2 $f set y $.
	fsbequ_3 $f set z $.
	sbequ $p |- ( x = y -> ( [ x / z ] ph <-> [ y / z ] ph ) ) $= fsbequ_1 sup_set_class fsbequ_2 sup_set_class wceq fsbequ_0 fsbequ_3 fsbequ_1 wsb fsbequ_0 fsbequ_3 fsbequ_2 wsb fsbequ_0 fsbequ_1 fsbequ_2 fsbequ_3 sbequi fsbequ_0 fsbequ_3 fsbequ_2 wsb fsbequ_0 fsbequ_3 fsbequ_1 wsb wi fsbequ_2 fsbequ_1 fsbequ_0 fsbequ_2 fsbequ_1 fsbequ_3 sbequi equcoms impbid $.
$}
$( Formula-building lemma for use with the Distinctor Reduction Theorem.
     Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).  (Contributed
     by NM, 27-Feb-2005.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	fdrsb2_0 $f wff ph $.
	fdrsb2_1 $f set x $.
	fdrsb2_2 $f set y $.
	fdrsb2_3 $f set z $.
	drsb2 $p |- ( A. x x = y -> ( [ x / z ] ph <-> [ y / z ] ph ) ) $= fdrsb2_1 sup_set_class fdrsb2_2 sup_set_class wceq fdrsb2_0 fdrsb2_3 fdrsb2_1 wsb fdrsb2_0 fdrsb2_3 fdrsb2_2 wsb wb fdrsb2_1 fdrsb2_0 fdrsb2_1 fdrsb2_2 fdrsb2_3 sbequ sps $.
$}
$( Negation inside and outside of substitution are equivalent.  (Contributed
     by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	fsbn_0 $f wff ph $.
	fsbn_1 $f set x $.
	fsbn_2 $f set y $.
	sbn $p |- ( [ y / x ] -. ph <-> -. [ y / x ] ph ) $= fsbn_0 wn fsbn_1 fsbn_2 wsb fsbn_0 fsbn_1 fsbn_2 wsb wn fsbn_1 sup_set_class fsbn_2 sup_set_class wceq fsbn_1 wal fsbn_0 wn fsbn_1 fsbn_2 wsb fsbn_0 fsbn_1 fsbn_2 wsb wn wi fsbn_1 sup_set_class fsbn_2 sup_set_class wceq fsbn_0 wn fsbn_1 fsbn_2 wsb fsbn_0 fsbn_1 fsbn_2 wsb wn wi fsbn_1 fsbn_1 sup_set_class fsbn_2 sup_set_class wceq fsbn_0 wn fsbn_1 fsbn_2 wsb fsbn_0 fsbn_0 fsbn_1 fsbn_2 wsb fsbn_0 wn fsbn_1 fsbn_2 sbequ2 fsbn_0 fsbn_1 fsbn_2 sbequ2 nsyld sps fsbn_1 sup_set_class fsbn_2 sup_set_class wceq fsbn_1 wal wn fsbn_0 wn fsbn_1 fsbn_2 wsb fsbn_1 sup_set_class fsbn_2 sup_set_class wceq fsbn_0 wn wi fsbn_1 wal fsbn_0 fsbn_1 fsbn_2 wsb wn fsbn_0 wn fsbn_1 fsbn_2 sb4 fsbn_0 fsbn_1 fsbn_2 wsb fsbn_1 sup_set_class fsbn_2 sup_set_class wceq fsbn_0 wn wi fsbn_1 wal fsbn_0 fsbn_1 fsbn_2 wsb fsbn_1 sup_set_class fsbn_2 sup_set_class wceq fsbn_0 wa fsbn_1 wex fsbn_1 sup_set_class fsbn_2 sup_set_class wceq fsbn_0 wn wi fsbn_1 wal wn fsbn_0 fsbn_1 fsbn_2 sb1 fsbn_0 fsbn_1 fsbn_2 equs3 sylib con2i syl6 pm2.61i fsbn_0 fsbn_1 fsbn_2 wsb wn fsbn_1 sup_set_class fsbn_2 sup_set_class wceq fsbn_0 wn wi fsbn_1 sup_set_class fsbn_2 sup_set_class wceq fsbn_0 wn wa fsbn_1 wex fsbn_0 wn fsbn_1 fsbn_2 wsb fsbn_1 sup_set_class fsbn_2 sup_set_class wceq fsbn_0 fsbn_0 fsbn_1 fsbn_2 wsb fsbn_0 fsbn_1 fsbn_2 sbequ1 con3rr3 fsbn_0 fsbn_1 fsbn_2 wsb wn fsbn_1 sup_set_class fsbn_2 sup_set_class wceq fsbn_0 wn wn wi fsbn_1 wal wn fsbn_1 sup_set_class fsbn_2 sup_set_class wceq fsbn_0 wn wa fsbn_1 wex fsbn_1 sup_set_class fsbn_2 sup_set_class wceq fsbn_0 wn wn wi fsbn_1 wal fsbn_0 fsbn_1 fsbn_2 wsb fsbn_1 sup_set_class fsbn_2 sup_set_class wceq fsbn_0 wn wn wi fsbn_1 wal fsbn_0 wn wn fsbn_1 fsbn_2 wsb fsbn_0 fsbn_1 fsbn_2 wsb fsbn_0 wn wn fsbn_1 fsbn_2 sb2 fsbn_0 fsbn_0 wn wn fsbn_1 fsbn_2 fsbn_0 notnot sbbii sylibr con3i fsbn_0 wn fsbn_1 fsbn_2 equs3 sylibr fsbn_0 wn fsbn_1 fsbn_2 df-sb sylanbrc impbii $.
$}
$( Removal of implication from substitution.  (Contributed by NM,
     5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	fsbi1_0 $f wff ph $.
	fsbi1_1 $f wff ps $.
	fsbi1_2 $f set x $.
	fsbi1_3 $f set y $.
	sbi1 $p |- ( [ y / x ] ( ph -> ps ) -> ( [ y / x ] ph -> [ y / x ] ps ) ) $= fsbi1_2 sup_set_class fsbi1_3 sup_set_class wceq fsbi1_2 wal fsbi1_0 fsbi1_1 wi fsbi1_2 fsbi1_3 wsb fsbi1_0 fsbi1_2 fsbi1_3 wsb fsbi1_1 fsbi1_2 fsbi1_3 wsb wi wi fsbi1_2 sup_set_class fsbi1_3 sup_set_class wceq fsbi1_0 fsbi1_1 wi fsbi1_2 fsbi1_3 wsb fsbi1_0 fsbi1_2 fsbi1_3 wsb fsbi1_1 fsbi1_2 fsbi1_3 wsb wi wi fsbi1_2 fsbi1_2 sup_set_class fsbi1_3 sup_set_class wceq fsbi1_0 fsbi1_1 wi fsbi1_2 fsbi1_3 wsb fsbi1_0 fsbi1_2 fsbi1_3 wsb fsbi1_1 fsbi1_1 fsbi1_2 fsbi1_3 wsb fsbi1_2 sup_set_class fsbi1_3 sup_set_class wceq fsbi1_0 fsbi1_2 fsbi1_3 wsb fsbi1_0 fsbi1_0 fsbi1_1 wi fsbi1_2 fsbi1_3 wsb fsbi1_1 fsbi1_0 fsbi1_2 fsbi1_3 sbequ2 fsbi1_0 fsbi1_1 wi fsbi1_2 fsbi1_3 sbequ2 syl5d fsbi1_1 fsbi1_2 fsbi1_3 sbequ1 syl6d sps fsbi1_2 sup_set_class fsbi1_3 sup_set_class wceq fsbi1_2 wal wn fsbi1_0 fsbi1_2 fsbi1_3 wsb fsbi1_2 sup_set_class fsbi1_3 sup_set_class wceq fsbi1_0 wi fsbi1_2 wal fsbi1_0 fsbi1_1 wi fsbi1_2 fsbi1_3 wsb fsbi1_1 fsbi1_2 fsbi1_3 wsb fsbi1_0 fsbi1_2 fsbi1_3 sb4 fsbi1_2 sup_set_class fsbi1_3 sup_set_class wceq fsbi1_2 wal wn fsbi1_0 fsbi1_1 wi fsbi1_2 fsbi1_3 wsb fsbi1_2 sup_set_class fsbi1_3 sup_set_class wceq fsbi1_0 fsbi1_1 wi wi fsbi1_2 wal fsbi1_2 sup_set_class fsbi1_3 sup_set_class wceq fsbi1_0 wi fsbi1_2 wal fsbi1_1 fsbi1_2 fsbi1_3 wsb wi fsbi1_0 fsbi1_1 wi fsbi1_2 fsbi1_3 sb4 fsbi1_2 sup_set_class fsbi1_3 sup_set_class wceq fsbi1_0 fsbi1_1 wi wi fsbi1_2 wal fsbi1_2 sup_set_class fsbi1_3 sup_set_class wceq fsbi1_0 wi fsbi1_2 wal fsbi1_2 sup_set_class fsbi1_3 sup_set_class wceq fsbi1_1 wi fsbi1_2 wal fsbi1_1 fsbi1_2 fsbi1_3 wsb fsbi1_2 sup_set_class fsbi1_3 sup_set_class wceq fsbi1_0 fsbi1_1 wi wi fsbi1_2 sup_set_class fsbi1_3 sup_set_class wceq fsbi1_0 wi fsbi1_2 sup_set_class fsbi1_3 sup_set_class wceq fsbi1_1 wi fsbi1_2 fsbi1_2 sup_set_class fsbi1_3 sup_set_class wceq fsbi1_0 fsbi1_1 ax-2 al2imi fsbi1_1 fsbi1_2 fsbi1_3 sb2 syl6 syl6 syl5d pm2.61i $.
$}
$( Introduction of implication into substitution.  (Contributed by NM,
     5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	fsbi2_0 $f wff ph $.
	fsbi2_1 $f wff ps $.
	fsbi2_2 $f set x $.
	fsbi2_3 $f set y $.
	sbi2 $p |- ( ( [ y / x ] ph -> [ y / x ] ps ) -> [ y / x ] ( ph -> ps ) ) $= fsbi2_0 fsbi2_2 fsbi2_3 wsb fsbi2_1 fsbi2_2 fsbi2_3 wsb fsbi2_0 fsbi2_1 wi fsbi2_2 fsbi2_3 wsb fsbi2_0 fsbi2_2 fsbi2_3 wsb wn fsbi2_0 wn fsbi2_2 fsbi2_3 wsb fsbi2_0 fsbi2_1 wi fsbi2_2 fsbi2_3 wsb fsbi2_0 fsbi2_2 fsbi2_3 sbn fsbi2_0 wn fsbi2_0 fsbi2_1 wi fsbi2_2 fsbi2_3 fsbi2_0 fsbi2_1 pm2.21 sbimi sylbir fsbi2_1 fsbi2_0 fsbi2_1 wi fsbi2_2 fsbi2_3 fsbi2_1 fsbi2_0 ax-1 sbimi ja $.
$}
$( Implication inside and outside of substitution are equivalent.
     (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	fsbim_0 $f wff ph $.
	fsbim_1 $f wff ps $.
	fsbim_2 $f set x $.
	fsbim_3 $f set y $.
	sbim $p |- ( [ y / x ] ( ph -> ps ) <-> ( [ y / x ] ph -> [ y / x ] ps ) ) $= fsbim_0 fsbim_1 wi fsbim_2 fsbim_3 wsb fsbim_0 fsbim_2 fsbim_3 wsb fsbim_1 fsbim_2 fsbim_3 wsb wi fsbim_0 fsbim_1 fsbim_2 fsbim_3 sbi1 fsbim_0 fsbim_1 fsbim_2 fsbim_3 sbi2 impbii $.
$}
$( Logical OR inside and outside of substitution are equivalent.
     (Contributed by NM, 29-Sep-2002.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	fsbor_0 $f wff ph $.
	fsbor_1 $f wff ps $.
	fsbor_2 $f set x $.
	fsbor_3 $f set y $.
	sbor $p |- ( [ y / x ] ( ph \/ ps ) <-> ( [ y / x ] ph \/ [ y / x ] ps ) ) $= fsbor_0 wn fsbor_1 wi fsbor_2 fsbor_3 wsb fsbor_0 fsbor_2 fsbor_3 wsb wn fsbor_1 fsbor_2 fsbor_3 wsb wi fsbor_0 fsbor_1 wo fsbor_2 fsbor_3 wsb fsbor_0 fsbor_2 fsbor_3 wsb fsbor_1 fsbor_2 fsbor_3 wsb wo fsbor_0 wn fsbor_1 wi fsbor_2 fsbor_3 wsb fsbor_0 wn fsbor_2 fsbor_3 wsb fsbor_1 fsbor_2 fsbor_3 wsb wi fsbor_0 fsbor_2 fsbor_3 wsb wn fsbor_1 fsbor_2 fsbor_3 wsb wi fsbor_0 wn fsbor_1 fsbor_2 fsbor_3 sbim fsbor_0 wn fsbor_2 fsbor_3 wsb fsbor_0 fsbor_2 fsbor_3 wsb wn fsbor_1 fsbor_2 fsbor_3 wsb fsbor_0 fsbor_2 fsbor_3 sbn imbi1i bitri fsbor_0 fsbor_1 wo fsbor_0 wn fsbor_1 wi fsbor_2 fsbor_3 fsbor_0 fsbor_1 df-or sbbii fsbor_0 fsbor_2 fsbor_3 wsb fsbor_1 fsbor_2 fsbor_3 wsb df-or 3bitr4i $.
$}
$( Substitution with a variable not free in antecedent affects only the
       consequent.  (Contributed by NM, 5-Aug-1993.)  (Revised by Mario
       Carneiro, 4-Oct-2016.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	fsbrim_0 $f wff ph $.
	fsbrim_1 $f wff ps $.
	fsbrim_2 $f set x $.
	fsbrim_3 $f set y $.
	esbrim_0 $e |- F/ x ph $.
	sbrim $p |- ( [ y / x ] ( ph -> ps ) <-> ( ph -> [ y / x ] ps ) ) $= fsbrim_0 fsbrim_1 wi fsbrim_2 fsbrim_3 wsb fsbrim_0 fsbrim_2 fsbrim_3 wsb fsbrim_1 fsbrim_2 fsbrim_3 wsb wi fsbrim_0 fsbrim_1 fsbrim_2 fsbrim_3 wsb wi fsbrim_0 fsbrim_1 fsbrim_2 fsbrim_3 sbim fsbrim_0 fsbrim_2 fsbrim_3 wsb fsbrim_0 fsbrim_1 fsbrim_2 fsbrim_3 wsb fsbrim_0 fsbrim_2 fsbrim_3 esbrim_0 sbf imbi1i bitri $.
$}
$( Substitution with a variable not free in consequent affects only the
       antecedent.  (Contributed by NM, 14-Nov-2013.)  (Revised by Mario
       Carneiro, 4-Oct-2016.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	fsblim_0 $f wff ph $.
	fsblim_1 $f wff ps $.
	fsblim_2 $f set x $.
	fsblim_3 $f set y $.
	esblim_0 $e |- F/ x ps $.
	sblim $p |- ( [ y / x ] ( ph -> ps ) <-> ( [ y / x ] ph -> ps ) ) $= fsblim_0 fsblim_1 wi fsblim_2 fsblim_3 wsb fsblim_0 fsblim_2 fsblim_3 wsb fsblim_1 fsblim_2 fsblim_3 wsb wi fsblim_0 fsblim_2 fsblim_3 wsb fsblim_1 wi fsblim_0 fsblim_1 fsblim_2 fsblim_3 sbim fsblim_1 fsblim_2 fsblim_3 wsb fsblim_1 fsblim_0 fsblim_2 fsblim_3 wsb fsblim_1 fsblim_2 fsblim_3 esblim_0 sbf imbi2i bitri $.
$}
$( Conjunction inside and outside of a substitution are equivalent.
     (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	fsban_0 $f wff ph $.
	fsban_1 $f wff ps $.
	fsban_2 $f set x $.
	fsban_3 $f set y $.
	sban $p |- ( [ y / x ] ( ph /\ ps ) <-> ( [ y / x ] ph /\ [ y / x ] ps ) ) $= fsban_0 fsban_1 wn wi wn fsban_2 fsban_3 wsb fsban_0 fsban_2 fsban_3 wsb fsban_1 fsban_2 fsban_3 wsb wn wi wn fsban_0 fsban_1 wa fsban_2 fsban_3 wsb fsban_0 fsban_2 fsban_3 wsb fsban_1 fsban_2 fsban_3 wsb wa fsban_0 fsban_1 wn wi wn fsban_2 fsban_3 wsb fsban_0 fsban_1 wn wi fsban_2 fsban_3 wsb fsban_0 fsban_2 fsban_3 wsb fsban_1 fsban_2 fsban_3 wsb wn wi fsban_0 fsban_1 wn wi fsban_2 fsban_3 sbn fsban_0 fsban_1 wn wi fsban_2 fsban_3 wsb fsban_0 fsban_2 fsban_3 wsb fsban_1 wn fsban_2 fsban_3 wsb wi fsban_0 fsban_2 fsban_3 wsb fsban_1 fsban_2 fsban_3 wsb wn wi fsban_0 fsban_1 wn fsban_2 fsban_3 sbim fsban_1 wn fsban_2 fsban_3 wsb fsban_1 fsban_2 fsban_3 wsb wn fsban_0 fsban_2 fsban_3 wsb fsban_1 fsban_2 fsban_3 sbn imbi2i bitri xchbinx fsban_0 fsban_1 wa fsban_0 fsban_1 wn wi wn fsban_2 fsban_3 fsban_0 fsban_1 df-an sbbii fsban_0 fsban_2 fsban_3 wsb fsban_1 fsban_2 fsban_3 wsb df-an 3bitr4i $.
$}
$( Conjunction inside and outside of a substitution are equivalent.
     (Contributed by NM, 14-Dec-2006.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	$v y $.
	fsb3an_0 $f wff ph $.
	fsb3an_1 $f wff ps $.
	fsb3an_2 $f wff ch $.
	fsb3an_3 $f set x $.
	fsb3an_4 $f set y $.
	sb3an $p |- ( [ y / x ] ( ph /\ ps /\ ch ) <-> ( [ y / x ] ph /\ [ y / x ] ps /\ [ y / x ] ch ) ) $= fsb3an_0 fsb3an_1 fsb3an_2 w3a fsb3an_3 fsb3an_4 wsb fsb3an_0 fsb3an_1 wa fsb3an_2 wa fsb3an_3 fsb3an_4 wsb fsb3an_0 fsb3an_1 wa fsb3an_3 fsb3an_4 wsb fsb3an_2 fsb3an_3 fsb3an_4 wsb wa fsb3an_0 fsb3an_3 fsb3an_4 wsb fsb3an_1 fsb3an_3 fsb3an_4 wsb fsb3an_2 fsb3an_3 fsb3an_4 wsb w3a fsb3an_0 fsb3an_1 fsb3an_2 w3a fsb3an_0 fsb3an_1 wa fsb3an_2 wa fsb3an_3 fsb3an_4 fsb3an_0 fsb3an_1 fsb3an_2 df-3an sbbii fsb3an_0 fsb3an_1 wa fsb3an_2 fsb3an_3 fsb3an_4 sban fsb3an_0 fsb3an_1 wa fsb3an_3 fsb3an_4 wsb fsb3an_2 fsb3an_3 fsb3an_4 wsb wa fsb3an_0 fsb3an_3 fsb3an_4 wsb fsb3an_1 fsb3an_3 fsb3an_4 wsb wa fsb3an_2 fsb3an_3 fsb3an_4 wsb wa fsb3an_0 fsb3an_3 fsb3an_4 wsb fsb3an_1 fsb3an_3 fsb3an_4 wsb fsb3an_2 fsb3an_3 fsb3an_4 wsb w3a fsb3an_0 fsb3an_1 wa fsb3an_3 fsb3an_4 wsb fsb3an_0 fsb3an_3 fsb3an_4 wsb fsb3an_1 fsb3an_3 fsb3an_4 wsb wa fsb3an_2 fsb3an_3 fsb3an_4 wsb fsb3an_0 fsb3an_1 fsb3an_3 fsb3an_4 sban anbi1i fsb3an_0 fsb3an_3 fsb3an_4 wsb fsb3an_1 fsb3an_3 fsb3an_4 wsb fsb3an_2 fsb3an_3 fsb3an_4 wsb df-3an bitr4i 3bitri $.
$}
$( Equivalence inside and outside of a substitution are equivalent.
     (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	fsbbi_0 $f wff ph $.
	fsbbi_1 $f wff ps $.
	fsbbi_2 $f set x $.
	fsbbi_3 $f set y $.
	sbbi $p |- ( [ y / x ] ( ph <-> ps ) <-> ( [ y / x ] ph <-> [ y / x ] ps ) ) $= fsbbi_0 fsbbi_1 wb fsbbi_2 fsbbi_3 wsb fsbbi_0 fsbbi_1 wi fsbbi_1 fsbbi_0 wi wa fsbbi_2 fsbbi_3 wsb fsbbi_0 fsbbi_2 fsbbi_3 wsb fsbbi_1 fsbbi_2 fsbbi_3 wsb wb fsbbi_0 fsbbi_1 wb fsbbi_0 fsbbi_1 wi fsbbi_1 fsbbi_0 wi wa fsbbi_2 fsbbi_3 fsbbi_0 fsbbi_1 dfbi2 sbbii fsbbi_0 fsbbi_1 wi fsbbi_2 fsbbi_3 wsb fsbbi_1 fsbbi_0 wi fsbbi_2 fsbbi_3 wsb wa fsbbi_0 fsbbi_2 fsbbi_3 wsb fsbbi_1 fsbbi_2 fsbbi_3 wsb wi fsbbi_1 fsbbi_2 fsbbi_3 wsb fsbbi_0 fsbbi_2 fsbbi_3 wsb wi wa fsbbi_0 fsbbi_1 wi fsbbi_1 fsbbi_0 wi wa fsbbi_2 fsbbi_3 wsb fsbbi_0 fsbbi_2 fsbbi_3 wsb fsbbi_1 fsbbi_2 fsbbi_3 wsb wb fsbbi_0 fsbbi_1 wi fsbbi_2 fsbbi_3 wsb fsbbi_0 fsbbi_2 fsbbi_3 wsb fsbbi_1 fsbbi_2 fsbbi_3 wsb wi fsbbi_1 fsbbi_0 wi fsbbi_2 fsbbi_3 wsb fsbbi_1 fsbbi_2 fsbbi_3 wsb fsbbi_0 fsbbi_2 fsbbi_3 wsb wi fsbbi_0 fsbbi_1 fsbbi_2 fsbbi_3 sbim fsbbi_1 fsbbi_0 fsbbi_2 fsbbi_3 sbim anbi12i fsbbi_0 fsbbi_1 wi fsbbi_1 fsbbi_0 wi fsbbi_2 fsbbi_3 sban fsbbi_0 fsbbi_2 fsbbi_3 wsb fsbbi_1 fsbbi_2 fsbbi_3 wsb dfbi2 3bitr4i bitri $.
$}
$( Introduce left biconditional inside of a substitution.  (Contributed by
       NM, 19-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	$v y $.
	fsblbis_0 $f wff ph $.
	fsblbis_1 $f wff ps $.
	fsblbis_2 $f wff ch $.
	fsblbis_3 $f set x $.
	fsblbis_4 $f set y $.
	esblbis_0 $e |- ( [ y / x ] ph <-> ps ) $.
	sblbis $p |- ( [ y / x ] ( ch <-> ph ) <-> ( [ y / x ] ch <-> ps ) ) $= fsblbis_2 fsblbis_0 wb fsblbis_3 fsblbis_4 wsb fsblbis_2 fsblbis_3 fsblbis_4 wsb fsblbis_0 fsblbis_3 fsblbis_4 wsb wb fsblbis_2 fsblbis_3 fsblbis_4 wsb fsblbis_1 wb fsblbis_2 fsblbis_0 fsblbis_3 fsblbis_4 sbbi fsblbis_0 fsblbis_3 fsblbis_4 wsb fsblbis_1 fsblbis_2 fsblbis_3 fsblbis_4 wsb esblbis_0 bibi2i bitri $.
$}
$( Introduce right biconditional inside of a substitution.  (Contributed by
       NM, 18-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	$v y $.
	fsbrbis_0 $f wff ph $.
	fsbrbis_1 $f wff ps $.
	fsbrbis_2 $f wff ch $.
	fsbrbis_3 $f set x $.
	fsbrbis_4 $f set y $.
	esbrbis_0 $e |- ( [ y / x ] ph <-> ps ) $.
	sbrbis $p |- ( [ y / x ] ( ph <-> ch ) <-> ( ps <-> [ y / x ] ch ) ) $= fsbrbis_0 fsbrbis_2 wb fsbrbis_3 fsbrbis_4 wsb fsbrbis_0 fsbrbis_3 fsbrbis_4 wsb fsbrbis_2 fsbrbis_3 fsbrbis_4 wsb wb fsbrbis_1 fsbrbis_2 fsbrbis_3 fsbrbis_4 wsb wb fsbrbis_0 fsbrbis_2 fsbrbis_3 fsbrbis_4 sbbi fsbrbis_0 fsbrbis_3 fsbrbis_4 wsb fsbrbis_1 fsbrbis_2 fsbrbis_3 fsbrbis_4 wsb esbrbis_0 bibi1i bitri $.
$}
$( Introduce right biconditional inside of a substitution.  (Contributed by
       NM, 18-Aug-1993.)  (Revised by Mario Carneiro, 4-Oct-2016.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	$v y $.
	fsbrbif_0 $f wff ph $.
	fsbrbif_1 $f wff ps $.
	fsbrbif_2 $f wff ch $.
	fsbrbif_3 $f set x $.
	fsbrbif_4 $f set y $.
	esbrbif_0 $e |- F/ x ch $.
	esbrbif_1 $e |- ( [ y / x ] ph <-> ps ) $.
	sbrbif $p |- ( [ y / x ] ( ph <-> ch ) <-> ( ps <-> ch ) ) $= fsbrbif_0 fsbrbif_2 wb fsbrbif_3 fsbrbif_4 wsb fsbrbif_1 fsbrbif_2 fsbrbif_3 fsbrbif_4 wsb wb fsbrbif_1 fsbrbif_2 wb fsbrbif_0 fsbrbif_1 fsbrbif_2 fsbrbif_3 fsbrbif_4 esbrbif_1 sbrbis fsbrbif_2 fsbrbif_3 fsbrbif_4 wsb fsbrbif_2 fsbrbif_1 fsbrbif_2 fsbrbif_3 fsbrbif_4 esbrbif_0 sbf bibi2i bitri $.
$}
$( A specialization theorem.  (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	fspsbe_0 $f wff ph $.
	fspsbe_1 $f set x $.
	fspsbe_2 $f set y $.
	spsbe $p |- ( [ y / x ] ph -> E. x ph ) $= fspsbe_0 fspsbe_1 fspsbe_2 wsb fspsbe_0 wn fspsbe_1 wal wn fspsbe_0 fspsbe_1 wex fspsbe_0 wn fspsbe_1 wal fspsbe_0 fspsbe_1 fspsbe_2 wsb fspsbe_0 wn fspsbe_1 wal fspsbe_0 wn fspsbe_1 fspsbe_2 wsb fspsbe_0 fspsbe_1 fspsbe_2 wsb wn fspsbe_0 wn fspsbe_1 fspsbe_2 stdpc4 fspsbe_0 fspsbe_1 fspsbe_2 sbn sylib con2i fspsbe_0 fspsbe_1 df-ex sylibr $.
$}
$( Specialization of implication.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Andrew Salmon, 25-May-2011.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	fspsbim_0 $f wff ph $.
	fspsbim_1 $f wff ps $.
	fspsbim_2 $f set x $.
	fspsbim_3 $f set y $.
	spsbim $p |- ( A. x ( ph -> ps ) -> ( [ y / x ] ph -> [ y / x ] ps ) ) $= fspsbim_0 fspsbim_1 wi fspsbim_2 wal fspsbim_0 fspsbim_1 wi fspsbim_2 fspsbim_3 wsb fspsbim_0 fspsbim_2 fspsbim_3 wsb fspsbim_1 fspsbim_2 fspsbim_3 wsb wi fspsbim_0 fspsbim_1 wi fspsbim_2 fspsbim_3 stdpc4 fspsbim_0 fspsbim_1 fspsbim_2 fspsbim_3 sbi1 syl $.
$}
$( Specialization of biconditional.  (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	fspsbbi_0 $f wff ph $.
	fspsbbi_1 $f wff ps $.
	fspsbbi_2 $f set x $.
	fspsbbi_3 $f set y $.
	spsbbi $p |- ( A. x ( ph <-> ps ) -> ( [ y / x ] ph <-> [ y / x ] ps ) ) $= fspsbbi_0 fspsbbi_1 wb fspsbbi_2 wal fspsbbi_0 fspsbbi_1 wb fspsbbi_2 fspsbbi_3 wsb fspsbbi_0 fspsbbi_2 fspsbbi_3 wsb fspsbbi_1 fspsbbi_2 fspsbbi_3 wsb wb fspsbbi_0 fspsbbi_1 wb fspsbbi_2 fspsbbi_3 stdpc4 fspsbbi_0 fspsbbi_1 fspsbbi_2 fspsbbi_3 sbbi sylib $.
$}
$( Deduction substituting both sides of a biconditional.  (Contributed by
       NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	$v y $.
	fsbbid_0 $f wff ph $.
	fsbbid_1 $f wff ps $.
	fsbbid_2 $f wff ch $.
	fsbbid_3 $f set x $.
	fsbbid_4 $f set y $.
	esbbid_0 $e |- F/ x ph $.
	esbbid_1 $e |- ( ph -> ( ps <-> ch ) ) $.
	sbbid $p |- ( ph -> ( [ y / x ] ps <-> [ y / x ] ch ) ) $= fsbbid_0 fsbbid_1 fsbbid_2 wb fsbbid_3 wal fsbbid_1 fsbbid_3 fsbbid_4 wsb fsbbid_2 fsbbid_3 fsbbid_4 wsb wb fsbbid_0 fsbbid_1 fsbbid_2 wb fsbbid_3 esbbid_0 esbbid_1 alrimi fsbbid_1 fsbbid_2 fsbbid_3 fsbbid_4 spsbbi syl $.
$}
$( Elimination of equality from antecedent after substitution.  (Contributed
     by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	fsbequ8_0 $f wff ph $.
	fsbequ8_1 $f set x $.
	fsbequ8_2 $f set y $.
	sbequ8 $p |- ( [ y / x ] ph <-> [ y / x ] ( x = y -> ph ) ) $= fsbequ8_0 fsbequ8_1 fsbequ8_2 wsb fsbequ8_1 sup_set_class fsbequ8_2 sup_set_class wceq fsbequ8_1 fsbequ8_2 wsb fsbequ8_0 fsbequ8_1 fsbequ8_2 wsb wi fsbequ8_1 sup_set_class fsbequ8_2 sup_set_class wceq fsbequ8_0 wi fsbequ8_1 fsbequ8_2 wsb fsbequ8_1 sup_set_class fsbequ8_2 sup_set_class wceq fsbequ8_1 fsbequ8_2 wsb fsbequ8_0 fsbequ8_1 fsbequ8_2 wsb fsbequ8_1 fsbequ8_2 equsb1 a1bi fsbequ8_1 sup_set_class fsbequ8_2 sup_set_class wceq fsbequ8_0 fsbequ8_1 fsbequ8_2 sbim bitr4i $.
$}
$( A variable not free remains so after substitution with a distinct variable
     (closed form of ~ nfsb4 ).  (Contributed by NM, 7-Apr-2004.)  (Revised by
     Mario Carneiro, 4-Oct-2016.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	fnfsb4t_0 $f wff ph $.
	fnfsb4t_1 $f set x $.
	fnfsb4t_2 $f set y $.
	fnfsb4t_3 $f set z $.
	nfsb4t $p |- ( A. x F/ z ph -> ( -. A. z z = y -> F/ z [ y / x ] ph ) ) $= fnfsb4t_0 fnfsb4t_3 wnf fnfsb4t_1 wal fnfsb4t_3 sup_set_class fnfsb4t_1 sup_set_class wceq fnfsb4t_3 wal fnfsb4t_3 sup_set_class fnfsb4t_2 sup_set_class wceq fnfsb4t_3 wal wn fnfsb4t_0 fnfsb4t_1 fnfsb4t_2 wsb fnfsb4t_3 wnf wi fnfsb4t_0 fnfsb4t_3 wnf fnfsb4t_1 wal fnfsb4t_3 sup_set_class fnfsb4t_1 sup_set_class wceq fnfsb4t_3 wal wn fnfsb4t_3 sup_set_class fnfsb4t_2 sup_set_class wceq fnfsb4t_3 wal wn fnfsb4t_0 fnfsb4t_1 fnfsb4t_2 wsb fnfsb4t_3 wnf fnfsb4t_0 fnfsb4t_3 wnf fnfsb4t_1 wal fnfsb4t_1 sup_set_class fnfsb4t_2 sup_set_class wceq fnfsb4t_1 wal fnfsb4t_3 sup_set_class fnfsb4t_1 sup_set_class wceq fnfsb4t_3 wal wn fnfsb4t_3 sup_set_class fnfsb4t_2 sup_set_class wceq fnfsb4t_3 wal wn wa fnfsb4t_0 fnfsb4t_1 fnfsb4t_2 wsb fnfsb4t_3 wnf wi fnfsb4t_0 fnfsb4t_3 wnf fnfsb4t_1 wal fnfsb4t_1 sup_set_class fnfsb4t_2 sup_set_class wceq fnfsb4t_1 wal fnfsb4t_0 fnfsb4t_1 fnfsb4t_2 wsb fnfsb4t_3 wnf fnfsb4t_3 sup_set_class fnfsb4t_1 sup_set_class wceq fnfsb4t_3 wal wn fnfsb4t_3 sup_set_class fnfsb4t_2 sup_set_class wceq fnfsb4t_3 wal wn wa fnfsb4t_0 fnfsb4t_3 wnf fnfsb4t_1 sup_set_class fnfsb4t_2 sup_set_class wceq fnfsb4t_1 wal fnfsb4t_0 fnfsb4t_1 fnfsb4t_2 wsb fnfsb4t_3 wnf wi fnfsb4t_1 fnfsb4t_1 sup_set_class fnfsb4t_2 sup_set_class wceq fnfsb4t_1 wal fnfsb4t_0 fnfsb4t_3 wnf fnfsb4t_0 fnfsb4t_1 fnfsb4t_2 wsb fnfsb4t_3 wnf fnfsb4t_0 fnfsb4t_0 fnfsb4t_1 fnfsb4t_2 wsb fnfsb4t_1 fnfsb4t_2 fnfsb4t_3 fnfsb4t_1 sup_set_class fnfsb4t_2 sup_set_class wceq fnfsb4t_0 fnfsb4t_0 fnfsb4t_1 fnfsb4t_2 wsb wb fnfsb4t_1 fnfsb4t_0 fnfsb4t_1 fnfsb4t_2 sbequ12 sps drnf2 biimpcd sps a1dd fnfsb4t_0 fnfsb4t_3 wnf fnfsb4t_1 wal fnfsb4t_3 sup_set_class fnfsb4t_1 sup_set_class wceq fnfsb4t_3 wal wn fnfsb4t_3 sup_set_class fnfsb4t_2 sup_set_class wceq fnfsb4t_3 wal wn wa fnfsb4t_0 fnfsb4t_1 fnfsb4t_2 wsb fnfsb4t_3 wnf wi fnfsb4t_1 sup_set_class fnfsb4t_2 sup_set_class wceq fnfsb4t_1 wal wn fnfsb4t_3 sup_set_class fnfsb4t_1 sup_set_class wceq fnfsb4t_3 wal wn fnfsb4t_3 sup_set_class fnfsb4t_2 sup_set_class wceq fnfsb4t_3 wal wn wa fnfsb4t_1 sup_set_class fnfsb4t_2 sup_set_class wceq fnfsb4t_0 wi fnfsb4t_1 wal fnfsb4t_3 wnf wi fnfsb4t_0 fnfsb4t_3 wnf fnfsb4t_1 wal fnfsb4t_3 sup_set_class fnfsb4t_1 sup_set_class wceq fnfsb4t_3 wal wn fnfsb4t_3 sup_set_class fnfsb4t_2 sup_set_class wceq fnfsb4t_3 wal wn wa fnfsb4t_1 sup_set_class fnfsb4t_2 sup_set_class wceq fnfsb4t_0 wi fnfsb4t_1 wal fnfsb4t_3 wnf fnfsb4t_0 fnfsb4t_3 wnf fnfsb4t_1 wal fnfsb4t_3 sup_set_class fnfsb4t_1 sup_set_class wceq fnfsb4t_3 wal wn fnfsb4t_3 sup_set_class fnfsb4t_2 sup_set_class wceq fnfsb4t_3 wal wn wa wa fnfsb4t_1 sup_set_class fnfsb4t_2 sup_set_class wceq fnfsb4t_0 wi fnfsb4t_3 fnfsb4t_1 fnfsb4t_0 fnfsb4t_3 wnf fnfsb4t_1 wal fnfsb4t_3 sup_set_class fnfsb4t_1 sup_set_class wceq fnfsb4t_3 wal wn fnfsb4t_3 sup_set_class fnfsb4t_2 sup_set_class wceq fnfsb4t_3 wal wn wa fnfsb4t_1 fnfsb4t_0 fnfsb4t_3 wnf fnfsb4t_1 nfa1 fnfsb4t_3 sup_set_class fnfsb4t_1 sup_set_class wceq fnfsb4t_3 wal wn fnfsb4t_3 sup_set_class fnfsb4t_2 sup_set_class wceq fnfsb4t_3 wal wn fnfsb4t_1 fnfsb4t_3 fnfsb4t_1 fnfsb4t_1 nfnae fnfsb4t_3 fnfsb4t_2 fnfsb4t_1 nfnae nfan nfan fnfsb4t_0 fnfsb4t_3 wnf fnfsb4t_1 wal fnfsb4t_3 sup_set_class fnfsb4t_1 sup_set_class wceq fnfsb4t_3 wal wn fnfsb4t_3 sup_set_class fnfsb4t_2 sup_set_class wceq fnfsb4t_3 wal wn wa wa fnfsb4t_1 sup_set_class fnfsb4t_2 sup_set_class wceq fnfsb4t_0 fnfsb4t_3 fnfsb4t_3 sup_set_class fnfsb4t_1 sup_set_class wceq fnfsb4t_3 wal wn fnfsb4t_3 sup_set_class fnfsb4t_2 sup_set_class wceq fnfsb4t_3 wal wn wa fnfsb4t_1 sup_set_class fnfsb4t_2 sup_set_class wceq fnfsb4t_3 wnf fnfsb4t_0 fnfsb4t_3 wnf fnfsb4t_1 wal fnfsb4t_1 fnfsb4t_2 fnfsb4t_3 nfeqf adantl fnfsb4t_0 fnfsb4t_3 wnf fnfsb4t_1 wal fnfsb4t_0 fnfsb4t_3 wnf fnfsb4t_3 sup_set_class fnfsb4t_1 sup_set_class wceq fnfsb4t_3 wal wn fnfsb4t_3 sup_set_class fnfsb4t_2 sup_set_class wceq fnfsb4t_3 wal wn wa fnfsb4t_0 fnfsb4t_3 wnf fnfsb4t_1 sp adantr nfimd nfald ex fnfsb4t_1 sup_set_class fnfsb4t_2 sup_set_class wceq fnfsb4t_1 wal wn fnfsb4t_0 fnfsb4t_1 fnfsb4t_2 wsb fnfsb4t_3 wnf fnfsb4t_1 sup_set_class fnfsb4t_2 sup_set_class wceq fnfsb4t_0 wi fnfsb4t_1 wal fnfsb4t_3 wnf fnfsb4t_3 sup_set_class fnfsb4t_1 sup_set_class wceq fnfsb4t_3 wal wn fnfsb4t_3 sup_set_class fnfsb4t_2 sup_set_class wceq fnfsb4t_3 wal wn wa fnfsb4t_1 sup_set_class fnfsb4t_2 sup_set_class wceq fnfsb4t_1 wal wn fnfsb4t_0 fnfsb4t_1 fnfsb4t_2 wsb fnfsb4t_1 sup_set_class fnfsb4t_2 sup_set_class wceq fnfsb4t_0 wi fnfsb4t_1 wal fnfsb4t_3 fnfsb4t_1 fnfsb4t_2 fnfsb4t_3 nfnae fnfsb4t_0 fnfsb4t_1 fnfsb4t_2 sb4b nfbidf imbi2d syl5ibrcom pm2.61d exp3a fnfsb4t_3 sup_set_class fnfsb4t_2 sup_set_class wceq fnfsb4t_3 wal wn fnfsb4t_0 fnfsb4t_3 fnfsb4t_2 wsb fnfsb4t_3 wnf fnfsb4t_3 sup_set_class fnfsb4t_1 sup_set_class wceq fnfsb4t_3 wal fnfsb4t_0 fnfsb4t_1 fnfsb4t_2 wsb fnfsb4t_3 wnf fnfsb4t_0 fnfsb4t_3 fnfsb4t_2 nfsb2 fnfsb4t_0 fnfsb4t_3 fnfsb4t_2 wsb fnfsb4t_0 fnfsb4t_1 fnfsb4t_2 wsb fnfsb4t_3 fnfsb4t_1 fnfsb4t_3 fnfsb4t_0 fnfsb4t_3 fnfsb4t_1 fnfsb4t_2 drsb1 drnf2 syl5ib pm2.61d2 $.
$}
$( A variable not free remains so after substitution with a distinct
       variable.  (Contributed by NM, 5-Aug-1993.)  (Revised by Mario Carneiro,
       4-Oct-2016.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	fnfsb4_0 $f wff ph $.
	fnfsb4_1 $f set x $.
	fnfsb4_2 $f set y $.
	fnfsb4_3 $f set z $.
	enfsb4_0 $e |- F/ z ph $.
	nfsb4 $p |- ( -. A. z z = y -> F/ z [ y / x ] ph ) $= fnfsb4_0 fnfsb4_3 wnf fnfsb4_3 sup_set_class fnfsb4_2 sup_set_class wceq fnfsb4_3 wal wn fnfsb4_0 fnfsb4_1 fnfsb4_2 wsb fnfsb4_3 wnf wi fnfsb4_1 fnfsb4_0 fnfsb4_1 fnfsb4_2 fnfsb4_3 nfsb4t enfsb4_0 mpg $.
$}
$( Deduction form of ~ dvelimf .  This version may be useful if we want to
       avoid ~ ax-17 and use ~ ax-16 instead.  (Contributed by NM,
       7-Apr-2004.)  (Revised by Mario Carneiro, 6-Oct-2016.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	$v y $.
	$v z $.
	fdvelimdf_0 $f wff ph $.
	fdvelimdf_1 $f wff ps $.
	fdvelimdf_2 $f wff ch $.
	fdvelimdf_3 $f set x $.
	fdvelimdf_4 $f set y $.
	fdvelimdf_5 $f set z $.
	edvelimdf_0 $e |- F/ x ph $.
	edvelimdf_1 $e |- F/ z ph $.
	edvelimdf_2 $e |- ( ph -> F/ x ps ) $.
	edvelimdf_3 $e |- ( ph -> F/ z ch ) $.
	edvelimdf_4 $e |- ( ph -> ( z = y -> ( ps <-> ch ) ) ) $.
	dvelimdf $p |- ( ph -> ( -. A. x x = y -> F/ x ch ) ) $= fdvelimdf_0 fdvelimdf_3 sup_set_class fdvelimdf_4 sup_set_class wceq fdvelimdf_3 wal wn fdvelimdf_2 fdvelimdf_3 wnf fdvelimdf_0 fdvelimdf_3 sup_set_class fdvelimdf_4 sup_set_class wceq fdvelimdf_3 wal wn wa fdvelimdf_1 fdvelimdf_5 fdvelimdf_4 wsb fdvelimdf_3 wnf fdvelimdf_2 fdvelimdf_3 wnf fdvelimdf_0 fdvelimdf_3 sup_set_class fdvelimdf_4 sup_set_class wceq fdvelimdf_3 wal wn fdvelimdf_1 fdvelimdf_5 fdvelimdf_4 wsb fdvelimdf_3 wnf fdvelimdf_0 fdvelimdf_1 fdvelimdf_3 wnf fdvelimdf_5 wal fdvelimdf_3 sup_set_class fdvelimdf_4 sup_set_class wceq fdvelimdf_3 wal wn fdvelimdf_1 fdvelimdf_5 fdvelimdf_4 wsb fdvelimdf_3 wnf wi fdvelimdf_0 fdvelimdf_1 fdvelimdf_3 wnf fdvelimdf_5 edvelimdf_1 edvelimdf_2 alrimi fdvelimdf_1 fdvelimdf_5 fdvelimdf_4 fdvelimdf_3 nfsb4t syl imp fdvelimdf_0 fdvelimdf_3 sup_set_class fdvelimdf_4 sup_set_class wceq fdvelimdf_3 wal wn wa fdvelimdf_1 fdvelimdf_5 fdvelimdf_4 wsb fdvelimdf_2 fdvelimdf_3 fdvelimdf_0 fdvelimdf_3 sup_set_class fdvelimdf_4 sup_set_class wceq fdvelimdf_3 wal wn fdvelimdf_3 edvelimdf_0 fdvelimdf_3 fdvelimdf_4 fdvelimdf_3 nfnae nfan fdvelimdf_0 fdvelimdf_1 fdvelimdf_5 fdvelimdf_4 wsb fdvelimdf_2 wb fdvelimdf_3 sup_set_class fdvelimdf_4 sup_set_class wceq fdvelimdf_3 wal wn fdvelimdf_0 fdvelimdf_1 fdvelimdf_2 fdvelimdf_5 fdvelimdf_4 edvelimdf_1 edvelimdf_3 edvelimdf_4 sbied adantr nfbidf mpbid ex $.
$}
$( A composition law for substitution.  (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	fsbco_0 $f wff ph $.
	fsbco_1 $f set x $.
	fsbco_2 $f set y $.
	sbco $p |- ( [ y / x ] [ x / y ] ph <-> [ y / x ] ph ) $= fsbco_0 fsbco_2 fsbco_1 wsb fsbco_0 wb fsbco_1 fsbco_2 wsb fsbco_0 fsbco_2 fsbco_1 wsb fsbco_1 fsbco_2 wsb fsbco_0 fsbco_1 fsbco_2 wsb wb fsbco_2 sup_set_class fsbco_1 sup_set_class wceq fsbco_1 fsbco_2 wsb fsbco_0 fsbco_2 fsbco_1 wsb fsbco_0 wb fsbco_1 fsbco_2 wsb fsbco_1 fsbco_2 equsb2 fsbco_2 sup_set_class fsbco_1 sup_set_class wceq fsbco_0 fsbco_2 fsbco_1 wsb fsbco_0 wb fsbco_1 fsbco_2 fsbco_2 sup_set_class fsbco_1 sup_set_class wceq fsbco_0 fsbco_0 fsbco_2 fsbco_1 wsb fsbco_0 fsbco_2 fsbco_1 sbequ12 bicomd sbimi ax-mp fsbco_0 fsbco_2 fsbco_1 wsb fsbco_0 fsbco_1 fsbco_2 sbbi mpbi $.
$}
$( An identity law for substitution.  (Contributed by NM, 5-Aug-1993.)
       (Revised by Mario Carneiro, 6-Oct-2016.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	fsbid2_0 $f wff ph $.
	fsbid2_1 $f set x $.
	fsbid2_2 $f set y $.
	esbid2_0 $e |- F/ x ph $.
	sbid2 $p |- ( [ y / x ] [ x / y ] ph <-> ph ) $= fsbid2_0 fsbid2_2 fsbid2_1 wsb fsbid2_1 fsbid2_2 wsb fsbid2_0 fsbid2_1 fsbid2_2 wsb fsbid2_0 fsbid2_0 fsbid2_1 fsbid2_2 sbco fsbid2_0 fsbid2_1 fsbid2_2 esbid2_0 sbf bitri $.
$}
$( An idempotent law for substitution.  (Contributed by NM, 30-Jun-1994.)
     (Proof shortened by Andrew Salmon, 25-May-2011.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	fsbidm_0 $f wff ph $.
	fsbidm_1 $f set x $.
	fsbidm_2 $f set y $.
	sbidm $p |- ( [ y / x ] [ y / x ] ph <-> [ y / x ] ph ) $= fsbidm_0 fsbidm_1 fsbidm_2 wsb fsbidm_0 wb fsbidm_1 fsbidm_2 wsb fsbidm_0 fsbidm_1 fsbidm_2 wsb fsbidm_1 fsbidm_2 wsb fsbidm_0 fsbidm_1 fsbidm_2 wsb wb fsbidm_2 sup_set_class fsbidm_1 sup_set_class wceq fsbidm_1 fsbidm_2 wsb fsbidm_0 fsbidm_1 fsbidm_2 wsb fsbidm_0 wb fsbidm_1 fsbidm_2 wsb fsbidm_1 fsbidm_2 equsb2 fsbidm_2 sup_set_class fsbidm_1 sup_set_class wceq fsbidm_0 fsbidm_1 fsbidm_2 wsb fsbidm_0 wb fsbidm_1 fsbidm_2 fsbidm_0 fsbidm_2 fsbidm_1 sbequ12r sbimi ax-mp fsbidm_0 fsbidm_1 fsbidm_2 wsb fsbidm_0 fsbidm_1 fsbidm_2 sbbi mpbi $.
$}
$( A composition law for substitution.  (Contributed by NM, 30-Jun-1994.)
       (Revised by Mario Carneiro, 6-Oct-2016.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	fsbco2_0 $f wff ph $.
	fsbco2_1 $f set x $.
	fsbco2_2 $f set y $.
	fsbco2_3 $f set z $.
	esbco2_0 $e |- F/ z ph $.
	sbco2 $p |- ( [ y / z ] [ z / x ] ph <-> [ y / x ] ph ) $= fsbco2_1 sup_set_class fsbco2_2 sup_set_class wceq fsbco2_1 wal fsbco2_0 fsbco2_1 fsbco2_3 wsb fsbco2_3 fsbco2_2 wsb fsbco2_0 fsbco2_1 fsbco2_2 wsb wb fsbco2_1 sup_set_class fsbco2_2 sup_set_class wceq fsbco2_0 fsbco2_1 fsbco2_3 wsb fsbco2_3 fsbco2_2 wsb fsbco2_0 fsbco2_1 fsbco2_2 wsb wb fsbco2_1 fsbco2_1 sup_set_class fsbco2_2 sup_set_class wceq fsbco2_0 fsbco2_0 fsbco2_1 fsbco2_3 wsb fsbco2_3 fsbco2_2 wsb fsbco2_0 fsbco2_1 fsbco2_2 wsb fsbco2_0 fsbco2_0 fsbco2_1 fsbco2_3 wsb fsbco2_3 fsbco2_1 wsb fsbco2_1 sup_set_class fsbco2_2 sup_set_class wceq fsbco2_0 fsbco2_1 fsbco2_3 wsb fsbco2_3 fsbco2_2 wsb fsbco2_0 fsbco2_3 fsbco2_1 esbco2_0 sbid2 fsbco2_0 fsbco2_1 fsbco2_3 wsb fsbco2_1 fsbco2_2 fsbco2_3 sbequ syl5bbr fsbco2_0 fsbco2_1 fsbco2_2 sbequ12 bitr3d sps fsbco2_1 sup_set_class fsbco2_2 sup_set_class wceq fsbco2_1 wal wn fsbco2_0 fsbco2_1 fsbco2_2 wsb fsbco2_0 fsbco2_1 fsbco2_3 wsb fsbco2_3 fsbco2_2 wsb fsbco2_1 sup_set_class fsbco2_2 sup_set_class wceq fsbco2_1 wal wn fsbco2_0 fsbco2_0 fsbco2_1 fsbco2_3 wsb fsbco2_3 fsbco2_2 wsb fsbco2_1 fsbco2_2 fsbco2_1 fsbco2_2 fsbco2_1 nfnae fsbco2_0 fsbco2_1 fsbco2_3 wsb fsbco2_3 fsbco2_2 fsbco2_1 fsbco2_0 fsbco2_1 fsbco2_3 esbco2_0 nfs1 nfsb4 fsbco2_1 sup_set_class fsbco2_2 sup_set_class wceq fsbco2_0 fsbco2_0 fsbco2_1 fsbco2_3 wsb fsbco2_3 fsbco2_2 wsb wb wi fsbco2_1 sup_set_class fsbco2_2 sup_set_class wceq fsbco2_1 wal wn fsbco2_0 fsbco2_0 fsbco2_1 fsbco2_3 wsb fsbco2_3 fsbco2_1 wsb fsbco2_1 sup_set_class fsbco2_2 sup_set_class wceq fsbco2_0 fsbco2_1 fsbco2_3 wsb fsbco2_3 fsbco2_2 wsb fsbco2_0 fsbco2_3 fsbco2_1 esbco2_0 sbid2 fsbco2_0 fsbco2_1 fsbco2_3 wsb fsbco2_1 fsbco2_2 fsbco2_3 sbequ syl5bbr a1i sbied bicomd pm2.61i $.
$}
$( A composition law for substitution.  (Contributed by NM, 5-Aug-1993.)
       (Revised by Mario Carneiro, 6-Oct-2016.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v z $.
	fsbco2d_0 $f wff ph $.
	fsbco2d_1 $f wff ps $.
	fsbco2d_2 $f set x $.
	fsbco2d_3 $f set y $.
	fsbco2d_4 $f set z $.
	esbco2d_0 $e |- F/ x ph $.
	esbco2d_1 $e |- F/ z ph $.
	esbco2d_2 $e |- ( ph -> F/ z ps ) $.
	sbco2d $p |- ( ph -> ( [ y / z ] [ z / x ] ps <-> [ y / x ] ps ) ) $= fsbco2d_0 fsbco2d_1 fsbco2d_2 fsbco2d_4 wsb fsbco2d_4 fsbco2d_3 wsb fsbco2d_1 fsbco2d_2 fsbco2d_3 wsb fsbco2d_0 fsbco2d_1 wi fsbco2d_2 fsbco2d_4 wsb fsbco2d_4 fsbco2d_3 wsb fsbco2d_0 fsbco2d_1 wi fsbco2d_2 fsbco2d_3 wsb fsbco2d_0 fsbco2d_1 fsbco2d_2 fsbco2d_4 wsb fsbco2d_4 fsbco2d_3 wsb wi fsbco2d_0 fsbco2d_1 fsbco2d_2 fsbco2d_3 wsb wi fsbco2d_0 fsbco2d_1 wi fsbco2d_2 fsbco2d_3 fsbco2d_4 fsbco2d_0 fsbco2d_1 fsbco2d_4 esbco2d_1 esbco2d_2 nfim1 sbco2 fsbco2d_0 fsbco2d_1 wi fsbco2d_2 fsbco2d_4 wsb fsbco2d_4 fsbco2d_3 wsb fsbco2d_0 fsbco2d_1 fsbco2d_2 fsbco2d_4 wsb wi fsbco2d_4 fsbco2d_3 wsb fsbco2d_0 fsbco2d_1 fsbco2d_2 fsbco2d_4 wsb fsbco2d_4 fsbco2d_3 wsb wi fsbco2d_0 fsbco2d_1 wi fsbco2d_2 fsbco2d_4 wsb fsbco2d_0 fsbco2d_1 fsbco2d_2 fsbco2d_4 wsb wi fsbco2d_4 fsbco2d_3 fsbco2d_0 fsbco2d_1 fsbco2d_2 fsbco2d_4 esbco2d_0 sbrim sbbii fsbco2d_0 fsbco2d_1 fsbco2d_2 fsbco2d_4 wsb fsbco2d_4 fsbco2d_3 esbco2d_1 sbrim bitri fsbco2d_0 fsbco2d_1 fsbco2d_2 fsbco2d_3 esbco2d_0 sbrim 3bitr3i pm5.74ri $.
$}
$( A composition law for substitution.  (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	fsbco3_0 $f wff ph $.
	fsbco3_1 $f set x $.
	fsbco3_2 $f set y $.
	fsbco3_3 $f set z $.
	sbco3 $p |- ( [ z / y ] [ y / x ] ph <-> [ z / x ] [ x / y ] ph ) $= fsbco3_1 sup_set_class fsbco3_2 sup_set_class wceq fsbco3_1 wal fsbco3_0 fsbco3_1 fsbco3_2 wsb fsbco3_2 fsbco3_3 wsb fsbco3_0 fsbco3_2 fsbco3_1 wsb fsbco3_1 fsbco3_3 wsb wb fsbco3_1 sup_set_class fsbco3_2 sup_set_class wceq fsbco3_1 wal fsbco3_0 fsbco3_1 fsbco3_2 wsb fsbco3_1 fsbco3_3 wsb fsbco3_0 fsbco3_1 fsbco3_2 wsb fsbco3_2 fsbco3_3 wsb fsbco3_0 fsbco3_2 fsbco3_1 wsb fsbco3_1 fsbco3_3 wsb fsbco3_0 fsbco3_1 fsbco3_2 wsb fsbco3_1 fsbco3_2 fsbco3_3 drsb1 fsbco3_1 sup_set_class fsbco3_2 sup_set_class wceq fsbco3_1 wal fsbco3_0 fsbco3_1 fsbco3_2 wsb fsbco3_0 fsbco3_2 fsbco3_1 wsb wb fsbco3_1 wal fsbco3_0 fsbco3_1 fsbco3_2 wsb fsbco3_1 fsbco3_3 wsb fsbco3_0 fsbco3_2 fsbco3_1 wsb fsbco3_1 fsbco3_3 wsb wb fsbco3_1 sup_set_class fsbco3_2 sup_set_class wceq fsbco3_0 fsbco3_1 fsbco3_2 wsb fsbco3_0 fsbco3_2 fsbco3_1 wsb wb fsbco3_1 fsbco3_0 fsbco3_1 fsbco3_2 sbequ12a alimi fsbco3_0 fsbco3_1 fsbco3_2 wsb fsbco3_0 fsbco3_2 fsbco3_1 wsb fsbco3_1 fsbco3_3 spsbbi syl bitr3d fsbco3_0 fsbco3_2 fsbco3_1 wsb fsbco3_1 fsbco3_3 wsb fsbco3_0 fsbco3_1 fsbco3_2 wsb fsbco3_2 fsbco3_1 wsb fsbco3_1 fsbco3_3 wsb fsbco3_1 sup_set_class fsbco3_2 sup_set_class wceq fsbco3_1 wal wn fsbco3_0 fsbco3_1 fsbco3_2 wsb fsbco3_2 fsbco3_3 wsb fsbco3_0 fsbco3_1 fsbco3_2 wsb fsbco3_2 fsbco3_1 wsb fsbco3_0 fsbco3_2 fsbco3_1 wsb fsbco3_1 fsbco3_3 fsbco3_0 fsbco3_2 fsbco3_1 sbco sbbii fsbco3_1 sup_set_class fsbco3_2 sup_set_class wceq fsbco3_1 wal wn fsbco3_0 fsbco3_1 fsbco3_2 wsb fsbco3_2 fsbco3_3 fsbco3_1 fsbco3_1 fsbco3_2 fsbco3_2 nfnae fsbco3_1 fsbco3_2 fsbco3_1 nfnae fsbco3_0 fsbco3_1 fsbco3_2 nfsb2 sbco2d syl5rbbr pm2.61i $.
$}
$( A commutativity law for substitution.  (Contributed by NM,
     27-May-1997.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	fsbcom_0 $f wff ph $.
	fsbcom_1 $f set x $.
	fsbcom_2 $f set y $.
	fsbcom_3 $f set z $.
	sbcom $p |- ( [ y / z ] [ y / x ] ph <-> [ y / x ] [ y / z ] ph ) $= fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_1 wal fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_3 wal fsbcom_0 fsbcom_1 fsbcom_2 wsb fsbcom_3 fsbcom_2 wsb fsbcom_0 fsbcom_3 fsbcom_2 wsb fsbcom_1 fsbcom_2 wsb wb fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_1 wal wn fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_3 wal wn fsbcom_0 fsbcom_1 fsbcom_2 wsb fsbcom_3 fsbcom_2 wsb fsbcom_0 fsbcom_3 fsbcom_2 wsb fsbcom_1 fsbcom_2 wsb wb fsbcom_1 sup_set_class fsbcom_3 sup_set_class wceq fsbcom_1 wal fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_1 wal wn fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_3 wal wn wa fsbcom_0 fsbcom_1 fsbcom_2 wsb fsbcom_3 fsbcom_2 wsb fsbcom_0 fsbcom_3 fsbcom_2 wsb fsbcom_1 fsbcom_2 wsb wb fsbcom_1 sup_set_class fsbcom_3 sup_set_class wceq fsbcom_1 wal fsbcom_0 fsbcom_1 fsbcom_2 wsb fsbcom_3 fsbcom_2 wsb fsbcom_0 fsbcom_3 fsbcom_2 wsb fsbcom_1 fsbcom_2 wsb wb fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_1 wal wn fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_3 wal wn wa fsbcom_1 sup_set_class fsbcom_3 sup_set_class wceq fsbcom_1 wal fsbcom_0 fsbcom_1 fsbcom_2 wsb fsbcom_1 fsbcom_2 wsb fsbcom_0 fsbcom_1 fsbcom_2 wsb fsbcom_3 fsbcom_2 wsb fsbcom_0 fsbcom_3 fsbcom_2 wsb fsbcom_1 fsbcom_2 wsb fsbcom_0 fsbcom_1 fsbcom_2 wsb fsbcom_1 fsbcom_3 fsbcom_2 drsb1 fsbcom_1 sup_set_class fsbcom_3 sup_set_class wceq fsbcom_1 wal fsbcom_0 fsbcom_1 fsbcom_2 wsb fsbcom_0 fsbcom_3 fsbcom_2 wsb fsbcom_1 fsbcom_2 fsbcom_1 fsbcom_3 fsbcom_1 nfae fsbcom_0 fsbcom_1 fsbcom_3 fsbcom_2 drsb1 sbbid bitr3d adantr fsbcom_1 sup_set_class fsbcom_3 sup_set_class wceq fsbcom_1 wal wn fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_1 wal wn fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_3 wal wn wa wa fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_0 wi fsbcom_1 wal wi fsbcom_3 wal fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_0 wi fsbcom_3 wal wi fsbcom_1 wal fsbcom_0 fsbcom_1 fsbcom_2 wsb fsbcom_3 fsbcom_2 wsb fsbcom_0 fsbcom_3 fsbcom_2 wsb fsbcom_1 fsbcom_2 wsb fsbcom_1 sup_set_class fsbcom_3 sup_set_class wceq fsbcom_1 wal wn fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_1 wal wn fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_3 wal wn wa wa fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_0 wi wi fsbcom_1 wal fsbcom_3 wal fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_0 wi fsbcom_1 wal wi fsbcom_3 wal fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_0 wi fsbcom_3 wal wi fsbcom_1 wal fsbcom_1 sup_set_class fsbcom_3 sup_set_class wceq fsbcom_1 wal wn fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_1 wal wn fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_0 wi wi fsbcom_1 wal fsbcom_3 wal fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_0 wi fsbcom_1 wal wi fsbcom_3 wal wb fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_3 wal wn fsbcom_1 sup_set_class fsbcom_3 sup_set_class wceq fsbcom_1 wal wn fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_1 wal wn wa fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_0 wi wi fsbcom_1 wal fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_0 wi fsbcom_1 wal wi fsbcom_3 fsbcom_1 sup_set_class fsbcom_3 sup_set_class wceq fsbcom_1 wal wn fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_1 wal wn fsbcom_3 fsbcom_1 fsbcom_3 fsbcom_3 nfnae fsbcom_1 fsbcom_2 fsbcom_3 nfnae nfan fsbcom_1 sup_set_class fsbcom_3 sup_set_class wceq fsbcom_1 wal wn fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_1 wal wn wa fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_1 wnf fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_0 wi wi fsbcom_1 wal fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_0 wi fsbcom_1 wal wi wb fsbcom_3 fsbcom_2 fsbcom_1 nfeqf fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_0 wi fsbcom_1 19.21t syl albid adantrr fsbcom_1 sup_set_class fsbcom_3 sup_set_class wceq fsbcom_1 wal wn fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_3 wal wn fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_0 wi wi fsbcom_1 wal fsbcom_3 wal fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_0 wi fsbcom_3 wal wi fsbcom_1 wal wb fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_1 wal wn fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_0 wi wi fsbcom_1 wal fsbcom_3 wal fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_0 wi wi fsbcom_3 wal fsbcom_1 wal fsbcom_1 sup_set_class fsbcom_3 sup_set_class wceq fsbcom_1 wal wn fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_3 wal wn wa fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_0 wi fsbcom_3 wal wi fsbcom_1 wal fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_0 wi wi fsbcom_3 fsbcom_1 alcom fsbcom_1 sup_set_class fsbcom_3 sup_set_class wceq fsbcom_1 wal wn fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_3 wal wn wa fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_0 wi wi fsbcom_3 wal fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_0 wi fsbcom_3 wal wi fsbcom_1 fsbcom_1 sup_set_class fsbcom_3 sup_set_class wceq fsbcom_1 wal wn fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_3 wal wn fsbcom_1 fsbcom_1 fsbcom_3 fsbcom_1 nfnae fsbcom_3 fsbcom_2 fsbcom_1 nfnae nfan fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_0 wi wi fsbcom_3 wal fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_0 wi wi fsbcom_3 wal fsbcom_1 sup_set_class fsbcom_3 sup_set_class wceq fsbcom_1 wal wn fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_3 wal wn wa fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_0 wi fsbcom_3 wal wi fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_0 wi wi fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_0 wi wi fsbcom_3 fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_0 bi2.04 albii fsbcom_1 sup_set_class fsbcom_3 sup_set_class wceq fsbcom_1 wal wn fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_3 wal wn wa fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_3 wnf fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_0 wi wi fsbcom_3 wal fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_0 wi fsbcom_3 wal wi wb fsbcom_1 sup_set_class fsbcom_3 sup_set_class wceq fsbcom_1 wal wn fsbcom_3 sup_set_class fsbcom_1 sup_set_class wceq fsbcom_3 wal wn fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_3 wal wn fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_3 wnf fsbcom_3 sup_set_class fsbcom_1 sup_set_class wceq fsbcom_3 wal fsbcom_1 sup_set_class fsbcom_3 sup_set_class wceq fsbcom_1 wal fsbcom_3 fsbcom_1 aecom con3i fsbcom_1 fsbcom_2 fsbcom_3 nfeqf sylan fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_0 wi fsbcom_3 19.21t syl syl5bb albid syl5bb adantrl bitr3d fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_1 wal wn fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_3 wal wn wa fsbcom_0 fsbcom_1 fsbcom_2 wsb fsbcom_3 fsbcom_2 wsb fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_0 wi fsbcom_1 wal wi fsbcom_3 wal wb fsbcom_1 sup_set_class fsbcom_3 sup_set_class wceq fsbcom_1 wal wn fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_3 wal wn fsbcom_0 fsbcom_1 fsbcom_2 wsb fsbcom_3 fsbcom_2 wsb fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_0 fsbcom_1 fsbcom_2 wsb wi fsbcom_3 wal fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_1 wal wn fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_0 wi fsbcom_1 wal wi fsbcom_3 wal fsbcom_0 fsbcom_1 fsbcom_2 wsb fsbcom_3 fsbcom_2 sb4b fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_1 wal wn fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_0 fsbcom_1 fsbcom_2 wsb wi fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_0 wi fsbcom_1 wal wi fsbcom_3 fsbcom_1 fsbcom_2 fsbcom_3 nfnae fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_1 wal wn fsbcom_0 fsbcom_1 fsbcom_2 wsb fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_0 wi fsbcom_1 wal fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_0 fsbcom_1 fsbcom_2 sb4b imbi2d albid sylan9bbr adantl fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_1 wal wn fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_3 wal wn wa fsbcom_0 fsbcom_3 fsbcom_2 wsb fsbcom_1 fsbcom_2 wsb fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_0 wi fsbcom_3 wal wi fsbcom_1 wal wb fsbcom_1 sup_set_class fsbcom_3 sup_set_class wceq fsbcom_1 wal wn fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_1 wal wn fsbcom_0 fsbcom_3 fsbcom_2 wsb fsbcom_1 fsbcom_2 wsb fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_0 fsbcom_3 fsbcom_2 wsb wi fsbcom_1 wal fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_3 wal wn fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_0 wi fsbcom_3 wal wi fsbcom_1 wal fsbcom_0 fsbcom_3 fsbcom_2 wsb fsbcom_1 fsbcom_2 sb4b fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_3 wal wn fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_0 fsbcom_3 fsbcom_2 wsb wi fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_0 wi fsbcom_3 wal wi fsbcom_1 fsbcom_3 fsbcom_2 fsbcom_1 nfnae fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_3 wal wn fsbcom_0 fsbcom_3 fsbcom_2 wsb fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_0 wi fsbcom_3 wal fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_0 fsbcom_3 fsbcom_2 sb4b imbi2d albid sylan9bb adantl 3bitr4d pm2.61ian ex fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_1 wal fsbcom_0 fsbcom_3 fsbcom_2 wsb fsbcom_0 fsbcom_1 fsbcom_2 wsb fsbcom_3 fsbcom_2 wsb fsbcom_0 fsbcom_3 fsbcom_2 wsb fsbcom_1 fsbcom_2 wsb fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_1 wal fsbcom_0 fsbcom_0 fsbcom_1 fsbcom_2 wsb fsbcom_3 fsbcom_2 fsbcom_1 fsbcom_2 fsbcom_3 nfae fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_0 fsbcom_0 fsbcom_1 fsbcom_2 wsb wb fsbcom_1 fsbcom_0 fsbcom_1 fsbcom_2 sbequ12 sps sbbid fsbcom_1 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_0 fsbcom_3 fsbcom_2 wsb fsbcom_0 fsbcom_3 fsbcom_2 wsb fsbcom_1 fsbcom_2 wsb wb fsbcom_1 fsbcom_0 fsbcom_3 fsbcom_2 wsb fsbcom_1 fsbcom_2 sbequ12 sps bitr3d fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_3 wal fsbcom_0 fsbcom_1 fsbcom_2 wsb fsbcom_0 fsbcom_1 fsbcom_2 wsb fsbcom_3 fsbcom_2 wsb fsbcom_0 fsbcom_3 fsbcom_2 wsb fsbcom_1 fsbcom_2 wsb fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_0 fsbcom_1 fsbcom_2 wsb fsbcom_0 fsbcom_1 fsbcom_2 wsb fsbcom_3 fsbcom_2 wsb wb fsbcom_3 fsbcom_0 fsbcom_1 fsbcom_2 wsb fsbcom_3 fsbcom_2 sbequ12 sps fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_3 wal fsbcom_0 fsbcom_0 fsbcom_3 fsbcom_2 wsb fsbcom_1 fsbcom_2 fsbcom_3 fsbcom_2 fsbcom_1 nfae fsbcom_3 sup_set_class fsbcom_2 sup_set_class wceq fsbcom_0 fsbcom_0 fsbcom_3 fsbcom_2 wsb wb fsbcom_3 fsbcom_0 fsbcom_3 fsbcom_2 sbequ12 sps sbbid bitr3d pm2.61ii $.
$}
$( Reversed substitution.  (Contributed by NM, 3-Feb-2005.)  (Revised by
       Mario Carneiro, 6-Oct-2016.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	fsb5rf_0 $f wff ph $.
	fsb5rf_1 $f set x $.
	fsb5rf_2 $f set y $.
	esb5rf_0 $e |- F/ y ph $.
	sb5rf $p |- ( ph <-> E. y ( y = x /\ [ y / x ] ph ) ) $= fsb5rf_0 fsb5rf_2 sup_set_class fsb5rf_1 sup_set_class wceq fsb5rf_0 fsb5rf_1 fsb5rf_2 wsb wa fsb5rf_2 wex fsb5rf_0 fsb5rf_0 fsb5rf_1 fsb5rf_2 wsb fsb5rf_2 fsb5rf_1 wsb fsb5rf_2 sup_set_class fsb5rf_1 sup_set_class wceq fsb5rf_0 fsb5rf_1 fsb5rf_2 wsb wa fsb5rf_2 wex fsb5rf_0 fsb5rf_2 fsb5rf_1 esb5rf_0 sbid2 fsb5rf_0 fsb5rf_1 fsb5rf_2 wsb fsb5rf_2 fsb5rf_1 sb1 sylbir fsb5rf_2 sup_set_class fsb5rf_1 sup_set_class wceq fsb5rf_0 fsb5rf_1 fsb5rf_2 wsb wa fsb5rf_0 fsb5rf_2 esb5rf_0 fsb5rf_2 sup_set_class fsb5rf_1 sup_set_class wceq fsb5rf_0 fsb5rf_1 fsb5rf_2 wsb fsb5rf_0 fsb5rf_0 fsb5rf_2 fsb5rf_1 stdpc7 imp exlimi impbii $.
$}
$( Reversed substitution.  (Contributed by NM, 5-Aug-1993.)  (Revised by
       Mario Carneiro, 6-Oct-2016.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	fsb6rf_0 $f wff ph $.
	fsb6rf_1 $f set x $.
	fsb6rf_2 $f set y $.
	esb6rf_0 $e |- F/ y ph $.
	sb6rf $p |- ( ph <-> A. y ( y = x -> [ y / x ] ph ) ) $= fsb6rf_0 fsb6rf_2 sup_set_class fsb6rf_1 sup_set_class wceq fsb6rf_0 fsb6rf_1 fsb6rf_2 wsb wi fsb6rf_2 wal fsb6rf_0 fsb6rf_2 sup_set_class fsb6rf_1 sup_set_class wceq fsb6rf_0 fsb6rf_1 fsb6rf_2 wsb wi fsb6rf_2 esb6rf_0 fsb6rf_2 sup_set_class fsb6rf_1 sup_set_class wceq fsb6rf_0 fsb6rf_0 fsb6rf_1 fsb6rf_2 wsb fsb6rf_0 fsb6rf_0 fsb6rf_1 fsb6rf_2 wsb wi fsb6rf_1 fsb6rf_2 fsb6rf_0 fsb6rf_1 fsb6rf_2 sbequ1 equcoms com12 alrimi fsb6rf_2 sup_set_class fsb6rf_1 sup_set_class wceq fsb6rf_0 fsb6rf_1 fsb6rf_2 wsb wi fsb6rf_2 wal fsb6rf_0 fsb6rf_1 fsb6rf_2 wsb fsb6rf_2 fsb6rf_1 wsb fsb6rf_0 fsb6rf_0 fsb6rf_1 fsb6rf_2 wsb fsb6rf_2 fsb6rf_1 sb2 fsb6rf_0 fsb6rf_2 fsb6rf_1 esb6rf_0 sbid2 sylib impbii $.
$}
$( Substitution of variable in universal quantifier.  (Contributed by NM,
       5-Aug-1993.)  (Revised by Mario Carneiro, 6-Oct-2016.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	fsb8_0 $f wff ph $.
	fsb8_1 $f set x $.
	fsb8_2 $f set y $.
	esb8_0 $e |- F/ y ph $.
	sb8 $p |- ( A. x ph <-> A. y [ y / x ] ph ) $= fsb8_0 fsb8_1 wal fsb8_0 fsb8_1 fsb8_2 wsb fsb8_2 wal fsb8_0 fsb8_1 wal fsb8_0 fsb8_1 fsb8_2 wsb fsb8_2 fsb8_0 fsb8_2 fsb8_1 esb8_0 nfal fsb8_0 fsb8_1 fsb8_2 stdpc4 alrimi fsb8_0 fsb8_1 fsb8_2 wsb fsb8_0 fsb8_2 fsb8_1 fsb8_0 fsb8_1 fsb8_2 esb8_0 nfs1 esb8_0 fsb8_0 fsb8_2 fsb8_1 stdpc7 cbv3 impbii $.
$}
$( Substitution of variable in existential quantifier.  (Contributed by NM,
       12-Aug-1993.)  (Revised by Mario Carneiro, 6-Oct-2016.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	fsb8e_0 $f wff ph $.
	fsb8e_1 $f set x $.
	fsb8e_2 $f set y $.
	esb8e_0 $e |- F/ y ph $.
	sb8e $p |- ( E. x ph <-> E. y [ y / x ] ph ) $= fsb8e_0 wn fsb8e_1 wal wn fsb8e_0 fsb8e_1 fsb8e_2 wsb wn fsb8e_2 wal wn fsb8e_0 fsb8e_1 wex fsb8e_0 fsb8e_1 fsb8e_2 wsb fsb8e_2 wex fsb8e_0 wn fsb8e_1 wal fsb8e_0 fsb8e_1 fsb8e_2 wsb wn fsb8e_2 wal fsb8e_0 wn fsb8e_1 wal fsb8e_0 wn fsb8e_1 fsb8e_2 wsb fsb8e_2 wal fsb8e_0 fsb8e_1 fsb8e_2 wsb wn fsb8e_2 wal fsb8e_0 wn fsb8e_1 fsb8e_2 fsb8e_0 fsb8e_2 esb8e_0 nfn sb8 fsb8e_0 wn fsb8e_1 fsb8e_2 wsb fsb8e_0 fsb8e_1 fsb8e_2 wsb wn fsb8e_2 fsb8e_0 fsb8e_1 fsb8e_2 sbn albii bitri notbii fsb8e_0 fsb8e_1 df-ex fsb8e_0 fsb8e_1 fsb8e_2 wsb fsb8e_2 df-ex 3bitr4i $.
$}
$( Commutation of quantification and substitution variables.  (Contributed by
     NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	fsb9i_0 $f wff ph $.
	fsb9i_1 $f set x $.
	fsb9i_2 $f set y $.
	sb9i $p |- ( A. x [ x / y ] ph -> A. y [ y / x ] ph ) $= fsb9i_2 sup_set_class fsb9i_1 sup_set_class wceq fsb9i_2 wal fsb9i_0 fsb9i_2 fsb9i_1 wsb fsb9i_1 wal fsb9i_0 fsb9i_1 fsb9i_2 wsb fsb9i_2 wal wi fsb9i_2 sup_set_class fsb9i_1 sup_set_class wceq fsb9i_2 wal fsb9i_0 fsb9i_1 fsb9i_2 wsb fsb9i_2 wal fsb9i_0 fsb9i_2 fsb9i_1 wsb fsb9i_1 wal fsb9i_0 fsb9i_1 fsb9i_2 wsb fsb9i_0 fsb9i_2 fsb9i_1 wsb fsb9i_2 fsb9i_1 fsb9i_2 sup_set_class fsb9i_1 sup_set_class wceq fsb9i_2 wal fsb9i_0 fsb9i_2 fsb9i_2 wsb fsb9i_0 fsb9i_1 fsb9i_2 wsb fsb9i_0 fsb9i_2 fsb9i_1 wsb fsb9i_0 fsb9i_2 fsb9i_1 fsb9i_2 drsb1 fsb9i_0 fsb9i_2 fsb9i_1 fsb9i_2 drsb2 bitr3d dral1 biimprd fsb9i_2 sup_set_class fsb9i_1 sup_set_class wceq fsb9i_2 wal wn fsb9i_0 fsb9i_2 fsb9i_1 wsb fsb9i_1 wal fsb9i_0 fsb9i_2 fsb9i_1 wsb fsb9i_2 wal fsb9i_1 wal fsb9i_0 fsb9i_1 fsb9i_2 wsb fsb9i_2 wal fsb9i_2 sup_set_class fsb9i_1 sup_set_class wceq fsb9i_2 wal wn fsb9i_0 fsb9i_2 fsb9i_1 wsb fsb9i_0 fsb9i_2 fsb9i_1 wsb fsb9i_2 wal fsb9i_1 fsb9i_2 fsb9i_1 fsb9i_1 nfnae fsb9i_0 fsb9i_2 fsb9i_1 hbsb2 alimd fsb9i_0 fsb9i_2 fsb9i_1 wsb fsb9i_0 fsb9i_1 fsb9i_2 wsb fsb9i_2 wal fsb9i_2 fsb9i_1 fsb9i_0 fsb9i_2 fsb9i_1 wsb fsb9i_1 wal fsb9i_0 fsb9i_1 fsb9i_2 wsb fsb9i_2 fsb9i_0 fsb9i_2 fsb9i_1 wsb fsb9i_1 wal fsb9i_0 fsb9i_2 fsb9i_1 wsb fsb9i_1 fsb9i_2 wsb fsb9i_0 fsb9i_1 fsb9i_2 wsb fsb9i_0 fsb9i_2 fsb9i_1 wsb fsb9i_1 fsb9i_2 stdpc4 fsb9i_0 fsb9i_1 fsb9i_2 sbco sylib alimi a7s syl6 pm2.61i $.
$}
$( Commutation of quantification and substitution variables.  (Contributed by
     NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	fsb9_0 $f wff ph $.
	fsb9_1 $f set x $.
	fsb9_2 $f set y $.
	sb9 $p |- ( A. x [ x / y ] ph <-> A. y [ y / x ] ph ) $= fsb9_0 fsb9_2 fsb9_1 wsb fsb9_1 wal fsb9_0 fsb9_1 fsb9_2 wsb fsb9_2 wal fsb9_0 fsb9_1 fsb9_2 sb9i fsb9_0 fsb9_2 fsb9_1 sb9i impbii $.
$}
$( This is a version of ~ ax-11o when the variables are distinct.  Axiom
       (C8) of [Monk2] p. 105.  See theorem ~ ax11v2 for the rederivation of
       ~ ax-11o from this theorem.  (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$d x y $.
	fax11v_0 $f wff ph $.
	fax11v_1 $f set x $.
	fax11v_2 $f set y $.
	ax11v $p |- ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) $= fax11v_1 sup_set_class fax11v_2 sup_set_class wceq fax11v_1 wal fax11v_1 sup_set_class fax11v_2 sup_set_class wceq fax11v_0 fax11v_1 sup_set_class fax11v_2 sup_set_class wceq fax11v_0 wi fax11v_1 wal wi wi fax11v_1 sup_set_class fax11v_2 sup_set_class wceq fax11v_1 wal fax11v_0 fax11v_1 sup_set_class fax11v_2 sup_set_class wceq fax11v_0 wi fax11v_1 wal wi fax11v_1 sup_set_class fax11v_2 sup_set_class wceq fax11v_0 fax11v_1 sup_set_class fax11v_2 sup_set_class wceq fax11v_0 wi fax11v_1 sup_set_class fax11v_2 sup_set_class wceq fax11v_1 wal fax11v_1 sup_set_class fax11v_2 sup_set_class wceq fax11v_0 wi fax11v_1 wal fax11v_0 fax11v_1 sup_set_class fax11v_2 sup_set_class wceq ax-1 fax11v_1 sup_set_class fax11v_2 sup_set_class wceq fax11v_0 wi fax11v_1 fax11v_2 ax16 syl5 a1d fax11v_0 fax11v_1 fax11v_2 ax11o pm2.61i $.
$}
$( Two equivalent ways of expressing the proper substitution of ` y ` for
       ` x ` in ` ph ` , when ` x ` and ` y ` are distinct.  Theorem 6.2 of
       [Quine] p. 40.  The proof does not involve ~ df-sb .  (Contributed by
       NM, 14-Apr-2008.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$d x y $.
	fsb56_0 $f wff ph $.
	fsb56_1 $f set x $.
	fsb56_2 $f set y $.
	sb56 $p |- ( E. x ( x = y /\ ph ) <-> A. x ( x = y -> ph ) ) $= fsb56_0 fsb56_1 sup_set_class fsb56_2 sup_set_class wceq fsb56_0 wi fsb56_1 wal fsb56_1 fsb56_2 fsb56_1 sup_set_class fsb56_2 sup_set_class wceq fsb56_0 wi fsb56_1 nfa1 fsb56_1 sup_set_class fsb56_2 sup_set_class wceq fsb56_0 fsb56_1 sup_set_class fsb56_2 sup_set_class wceq fsb56_0 wi fsb56_1 wal fsb56_0 fsb56_1 fsb56_2 ax11v fsb56_1 sup_set_class fsb56_2 sup_set_class wceq fsb56_0 wi fsb56_1 wal fsb56_1 sup_set_class fsb56_2 sup_set_class wceq fsb56_0 fsb56_1 sup_set_class fsb56_2 sup_set_class wceq fsb56_0 wi fsb56_1 sp com12 impbid equsex $.
$}
$( Equivalence for substitution.  Compare Theorem 6.2 of [Quine] p. 40.
       Also proved as Lemmas 16 and 17 of [Tarski] p. 70.  (Contributed by NM,
       18-Aug-1993.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$d x y $.
	fsb6_0 $f wff ph $.
	fsb6_1 $f set x $.
	fsb6_2 $f set y $.
	sb6 $p |- ( [ y / x ] ph <-> A. x ( x = y -> ph ) ) $= fsb6_1 sup_set_class fsb6_2 sup_set_class wceq fsb6_0 wi fsb6_1 sup_set_class fsb6_2 sup_set_class wceq fsb6_0 wa fsb6_1 wex wa fsb6_1 sup_set_class fsb6_2 sup_set_class wceq fsb6_0 wi fsb6_1 sup_set_class fsb6_2 sup_set_class wceq fsb6_0 wi fsb6_1 wal wa fsb6_0 fsb6_1 fsb6_2 wsb fsb6_1 sup_set_class fsb6_2 sup_set_class wceq fsb6_0 wi fsb6_1 wal fsb6_1 sup_set_class fsb6_2 sup_set_class wceq fsb6_0 wa fsb6_1 wex fsb6_1 sup_set_class fsb6_2 sup_set_class wceq fsb6_0 wi fsb6_1 wal fsb6_1 sup_set_class fsb6_2 sup_set_class wceq fsb6_0 wi fsb6_0 fsb6_1 fsb6_2 sb56 anbi2i fsb6_0 fsb6_1 fsb6_2 df-sb fsb6_1 sup_set_class fsb6_2 sup_set_class wceq fsb6_0 wi fsb6_1 wal fsb6_1 sup_set_class fsb6_2 sup_set_class wceq fsb6_0 wi fsb6_1 sup_set_class fsb6_2 sup_set_class wceq fsb6_0 wi fsb6_1 sp pm4.71ri 3bitr4i $.
$}
$( Equivalence for substitution.  Similar to Theorem 6.1 of [Quine] p. 40.
       (Contributed by NM, 18-Aug-1993.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$d x y $.
	fsb5_0 $f wff ph $.
	fsb5_1 $f set x $.
	fsb5_2 $f set y $.
	sb5 $p |- ( [ y / x ] ph <-> E. x ( x = y /\ ph ) ) $= fsb5_0 fsb5_1 fsb5_2 wsb fsb5_1 sup_set_class fsb5_2 sup_set_class wceq fsb5_0 wi fsb5_1 wal fsb5_1 sup_set_class fsb5_2 sup_set_class wceq fsb5_0 wa fsb5_1 wex fsb5_0 fsb5_1 fsb5_2 sb6 fsb5_0 fsb5_1 fsb5_2 sb56 bitr4i $.
$}
$( Lemma for ~ equsb3 .  (Contributed by Raph Levien and FL, 4-Dec-2005.)
       (Proof shortened by Andrew Salmon, 14-Jun-2011.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$d y z $.
	$d x y $.
	fequsb3lem_0 $f set x $.
	fequsb3lem_1 $f set y $.
	fequsb3lem_2 $f set z $.
	equsb3lem $p |- ( [ x / y ] y = z <-> x = z ) $= fequsb3lem_1 sup_set_class fequsb3lem_2 sup_set_class wceq fequsb3lem_0 sup_set_class fequsb3lem_2 sup_set_class wceq fequsb3lem_1 fequsb3lem_0 fequsb3lem_0 sup_set_class fequsb3lem_2 sup_set_class wceq fequsb3lem_1 nfv fequsb3lem_1 fequsb3lem_0 fequsb3lem_2 equequ1 sbie $.
$}
$( Substitution applied to an atomic wff.  (Contributed by Raph Levien and
       FL, 4-Dec-2005.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d w y z $.
	$d w x $.
	iequsb3_0 $f set w $.
	fequsb3_0 $f set x $.
	fequsb3_1 $f set y $.
	fequsb3_2 $f set z $.
	equsb3 $p |- ( [ x / y ] y = z <-> x = z ) $= fequsb3_1 sup_set_class fequsb3_2 sup_set_class wceq fequsb3_1 iequsb3_0 wsb iequsb3_0 fequsb3_0 wsb iequsb3_0 sup_set_class fequsb3_2 sup_set_class wceq iequsb3_0 fequsb3_0 wsb fequsb3_1 sup_set_class fequsb3_2 sup_set_class wceq fequsb3_1 fequsb3_0 wsb fequsb3_0 sup_set_class fequsb3_2 sup_set_class wceq fequsb3_1 sup_set_class fequsb3_2 sup_set_class wceq fequsb3_1 iequsb3_0 wsb iequsb3_0 sup_set_class fequsb3_2 sup_set_class wceq iequsb3_0 fequsb3_0 iequsb3_0 fequsb3_1 fequsb3_2 equsb3lem sbbii fequsb3_1 sup_set_class fequsb3_2 sup_set_class wceq fequsb3_1 fequsb3_0 iequsb3_0 fequsb3_1 sup_set_class fequsb3_2 sup_set_class wceq iequsb3_0 nfv sbco2 fequsb3_0 iequsb3_0 fequsb3_2 equsb3lem 3bitr3i $.
$}
$( Substitution applied to an atomic membership wff.  (Contributed by NM,
       7-Nov-2006.)  (Proof shortened by Andrew Salmon, 14-Jun-2011.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d w y z $.
	$d w x $.
	ielsb3_0 $f set w $.
	felsb3_0 $f set x $.
	felsb3_1 $f set y $.
	felsb3_2 $f set z $.
	elsb3 $p |- ( [ x / y ] y e. z <-> x e. z ) $= ielsb3_0 sup_set_class felsb3_2 sup_set_class wcel ielsb3_0 felsb3_1 wsb felsb3_1 felsb3_0 wsb ielsb3_0 sup_set_class felsb3_2 sup_set_class wcel ielsb3_0 felsb3_0 wsb felsb3_1 sup_set_class felsb3_2 sup_set_class wcel felsb3_1 felsb3_0 wsb felsb3_0 sup_set_class felsb3_2 sup_set_class wcel ielsb3_0 sup_set_class felsb3_2 sup_set_class wcel ielsb3_0 felsb3_0 felsb3_1 ielsb3_0 sup_set_class felsb3_2 sup_set_class wcel felsb3_1 nfv sbco2 ielsb3_0 sup_set_class felsb3_2 sup_set_class wcel ielsb3_0 felsb3_1 wsb felsb3_1 sup_set_class felsb3_2 sup_set_class wcel felsb3_1 felsb3_0 ielsb3_0 sup_set_class felsb3_2 sup_set_class wcel felsb3_1 sup_set_class felsb3_2 sup_set_class wcel ielsb3_0 felsb3_1 felsb3_1 sup_set_class felsb3_2 sup_set_class wcel ielsb3_0 nfv ielsb3_0 felsb3_1 felsb3_2 elequ1 sbie sbbii ielsb3_0 sup_set_class felsb3_2 sup_set_class wcel felsb3_0 sup_set_class felsb3_2 sup_set_class wcel ielsb3_0 felsb3_0 felsb3_0 sup_set_class felsb3_2 sup_set_class wcel ielsb3_0 nfv ielsb3_0 felsb3_0 felsb3_2 elequ1 sbie 3bitr3i $.
$}
$( Substitution applied to an atomic membership wff.  (Contributed by
       Rodolfo Medina, 3-Apr-2010.)  (Proof shortened by Andrew Salmon,
       14-Jun-2011.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d w y z $.
	$d w x $.
	ielsb4_0 $f set w $.
	felsb4_0 $f set x $.
	felsb4_1 $f set y $.
	felsb4_2 $f set z $.
	elsb4 $p |- ( [ x / y ] z e. y <-> z e. x ) $= felsb4_2 sup_set_class ielsb4_0 sup_set_class wcel ielsb4_0 felsb4_1 wsb felsb4_1 felsb4_0 wsb felsb4_2 sup_set_class ielsb4_0 sup_set_class wcel ielsb4_0 felsb4_0 wsb felsb4_2 sup_set_class felsb4_1 sup_set_class wcel felsb4_1 felsb4_0 wsb felsb4_2 sup_set_class felsb4_0 sup_set_class wcel felsb4_2 sup_set_class ielsb4_0 sup_set_class wcel ielsb4_0 felsb4_0 felsb4_1 felsb4_2 sup_set_class ielsb4_0 sup_set_class wcel felsb4_1 nfv sbco2 felsb4_2 sup_set_class ielsb4_0 sup_set_class wcel ielsb4_0 felsb4_1 wsb felsb4_2 sup_set_class felsb4_1 sup_set_class wcel felsb4_1 felsb4_0 felsb4_2 sup_set_class ielsb4_0 sup_set_class wcel felsb4_2 sup_set_class felsb4_1 sup_set_class wcel ielsb4_0 felsb4_1 felsb4_2 sup_set_class felsb4_1 sup_set_class wcel ielsb4_0 nfv ielsb4_0 felsb4_1 felsb4_2 elequ2 sbie sbbii felsb4_2 sup_set_class ielsb4_0 sup_set_class wcel felsb4_2 sup_set_class felsb4_0 sup_set_class wcel ielsb4_0 felsb4_0 felsb4_2 sup_set_class felsb4_0 sup_set_class wcel ielsb4_0 nfv ielsb4_0 felsb4_0 felsb4_2 elequ2 sbie 3bitr3i $.
$}
$( ` x ` is not free in ` [ y / x ] ph ` when ` x ` and ` y ` are
       distinct.  (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$d x y $.
	fhbs1_0 $f wff ph $.
	fhbs1_1 $f set x $.
	fhbs1_2 $f set y $.
	hbs1 $p |- ( [ y / x ] ph -> A. x [ y / x ] ph ) $= fhbs1_1 sup_set_class fhbs1_2 sup_set_class wceq fhbs1_1 wal fhbs1_0 fhbs1_1 fhbs1_2 wsb fhbs1_0 fhbs1_1 fhbs1_2 wsb fhbs1_1 wal wi fhbs1_0 fhbs1_1 fhbs1_2 wsb fhbs1_1 fhbs1_2 ax16 fhbs1_0 fhbs1_1 fhbs1_2 hbsb2 pm2.61i $.
$}
$( ` x ` is not free in ` [ y / x ] ph ` when ` x ` and ` y ` are
       distinct.  (Contributed by Mario Carneiro, 11-Aug-2016.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$d x y $.
	fnfs1v_0 $f wff ph $.
	fnfs1v_1 $f set x $.
	fnfs1v_2 $f set y $.
	nfs1v $p |- F/ x [ y / x ] ph $= fnfs1v_0 fnfs1v_1 fnfs1v_2 wsb fnfs1v_1 fnfs1v_0 fnfs1v_1 fnfs1v_2 hbs1 nfi $.
$}
$( Two ways of expressing " ` x ` is (effectively) not free in ` ph ` ."
       (Contributed by NM, 29-May-2009.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$d y ph $.
	fsbhb_0 $f wff ph $.
	fsbhb_1 $f set x $.
	fsbhb_2 $f set y $.
	sbhb $p |- ( ( ph -> A. x ph ) <-> A. y ( ph -> [ y / x ] ph ) ) $= fsbhb_0 fsbhb_0 fsbhb_1 wal wi fsbhb_0 fsbhb_0 fsbhb_1 fsbhb_2 wsb fsbhb_2 wal wi fsbhb_0 fsbhb_0 fsbhb_1 fsbhb_2 wsb wi fsbhb_2 wal fsbhb_0 fsbhb_1 wal fsbhb_0 fsbhb_1 fsbhb_2 wsb fsbhb_2 wal fsbhb_0 fsbhb_0 fsbhb_1 fsbhb_2 fsbhb_0 fsbhb_2 nfv sb8 imbi2i fsbhb_0 fsbhb_0 fsbhb_1 fsbhb_2 wsb fsbhb_2 19.21v bitr4i $.
$}
$( Two ways of expressing " ` x ` is (effectively) not free in ` ph ` ."
       (Contributed by G&eacute;rard Lang, 14-Nov-2013.)  (Revised by Mario
       Carneiro, 6-Oct-2016.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$d x y z $.
	$d y z ph $.
	fsbnf2_0 $f wff ph $.
	fsbnf2_1 $f set x $.
	fsbnf2_2 $f set y $.
	fsbnf2_3 $f set z $.
	sbnf2 $p |- ( F/ x ph <-> A. y A. z ( [ y / x ] ph <-> [ z / x ] ph ) ) $= fsbnf2_0 fsbnf2_1 fsbnf2_2 wsb fsbnf2_0 fsbnf2_1 fsbnf2_3 wsb wb fsbnf2_3 wal fsbnf2_2 wal fsbnf2_0 fsbnf2_1 fsbnf2_2 wsb fsbnf2_0 fsbnf2_1 fsbnf2_3 wsb wi fsbnf2_3 wal fsbnf2_2 wal fsbnf2_0 fsbnf2_1 fsbnf2_3 wsb fsbnf2_0 fsbnf2_1 fsbnf2_2 wsb wi fsbnf2_3 wal fsbnf2_2 wal wa fsbnf2_0 fsbnf2_1 wnf fsbnf2_0 fsbnf2_1 wnf wa fsbnf2_0 fsbnf2_1 wnf fsbnf2_0 fsbnf2_1 fsbnf2_2 wsb fsbnf2_0 fsbnf2_1 fsbnf2_3 wsb fsbnf2_2 fsbnf2_3 2albiim fsbnf2_0 fsbnf2_1 wnf fsbnf2_0 fsbnf2_1 fsbnf2_2 wsb fsbnf2_0 fsbnf2_1 fsbnf2_3 wsb wi fsbnf2_3 wal fsbnf2_2 wal fsbnf2_0 fsbnf2_1 wnf fsbnf2_0 fsbnf2_1 fsbnf2_3 wsb fsbnf2_0 fsbnf2_1 fsbnf2_2 wsb wi fsbnf2_3 wal fsbnf2_2 wal fsbnf2_0 fsbnf2_1 wnf fsbnf2_0 fsbnf2_0 fsbnf2_1 fsbnf2_3 wsb wi fsbnf2_1 wal fsbnf2_3 wal fsbnf2_0 fsbnf2_1 fsbnf2_2 wsb fsbnf2_0 fsbnf2_1 fsbnf2_3 wsb wi fsbnf2_2 wal fsbnf2_3 wal fsbnf2_0 fsbnf2_1 fsbnf2_2 wsb fsbnf2_0 fsbnf2_1 fsbnf2_3 wsb wi fsbnf2_3 wal fsbnf2_2 wal fsbnf2_0 fsbnf2_1 wnf fsbnf2_0 fsbnf2_0 fsbnf2_1 wal wi fsbnf2_1 wal fsbnf2_0 fsbnf2_0 fsbnf2_1 fsbnf2_3 wsb wi fsbnf2_3 wal fsbnf2_1 wal fsbnf2_0 fsbnf2_0 fsbnf2_1 fsbnf2_3 wsb wi fsbnf2_1 wal fsbnf2_3 wal fsbnf2_0 fsbnf2_1 df-nf fsbnf2_0 fsbnf2_0 fsbnf2_1 wal wi fsbnf2_0 fsbnf2_0 fsbnf2_1 fsbnf2_3 wsb wi fsbnf2_3 wal fsbnf2_1 fsbnf2_0 fsbnf2_1 fsbnf2_3 sbhb albii fsbnf2_0 fsbnf2_0 fsbnf2_1 fsbnf2_3 wsb wi fsbnf2_1 fsbnf2_3 alcom 3bitri fsbnf2_0 fsbnf2_0 fsbnf2_1 fsbnf2_3 wsb wi fsbnf2_1 wal fsbnf2_0 fsbnf2_1 fsbnf2_2 wsb fsbnf2_0 fsbnf2_1 fsbnf2_3 wsb wi fsbnf2_2 wal fsbnf2_3 fsbnf2_0 fsbnf2_0 fsbnf2_1 fsbnf2_3 wsb wi fsbnf2_1 wal fsbnf2_0 fsbnf2_0 fsbnf2_1 fsbnf2_3 wsb wi fsbnf2_1 fsbnf2_2 wsb fsbnf2_2 wal fsbnf2_0 fsbnf2_1 fsbnf2_2 wsb fsbnf2_0 fsbnf2_1 fsbnf2_3 wsb wi fsbnf2_2 wal fsbnf2_0 fsbnf2_0 fsbnf2_1 fsbnf2_3 wsb wi fsbnf2_1 fsbnf2_2 fsbnf2_0 fsbnf2_0 fsbnf2_1 fsbnf2_3 wsb wi fsbnf2_2 nfv sb8 fsbnf2_0 fsbnf2_0 fsbnf2_1 fsbnf2_3 wsb wi fsbnf2_1 fsbnf2_2 wsb fsbnf2_0 fsbnf2_1 fsbnf2_2 wsb fsbnf2_0 fsbnf2_1 fsbnf2_3 wsb wi fsbnf2_2 fsbnf2_0 fsbnf2_0 fsbnf2_1 fsbnf2_3 wsb fsbnf2_1 fsbnf2_2 fsbnf2_0 fsbnf2_1 fsbnf2_3 nfs1v sblim albii bitri albii fsbnf2_0 fsbnf2_1 fsbnf2_2 wsb fsbnf2_0 fsbnf2_1 fsbnf2_3 wsb wi fsbnf2_3 fsbnf2_2 alcom 3bitri fsbnf2_0 fsbnf2_1 wnf fsbnf2_0 fsbnf2_0 fsbnf2_1 fsbnf2_2 wsb wi fsbnf2_1 wal fsbnf2_2 wal fsbnf2_0 fsbnf2_1 fsbnf2_3 wsb fsbnf2_0 fsbnf2_1 fsbnf2_2 wsb wi fsbnf2_3 wal fsbnf2_2 wal fsbnf2_0 fsbnf2_1 wnf fsbnf2_0 fsbnf2_0 fsbnf2_1 wal wi fsbnf2_1 wal fsbnf2_0 fsbnf2_0 fsbnf2_1 fsbnf2_2 wsb wi fsbnf2_2 wal fsbnf2_1 wal fsbnf2_0 fsbnf2_0 fsbnf2_1 fsbnf2_2 wsb wi fsbnf2_1 wal fsbnf2_2 wal fsbnf2_0 fsbnf2_1 df-nf fsbnf2_0 fsbnf2_0 fsbnf2_1 wal wi fsbnf2_0 fsbnf2_0 fsbnf2_1 fsbnf2_2 wsb wi fsbnf2_2 wal fsbnf2_1 fsbnf2_0 fsbnf2_1 fsbnf2_2 sbhb albii fsbnf2_0 fsbnf2_0 fsbnf2_1 fsbnf2_2 wsb wi fsbnf2_1 fsbnf2_2 alcom 3bitri fsbnf2_0 fsbnf2_0 fsbnf2_1 fsbnf2_2 wsb wi fsbnf2_1 wal fsbnf2_0 fsbnf2_1 fsbnf2_3 wsb fsbnf2_0 fsbnf2_1 fsbnf2_2 wsb wi fsbnf2_3 wal fsbnf2_2 fsbnf2_0 fsbnf2_0 fsbnf2_1 fsbnf2_2 wsb wi fsbnf2_1 wal fsbnf2_0 fsbnf2_0 fsbnf2_1 fsbnf2_2 wsb wi fsbnf2_1 fsbnf2_3 wsb fsbnf2_3 wal fsbnf2_0 fsbnf2_1 fsbnf2_3 wsb fsbnf2_0 fsbnf2_1 fsbnf2_2 wsb wi fsbnf2_3 wal fsbnf2_0 fsbnf2_0 fsbnf2_1 fsbnf2_2 wsb wi fsbnf2_1 fsbnf2_3 fsbnf2_0 fsbnf2_0 fsbnf2_1 fsbnf2_2 wsb wi fsbnf2_3 nfv sb8 fsbnf2_0 fsbnf2_0 fsbnf2_1 fsbnf2_2 wsb wi fsbnf2_1 fsbnf2_3 wsb fsbnf2_0 fsbnf2_1 fsbnf2_3 wsb fsbnf2_0 fsbnf2_1 fsbnf2_2 wsb wi fsbnf2_3 fsbnf2_0 fsbnf2_0 fsbnf2_1 fsbnf2_2 wsb fsbnf2_1 fsbnf2_3 fsbnf2_0 fsbnf2_1 fsbnf2_2 nfs1v sblim albii bitri albii bitri anbi12i fsbnf2_0 fsbnf2_1 wnf anidm 3bitr2ri $.
$}
$( If ` z ` is not free in ` ph ` , it is not free in ` [ y / x ] ph ` when
       ` y ` and ` z ` are distinct.  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$d y z $.
	fnfsb_0 $f wff ph $.
	fnfsb_1 $f set x $.
	fnfsb_2 $f set y $.
	fnfsb_3 $f set z $.
	enfsb_0 $e |- F/ z ph $.
	nfsb $p |- F/ z [ y / x ] ph $= fnfsb_3 sup_set_class fnfsb_2 sup_set_class wceq fnfsb_3 wal fnfsb_0 fnfsb_1 fnfsb_2 wsb fnfsb_3 wnf fnfsb_0 fnfsb_1 fnfsb_2 wsb fnfsb_3 fnfsb_2 fnfsb_3 a16nf fnfsb_0 fnfsb_1 fnfsb_2 fnfsb_3 enfsb_0 nfsb4 pm2.61i $.
$}
$( If ` z ` is not free in ` ph ` , it is not free in ` [ y / x ] ph ` when
       ` y ` and ` z ` are distinct.  (Contributed by NM, 12-Aug-1993.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$d y z $.
	fhbsb_0 $f wff ph $.
	fhbsb_1 $f set x $.
	fhbsb_2 $f set y $.
	fhbsb_3 $f set z $.
	ehbsb_0 $e |- ( ph -> A. z ph ) $.
	hbsb $p |- ( [ y / x ] ph -> A. z [ y / x ] ph ) $= fhbsb_0 fhbsb_1 fhbsb_2 wsb fhbsb_3 fhbsb_0 fhbsb_1 fhbsb_2 fhbsb_3 fhbsb_0 fhbsb_3 ehbsb_0 nfi nfsb nfri $.
$}
$( Deduction version of ~ nfsb .  (Contributed by NM, 15-Feb-2013.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v z $.
	$d y z $.
	fnfsbd_0 $f wff ph $.
	fnfsbd_1 $f wff ps $.
	fnfsbd_2 $f set x $.
	fnfsbd_3 $f set y $.
	fnfsbd_4 $f set z $.
	enfsbd_0 $e |- F/ x ph $.
	enfsbd_1 $e |- ( ph -> F/ z ps ) $.
	nfsbd $p |- ( ph -> F/ z [ y / x ] ps ) $= fnfsbd_0 fnfsbd_4 sup_set_class fnfsbd_3 sup_set_class wceq fnfsbd_4 wal fnfsbd_1 fnfsbd_2 fnfsbd_3 wsb fnfsbd_4 wnf fnfsbd_0 fnfsbd_1 fnfsbd_4 wnf fnfsbd_2 wal fnfsbd_4 sup_set_class fnfsbd_3 sup_set_class wceq fnfsbd_4 wal wn fnfsbd_1 fnfsbd_2 fnfsbd_3 wsb fnfsbd_4 wnf wi fnfsbd_0 fnfsbd_1 fnfsbd_4 wnf fnfsbd_2 enfsbd_0 enfsbd_1 alrimi fnfsbd_1 fnfsbd_2 fnfsbd_3 fnfsbd_4 nfsb4t syl fnfsbd_1 fnfsbd_2 fnfsbd_3 wsb fnfsbd_4 fnfsbd_3 fnfsbd_4 a16nf pm2.61d2 $.
$}
$( Equivalence for double substitution.  (Contributed by NM,
       3-Feb-2005.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d x y z $.
	$d w y $.
	f2sb5_0 $f wff ph $.
	f2sb5_1 $f set x $.
	f2sb5_2 $f set y $.
	f2sb5_3 $f set z $.
	f2sb5_4 $f set w $.
	2sb5 $p |- ( [ z / x ] [ w / y ] ph <-> E. x E. y ( ( x = z /\ y = w ) /\ ph ) ) $= f2sb5_0 f2sb5_2 f2sb5_4 wsb f2sb5_1 f2sb5_3 wsb f2sb5_1 sup_set_class f2sb5_3 sup_set_class wceq f2sb5_0 f2sb5_2 f2sb5_4 wsb wa f2sb5_1 wex f2sb5_1 sup_set_class f2sb5_3 sup_set_class wceq f2sb5_2 sup_set_class f2sb5_4 sup_set_class wceq wa f2sb5_0 wa f2sb5_2 wex f2sb5_1 wex f2sb5_0 f2sb5_2 f2sb5_4 wsb f2sb5_1 f2sb5_3 sb5 f2sb5_1 sup_set_class f2sb5_3 sup_set_class wceq f2sb5_0 f2sb5_2 f2sb5_4 wsb wa f2sb5_1 sup_set_class f2sb5_3 sup_set_class wceq f2sb5_2 sup_set_class f2sb5_4 sup_set_class wceq wa f2sb5_0 wa f2sb5_2 wex f2sb5_1 f2sb5_1 sup_set_class f2sb5_3 sup_set_class wceq f2sb5_2 sup_set_class f2sb5_4 sup_set_class wceq f2sb5_0 wa wa f2sb5_2 wex f2sb5_1 sup_set_class f2sb5_3 sup_set_class wceq f2sb5_2 sup_set_class f2sb5_4 sup_set_class wceq f2sb5_0 wa f2sb5_2 wex wa f2sb5_1 sup_set_class f2sb5_3 sup_set_class wceq f2sb5_2 sup_set_class f2sb5_4 sup_set_class wceq wa f2sb5_0 wa f2sb5_2 wex f2sb5_1 sup_set_class f2sb5_3 sup_set_class wceq f2sb5_0 f2sb5_2 f2sb5_4 wsb wa f2sb5_1 sup_set_class f2sb5_3 sup_set_class wceq f2sb5_2 sup_set_class f2sb5_4 sup_set_class wceq f2sb5_0 wa f2sb5_2 19.42v f2sb5_1 sup_set_class f2sb5_3 sup_set_class wceq f2sb5_2 sup_set_class f2sb5_4 sup_set_class wceq wa f2sb5_0 wa f2sb5_1 sup_set_class f2sb5_3 sup_set_class wceq f2sb5_2 sup_set_class f2sb5_4 sup_set_class wceq f2sb5_0 wa wa f2sb5_2 f2sb5_1 sup_set_class f2sb5_3 sup_set_class wceq f2sb5_2 sup_set_class f2sb5_4 sup_set_class wceq f2sb5_0 anass exbii f2sb5_0 f2sb5_2 f2sb5_4 wsb f2sb5_2 sup_set_class f2sb5_4 sup_set_class wceq f2sb5_0 wa f2sb5_2 wex f2sb5_1 sup_set_class f2sb5_3 sup_set_class wceq f2sb5_0 f2sb5_2 f2sb5_4 sb5 anbi2i 3bitr4ri exbii bitri $.
$}
$( Equivalence for double substitution.  (Contributed by NM,
       3-Feb-2005.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d x y z $.
	$d w y $.
	f2sb6_0 $f wff ph $.
	f2sb6_1 $f set x $.
	f2sb6_2 $f set y $.
	f2sb6_3 $f set z $.
	f2sb6_4 $f set w $.
	2sb6 $p |- ( [ z / x ] [ w / y ] ph <-> A. x A. y ( ( x = z /\ y = w ) -> ph ) ) $= f2sb6_0 f2sb6_2 f2sb6_4 wsb f2sb6_1 f2sb6_3 wsb f2sb6_1 sup_set_class f2sb6_3 sup_set_class wceq f2sb6_0 f2sb6_2 f2sb6_4 wsb wi f2sb6_1 wal f2sb6_1 sup_set_class f2sb6_3 sup_set_class wceq f2sb6_2 sup_set_class f2sb6_4 sup_set_class wceq wa f2sb6_0 wi f2sb6_2 wal f2sb6_1 wal f2sb6_0 f2sb6_2 f2sb6_4 wsb f2sb6_1 f2sb6_3 sb6 f2sb6_1 sup_set_class f2sb6_3 sup_set_class wceq f2sb6_0 f2sb6_2 f2sb6_4 wsb wi f2sb6_1 sup_set_class f2sb6_3 sup_set_class wceq f2sb6_2 sup_set_class f2sb6_4 sup_set_class wceq wa f2sb6_0 wi f2sb6_2 wal f2sb6_1 f2sb6_1 sup_set_class f2sb6_3 sup_set_class wceq f2sb6_2 sup_set_class f2sb6_4 sup_set_class wceq f2sb6_0 wi wi f2sb6_2 wal f2sb6_1 sup_set_class f2sb6_3 sup_set_class wceq f2sb6_2 sup_set_class f2sb6_4 sup_set_class wceq f2sb6_0 wi f2sb6_2 wal wi f2sb6_1 sup_set_class f2sb6_3 sup_set_class wceq f2sb6_2 sup_set_class f2sb6_4 sup_set_class wceq wa f2sb6_0 wi f2sb6_2 wal f2sb6_1 sup_set_class f2sb6_3 sup_set_class wceq f2sb6_0 f2sb6_2 f2sb6_4 wsb wi f2sb6_1 sup_set_class f2sb6_3 sup_set_class wceq f2sb6_2 sup_set_class f2sb6_4 sup_set_class wceq f2sb6_0 wi f2sb6_2 19.21v f2sb6_1 sup_set_class f2sb6_3 sup_set_class wceq f2sb6_2 sup_set_class f2sb6_4 sup_set_class wceq wa f2sb6_0 wi f2sb6_1 sup_set_class f2sb6_3 sup_set_class wceq f2sb6_2 sup_set_class f2sb6_4 sup_set_class wceq f2sb6_0 wi wi f2sb6_2 f2sb6_1 sup_set_class f2sb6_3 sup_set_class wceq f2sb6_2 sup_set_class f2sb6_4 sup_set_class wceq f2sb6_0 impexp albii f2sb6_0 f2sb6_2 f2sb6_4 wsb f2sb6_2 sup_set_class f2sb6_4 sup_set_class wceq f2sb6_0 wi f2sb6_2 wal f2sb6_1 sup_set_class f2sb6_3 sup_set_class wceq f2sb6_0 f2sb6_2 f2sb6_4 sb6 imbi2i 3bitr4ri albii bitri $.
$}
$( Commutativity law for substitution.  Used in proof of Theorem 9.7 of
       [Megill] p. 449 (p. 16 of the preprint).  (Contributed by NM,
       27-May-1997.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d x z $.
	$d x w $.
	$d y z $.
	fsbcom2_0 $f wff ph $.
	fsbcom2_1 $f set x $.
	fsbcom2_2 $f set y $.
	fsbcom2_3 $f set z $.
	fsbcom2_4 $f set w $.
	sbcom2 $p |- ( [ w / z ] [ y / x ] ph <-> [ y / x ] [ w / z ] ph ) $= fsbcom2_1 sup_set_class fsbcom2_2 sup_set_class wceq fsbcom2_1 wal fsbcom2_3 sup_set_class fsbcom2_4 sup_set_class wceq fsbcom2_3 wal fsbcom2_0 fsbcom2_1 fsbcom2_2 wsb fsbcom2_3 fsbcom2_4 wsb fsbcom2_0 fsbcom2_3 fsbcom2_4 wsb fsbcom2_1 fsbcom2_2 wsb wb fsbcom2_1 sup_set_class fsbcom2_2 sup_set_class wceq fsbcom2_1 wal wn fsbcom2_3 sup_set_class fsbcom2_4 sup_set_class wceq fsbcom2_3 wal wn fsbcom2_0 fsbcom2_1 fsbcom2_2 wsb fsbcom2_3 fsbcom2_4 wsb fsbcom2_0 fsbcom2_3 fsbcom2_4 wsb fsbcom2_1 fsbcom2_2 wsb wb fsbcom2_1 sup_set_class fsbcom2_2 sup_set_class wceq fsbcom2_1 wal wn fsbcom2_3 sup_set_class fsbcom2_4 sup_set_class wceq fsbcom2_3 wal wn wa fsbcom2_3 sup_set_class fsbcom2_4 sup_set_class wceq fsbcom2_1 sup_set_class fsbcom2_2 sup_set_class wceq fsbcom2_0 wi fsbcom2_1 wal wi fsbcom2_3 wal fsbcom2_1 sup_set_class fsbcom2_2 sup_set_class wceq fsbcom2_3 sup_set_class fsbcom2_4 sup_set_class wceq fsbcom2_0 wi fsbcom2_3 wal wi fsbcom2_1 wal fsbcom2_0 fsbcom2_1 fsbcom2_2 wsb fsbcom2_3 fsbcom2_4 wsb fsbcom2_0 fsbcom2_3 fsbcom2_4 wsb fsbcom2_1 fsbcom2_2 wsb fsbcom2_3 sup_set_class fsbcom2_4 sup_set_class wceq fsbcom2_1 sup_set_class fsbcom2_2 sup_set_class wceq fsbcom2_0 wi fsbcom2_1 wal wi fsbcom2_3 wal fsbcom2_1 sup_set_class fsbcom2_2 sup_set_class wceq fsbcom2_3 sup_set_class fsbcom2_4 sup_set_class wceq fsbcom2_0 wi fsbcom2_3 wal wi fsbcom2_1 wal wb fsbcom2_1 sup_set_class fsbcom2_2 sup_set_class wceq fsbcom2_1 wal wn fsbcom2_3 sup_set_class fsbcom2_4 sup_set_class wceq fsbcom2_3 wal wn wa fsbcom2_1 sup_set_class fsbcom2_2 sup_set_class wceq fsbcom2_3 sup_set_class fsbcom2_4 sup_set_class wceq fsbcom2_0 wi wi fsbcom2_1 wal fsbcom2_3 wal fsbcom2_1 sup_set_class fsbcom2_2 sup_set_class wceq fsbcom2_3 sup_set_class fsbcom2_4 sup_set_class wceq fsbcom2_0 wi wi fsbcom2_3 wal fsbcom2_1 wal fsbcom2_3 sup_set_class fsbcom2_4 sup_set_class wceq fsbcom2_1 sup_set_class fsbcom2_2 sup_set_class wceq fsbcom2_0 wi fsbcom2_1 wal wi fsbcom2_3 wal fsbcom2_1 sup_set_class fsbcom2_2 sup_set_class wceq fsbcom2_3 sup_set_class fsbcom2_4 sup_set_class wceq fsbcom2_0 wi fsbcom2_3 wal wi fsbcom2_1 wal fsbcom2_1 sup_set_class fsbcom2_2 sup_set_class wceq fsbcom2_3 sup_set_class fsbcom2_4 sup_set_class wceq fsbcom2_0 wi wi fsbcom2_3 fsbcom2_1 alcom fsbcom2_1 sup_set_class fsbcom2_2 sup_set_class wceq fsbcom2_3 sup_set_class fsbcom2_4 sup_set_class wceq fsbcom2_0 wi wi fsbcom2_1 wal fsbcom2_3 sup_set_class fsbcom2_4 sup_set_class wceq fsbcom2_1 sup_set_class fsbcom2_2 sup_set_class wceq fsbcom2_0 wi fsbcom2_1 wal wi fsbcom2_3 fsbcom2_1 sup_set_class fsbcom2_2 sup_set_class wceq fsbcom2_3 sup_set_class fsbcom2_4 sup_set_class wceq fsbcom2_0 wi wi fsbcom2_1 wal fsbcom2_3 sup_set_class fsbcom2_4 sup_set_class wceq fsbcom2_1 sup_set_class fsbcom2_2 sup_set_class wceq fsbcom2_0 wi wi fsbcom2_1 wal fsbcom2_3 sup_set_class fsbcom2_4 sup_set_class wceq fsbcom2_1 sup_set_class fsbcom2_2 sup_set_class wceq fsbcom2_0 wi fsbcom2_1 wal wi fsbcom2_1 sup_set_class fsbcom2_2 sup_set_class wceq fsbcom2_3 sup_set_class fsbcom2_4 sup_set_class wceq fsbcom2_0 wi wi fsbcom2_3 sup_set_class fsbcom2_4 sup_set_class wceq fsbcom2_1 sup_set_class fsbcom2_2 sup_set_class wceq fsbcom2_0 wi wi fsbcom2_1 fsbcom2_1 sup_set_class fsbcom2_2 sup_set_class wceq fsbcom2_3 sup_set_class fsbcom2_4 sup_set_class wceq fsbcom2_0 bi2.04 albii fsbcom2_3 sup_set_class fsbcom2_4 sup_set_class wceq fsbcom2_1 sup_set_class fsbcom2_2 sup_set_class wceq fsbcom2_0 wi fsbcom2_1 19.21v bitri albii fsbcom2_1 sup_set_class fsbcom2_2 sup_set_class wceq fsbcom2_3 sup_set_class fsbcom2_4 sup_set_class wceq fsbcom2_0 wi wi fsbcom2_3 wal fsbcom2_1 sup_set_class fsbcom2_2 sup_set_class wceq fsbcom2_3 sup_set_class fsbcom2_4 sup_set_class wceq fsbcom2_0 wi fsbcom2_3 wal wi fsbcom2_1 fsbcom2_1 sup_set_class fsbcom2_2 sup_set_class wceq fsbcom2_3 sup_set_class fsbcom2_4 sup_set_class wceq fsbcom2_0 wi fsbcom2_3 19.21v albii 3bitr3i a1i fsbcom2_3 sup_set_class fsbcom2_4 sup_set_class wceq fsbcom2_3 wal wn fsbcom2_0 fsbcom2_1 fsbcom2_2 wsb fsbcom2_3 fsbcom2_4 wsb fsbcom2_3 sup_set_class fsbcom2_4 sup_set_class wceq fsbcom2_0 fsbcom2_1 fsbcom2_2 wsb wi fsbcom2_3 wal fsbcom2_1 sup_set_class fsbcom2_2 sup_set_class wceq fsbcom2_1 wal wn fsbcom2_3 sup_set_class fsbcom2_4 sup_set_class wceq fsbcom2_1 sup_set_class fsbcom2_2 sup_set_class wceq fsbcom2_0 wi fsbcom2_1 wal wi fsbcom2_3 wal fsbcom2_0 fsbcom2_1 fsbcom2_2 wsb fsbcom2_3 fsbcom2_4 sb4b fsbcom2_1 sup_set_class fsbcom2_2 sup_set_class wceq fsbcom2_1 wal wn fsbcom2_3 sup_set_class fsbcom2_4 sup_set_class wceq fsbcom2_0 fsbcom2_1 fsbcom2_2 wsb wi fsbcom2_3 sup_set_class fsbcom2_4 sup_set_class wceq fsbcom2_1 sup_set_class fsbcom2_2 sup_set_class wceq fsbcom2_0 wi fsbcom2_1 wal wi fsbcom2_3 fsbcom2_1 sup_set_class fsbcom2_2 sup_set_class wceq fsbcom2_1 wal wn fsbcom2_0 fsbcom2_1 fsbcom2_2 wsb fsbcom2_1 sup_set_class fsbcom2_2 sup_set_class wceq fsbcom2_0 wi fsbcom2_1 wal fsbcom2_3 sup_set_class fsbcom2_4 sup_set_class wceq fsbcom2_0 fsbcom2_1 fsbcom2_2 sb4b imbi2d albidv sylan9bbr fsbcom2_1 sup_set_class fsbcom2_2 sup_set_class wceq fsbcom2_1 wal wn fsbcom2_0 fsbcom2_3 fsbcom2_4 wsb fsbcom2_1 fsbcom2_2 wsb fsbcom2_1 sup_set_class fsbcom2_2 sup_set_class wceq fsbcom2_0 fsbcom2_3 fsbcom2_4 wsb wi fsbcom2_1 wal fsbcom2_3 sup_set_class fsbcom2_4 sup_set_class wceq fsbcom2_3 wal wn fsbcom2_1 sup_set_class fsbcom2_2 sup_set_class wceq fsbcom2_3 sup_set_class fsbcom2_4 sup_set_class wceq fsbcom2_0 wi fsbcom2_3 wal wi fsbcom2_1 wal fsbcom2_0 fsbcom2_3 fsbcom2_4 wsb fsbcom2_1 fsbcom2_2 sb4b fsbcom2_3 sup_set_class fsbcom2_4 sup_set_class wceq fsbcom2_3 wal wn fsbcom2_1 sup_set_class fsbcom2_2 sup_set_class wceq fsbcom2_0 fsbcom2_3 fsbcom2_4 wsb wi fsbcom2_1 sup_set_class fsbcom2_2 sup_set_class wceq fsbcom2_3 sup_set_class fsbcom2_4 sup_set_class wceq fsbcom2_0 wi fsbcom2_3 wal wi fsbcom2_1 fsbcom2_3 sup_set_class fsbcom2_4 sup_set_class wceq fsbcom2_3 wal wn fsbcom2_0 fsbcom2_3 fsbcom2_4 wsb fsbcom2_3 sup_set_class fsbcom2_4 sup_set_class wceq fsbcom2_0 wi fsbcom2_3 wal fsbcom2_1 sup_set_class fsbcom2_2 sup_set_class wceq fsbcom2_0 fsbcom2_3 fsbcom2_4 sb4b imbi2d albidv sylan9bb 3bitr4d ex fsbcom2_1 sup_set_class fsbcom2_2 sup_set_class wceq fsbcom2_1 wal fsbcom2_0 fsbcom2_3 fsbcom2_4 wsb fsbcom2_0 fsbcom2_1 fsbcom2_2 wsb fsbcom2_3 fsbcom2_4 wsb fsbcom2_0 fsbcom2_3 fsbcom2_4 wsb fsbcom2_1 fsbcom2_2 wsb fsbcom2_1 sup_set_class fsbcom2_2 sup_set_class wceq fsbcom2_1 wal fsbcom2_0 fsbcom2_0 fsbcom2_1 fsbcom2_2 wsb fsbcom2_3 fsbcom2_4 fsbcom2_1 fsbcom2_2 fsbcom2_3 nfae fsbcom2_1 sup_set_class fsbcom2_2 sup_set_class wceq fsbcom2_0 fsbcom2_0 fsbcom2_1 fsbcom2_2 wsb wb fsbcom2_1 fsbcom2_0 fsbcom2_1 fsbcom2_2 sbequ12 sps sbbid fsbcom2_1 sup_set_class fsbcom2_2 sup_set_class wceq fsbcom2_0 fsbcom2_3 fsbcom2_4 wsb fsbcom2_0 fsbcom2_3 fsbcom2_4 wsb fsbcom2_1 fsbcom2_2 wsb wb fsbcom2_1 fsbcom2_0 fsbcom2_3 fsbcom2_4 wsb fsbcom2_1 fsbcom2_2 sbequ12 sps bitr3d fsbcom2_3 sup_set_class fsbcom2_4 sup_set_class wceq fsbcom2_3 wal fsbcom2_0 fsbcom2_1 fsbcom2_2 wsb fsbcom2_0 fsbcom2_1 fsbcom2_2 wsb fsbcom2_3 fsbcom2_4 wsb fsbcom2_0 fsbcom2_3 fsbcom2_4 wsb fsbcom2_1 fsbcom2_2 wsb fsbcom2_3 sup_set_class fsbcom2_4 sup_set_class wceq fsbcom2_0 fsbcom2_1 fsbcom2_2 wsb fsbcom2_0 fsbcom2_1 fsbcom2_2 wsb fsbcom2_3 fsbcom2_4 wsb wb fsbcom2_3 fsbcom2_0 fsbcom2_1 fsbcom2_2 wsb fsbcom2_3 fsbcom2_4 sbequ12 sps fsbcom2_3 sup_set_class fsbcom2_4 sup_set_class wceq fsbcom2_3 wal fsbcom2_0 fsbcom2_0 fsbcom2_3 fsbcom2_4 wsb fsbcom2_1 fsbcom2_2 fsbcom2_3 fsbcom2_4 fsbcom2_1 nfae fsbcom2_3 sup_set_class fsbcom2_4 sup_set_class wceq fsbcom2_0 fsbcom2_0 fsbcom2_3 fsbcom2_4 wsb wb fsbcom2_3 fsbcom2_0 fsbcom2_3 fsbcom2_4 sbequ12 sps sbbid bitr3d pm2.61ii $.
$}
$( Theorem *11.07 in [WhiteheadRussell] p. 159.  (Contributed by Andrew
       Salmon, 17-Jun-2011.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d ph x y z $.
	$d w x z $.
	fpm11.07_0 $f wff ph $.
	fpm11.07_1 $f set x $.
	fpm11.07_2 $f set y $.
	fpm11.07_3 $f set z $.
	fpm11.07_4 $f set w $.
	pm11.07 $p |- ( [ w / x ] [ y / z ] ph <-> [ y / x ] [ w / z ] ph ) $= fpm11.07_1 sup_set_class fpm11.07_4 sup_set_class wceq fpm11.07_3 sup_set_class fpm11.07_2 sup_set_class wceq wa fpm11.07_0 wa fpm11.07_3 wex fpm11.07_1 wex fpm11.07_1 sup_set_class fpm11.07_2 sup_set_class wceq fpm11.07_3 sup_set_class fpm11.07_4 sup_set_class wceq wa fpm11.07_0 wa fpm11.07_3 wex fpm11.07_1 wex fpm11.07_0 fpm11.07_3 fpm11.07_2 wsb fpm11.07_1 fpm11.07_4 wsb fpm11.07_0 fpm11.07_3 fpm11.07_4 wsb fpm11.07_1 fpm11.07_2 wsb fpm11.07_1 sup_set_class fpm11.07_4 sup_set_class wceq fpm11.07_3 sup_set_class fpm11.07_2 sup_set_class wceq wa fpm11.07_3 wex fpm11.07_1 wex fpm11.07_0 wa fpm11.07_1 sup_set_class fpm11.07_2 sup_set_class wceq fpm11.07_3 sup_set_class fpm11.07_4 sup_set_class wceq wa fpm11.07_3 wex fpm11.07_1 wex fpm11.07_0 wa fpm11.07_1 sup_set_class fpm11.07_4 sup_set_class wceq fpm11.07_3 sup_set_class fpm11.07_2 sup_set_class wceq wa fpm11.07_0 wa fpm11.07_3 wex fpm11.07_1 wex fpm11.07_1 sup_set_class fpm11.07_2 sup_set_class wceq fpm11.07_3 sup_set_class fpm11.07_4 sup_set_class wceq wa fpm11.07_0 wa fpm11.07_3 wex fpm11.07_1 wex fpm11.07_1 sup_set_class fpm11.07_4 sup_set_class wceq fpm11.07_3 sup_set_class fpm11.07_2 sup_set_class wceq wa fpm11.07_3 wex fpm11.07_1 wex fpm11.07_1 sup_set_class fpm11.07_2 sup_set_class wceq fpm11.07_3 sup_set_class fpm11.07_4 sup_set_class wceq wa fpm11.07_3 wex fpm11.07_1 wex fpm11.07_0 fpm11.07_1 sup_set_class fpm11.07_4 sup_set_class wceq fpm11.07_1 wex fpm11.07_3 sup_set_class fpm11.07_2 sup_set_class wceq fpm11.07_3 wex wa fpm11.07_1 sup_set_class fpm11.07_2 sup_set_class wceq fpm11.07_1 wex fpm11.07_3 sup_set_class fpm11.07_4 sup_set_class wceq fpm11.07_3 wex wa fpm11.07_1 sup_set_class fpm11.07_4 sup_set_class wceq fpm11.07_3 sup_set_class fpm11.07_2 sup_set_class wceq wa fpm11.07_3 wex fpm11.07_1 wex fpm11.07_1 sup_set_class fpm11.07_2 sup_set_class wceq fpm11.07_3 sup_set_class fpm11.07_4 sup_set_class wceq wa fpm11.07_3 wex fpm11.07_1 wex fpm11.07_1 sup_set_class fpm11.07_4 sup_set_class wceq fpm11.07_1 wex fpm11.07_3 sup_set_class fpm11.07_2 sup_set_class wceq fpm11.07_3 wex wa fpm11.07_1 sup_set_class fpm11.07_2 sup_set_class wceq fpm11.07_1 wex fpm11.07_3 sup_set_class fpm11.07_4 sup_set_class wceq fpm11.07_3 wex wa fpm11.07_1 sup_set_class fpm11.07_4 sup_set_class wceq fpm11.07_1 wex fpm11.07_3 sup_set_class fpm11.07_2 sup_set_class wceq fpm11.07_3 wex fpm11.07_1 fpm11.07_4 a9ev fpm11.07_3 fpm11.07_2 a9ev pm3.2i fpm11.07_1 sup_set_class fpm11.07_2 sup_set_class wceq fpm11.07_1 wex fpm11.07_3 sup_set_class fpm11.07_4 sup_set_class wceq fpm11.07_3 wex fpm11.07_1 fpm11.07_2 a9ev fpm11.07_3 fpm11.07_4 a9ev pm3.2i 2th fpm11.07_1 sup_set_class fpm11.07_4 sup_set_class wceq fpm11.07_3 sup_set_class fpm11.07_2 sup_set_class wceq fpm11.07_1 fpm11.07_3 eeanv fpm11.07_1 sup_set_class fpm11.07_2 sup_set_class wceq fpm11.07_3 sup_set_class fpm11.07_4 sup_set_class wceq fpm11.07_1 fpm11.07_3 eeanv 3bitr4i anbi1i fpm11.07_1 sup_set_class fpm11.07_4 sup_set_class wceq fpm11.07_3 sup_set_class fpm11.07_2 sup_set_class wceq wa fpm11.07_0 fpm11.07_1 fpm11.07_3 19.41vv fpm11.07_1 sup_set_class fpm11.07_2 sup_set_class wceq fpm11.07_3 sup_set_class fpm11.07_4 sup_set_class wceq wa fpm11.07_0 fpm11.07_1 fpm11.07_3 19.41vv 3bitr4i fpm11.07_0 fpm11.07_1 fpm11.07_3 fpm11.07_4 fpm11.07_2 2sb5 fpm11.07_0 fpm11.07_1 fpm11.07_3 fpm11.07_2 fpm11.07_4 2sb5 3bitr4i $.
$}
$( Equivalence for substitution.  (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$d x y $.
	fsb6a_0 $f wff ph $.
	fsb6a_1 $f set x $.
	fsb6a_2 $f set y $.
	sb6a $p |- ( [ y / x ] ph <-> A. x ( x = y -> [ x / y ] ph ) ) $= fsb6a_0 fsb6a_1 fsb6a_2 wsb fsb6a_1 sup_set_class fsb6a_2 sup_set_class wceq fsb6a_0 wi fsb6a_1 wal fsb6a_1 sup_set_class fsb6a_2 sup_set_class wceq fsb6a_0 fsb6a_2 fsb6a_1 wsb wi fsb6a_1 wal fsb6a_0 fsb6a_1 fsb6a_2 sb6 fsb6a_1 sup_set_class fsb6a_2 sup_set_class wceq fsb6a_0 wi fsb6a_1 sup_set_class fsb6a_2 sup_set_class wceq fsb6a_0 fsb6a_2 fsb6a_1 wsb wi fsb6a_1 fsb6a_1 sup_set_class fsb6a_2 sup_set_class wceq fsb6a_0 fsb6a_0 fsb6a_2 fsb6a_1 wsb fsb6a_0 fsb6a_0 fsb6a_2 fsb6a_1 wsb wb fsb6a_2 fsb6a_1 fsb6a_0 fsb6a_2 fsb6a_1 sbequ12 equcoms pm5.74i albii bitri $.
$}
$( Reversed double substitution.  (Contributed by NM, 3-Feb-2005.)
       (Revised by Mario Carneiro, 6-Oct-2016.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d x y $.
	$d x w $.
	$d y z $.
	$d z w $.
	f2sb5rf_0 $f wff ph $.
	f2sb5rf_1 $f set x $.
	f2sb5rf_2 $f set y $.
	f2sb5rf_3 $f set z $.
	f2sb5rf_4 $f set w $.
	e2sb5rf_0 $e |- F/ z ph $.
	e2sb5rf_1 $e |- F/ w ph $.
	2sb5rf $p |- ( ph <-> E. z E. w ( ( z = x /\ w = y ) /\ [ z / x ] [ w / y ] ph ) ) $= f2sb5rf_0 f2sb5rf_3 sup_set_class f2sb5rf_1 sup_set_class wceq f2sb5rf_0 f2sb5rf_1 f2sb5rf_3 wsb wa f2sb5rf_3 wex f2sb5rf_3 sup_set_class f2sb5rf_1 sup_set_class wceq f2sb5rf_4 sup_set_class f2sb5rf_2 sup_set_class wceq wa f2sb5rf_0 f2sb5rf_2 f2sb5rf_4 wsb f2sb5rf_1 f2sb5rf_3 wsb wa f2sb5rf_4 wex f2sb5rf_3 wex f2sb5rf_0 f2sb5rf_1 f2sb5rf_3 e2sb5rf_0 sb5rf f2sb5rf_3 sup_set_class f2sb5rf_1 sup_set_class wceq f2sb5rf_0 f2sb5rf_1 f2sb5rf_3 wsb wa f2sb5rf_3 sup_set_class f2sb5rf_1 sup_set_class wceq f2sb5rf_4 sup_set_class f2sb5rf_2 sup_set_class wceq wa f2sb5rf_0 f2sb5rf_2 f2sb5rf_4 wsb f2sb5rf_1 f2sb5rf_3 wsb wa f2sb5rf_4 wex f2sb5rf_3 f2sb5rf_3 sup_set_class f2sb5rf_1 sup_set_class wceq f2sb5rf_4 sup_set_class f2sb5rf_2 sup_set_class wceq f2sb5rf_0 f2sb5rf_1 f2sb5rf_3 wsb f2sb5rf_2 f2sb5rf_4 wsb wa wa f2sb5rf_4 wex f2sb5rf_3 sup_set_class f2sb5rf_1 sup_set_class wceq f2sb5rf_4 sup_set_class f2sb5rf_2 sup_set_class wceq f2sb5rf_0 f2sb5rf_1 f2sb5rf_3 wsb f2sb5rf_2 f2sb5rf_4 wsb wa f2sb5rf_4 wex wa f2sb5rf_3 sup_set_class f2sb5rf_1 sup_set_class wceq f2sb5rf_4 sup_set_class f2sb5rf_2 sup_set_class wceq wa f2sb5rf_0 f2sb5rf_2 f2sb5rf_4 wsb f2sb5rf_1 f2sb5rf_3 wsb wa f2sb5rf_4 wex f2sb5rf_3 sup_set_class f2sb5rf_1 sup_set_class wceq f2sb5rf_0 f2sb5rf_1 f2sb5rf_3 wsb wa f2sb5rf_3 sup_set_class f2sb5rf_1 sup_set_class wceq f2sb5rf_4 sup_set_class f2sb5rf_2 sup_set_class wceq f2sb5rf_0 f2sb5rf_1 f2sb5rf_3 wsb f2sb5rf_2 f2sb5rf_4 wsb wa f2sb5rf_4 19.42v f2sb5rf_3 sup_set_class f2sb5rf_1 sup_set_class wceq f2sb5rf_4 sup_set_class f2sb5rf_2 sup_set_class wceq wa f2sb5rf_0 f2sb5rf_2 f2sb5rf_4 wsb f2sb5rf_1 f2sb5rf_3 wsb wa f2sb5rf_3 sup_set_class f2sb5rf_1 sup_set_class wceq f2sb5rf_4 sup_set_class f2sb5rf_2 sup_set_class wceq f2sb5rf_0 f2sb5rf_1 f2sb5rf_3 wsb f2sb5rf_2 f2sb5rf_4 wsb wa wa f2sb5rf_4 f2sb5rf_3 sup_set_class f2sb5rf_1 sup_set_class wceq f2sb5rf_4 sup_set_class f2sb5rf_2 sup_set_class wceq wa f2sb5rf_0 f2sb5rf_2 f2sb5rf_4 wsb f2sb5rf_1 f2sb5rf_3 wsb wa f2sb5rf_3 sup_set_class f2sb5rf_1 sup_set_class wceq f2sb5rf_4 sup_set_class f2sb5rf_2 sup_set_class wceq wa f2sb5rf_0 f2sb5rf_1 f2sb5rf_3 wsb f2sb5rf_2 f2sb5rf_4 wsb wa f2sb5rf_3 sup_set_class f2sb5rf_1 sup_set_class wceq f2sb5rf_4 sup_set_class f2sb5rf_2 sup_set_class wceq f2sb5rf_0 f2sb5rf_1 f2sb5rf_3 wsb f2sb5rf_2 f2sb5rf_4 wsb wa wa f2sb5rf_0 f2sb5rf_2 f2sb5rf_4 wsb f2sb5rf_1 f2sb5rf_3 wsb f2sb5rf_0 f2sb5rf_1 f2sb5rf_3 wsb f2sb5rf_2 f2sb5rf_4 wsb f2sb5rf_3 sup_set_class f2sb5rf_1 sup_set_class wceq f2sb5rf_4 sup_set_class f2sb5rf_2 sup_set_class wceq wa f2sb5rf_0 f2sb5rf_2 f2sb5rf_4 f2sb5rf_1 f2sb5rf_3 sbcom2 anbi2i f2sb5rf_3 sup_set_class f2sb5rf_1 sup_set_class wceq f2sb5rf_4 sup_set_class f2sb5rf_2 sup_set_class wceq f2sb5rf_0 f2sb5rf_1 f2sb5rf_3 wsb f2sb5rf_2 f2sb5rf_4 wsb anass bitri exbii f2sb5rf_0 f2sb5rf_1 f2sb5rf_3 wsb f2sb5rf_4 sup_set_class f2sb5rf_2 sup_set_class wceq f2sb5rf_0 f2sb5rf_1 f2sb5rf_3 wsb f2sb5rf_2 f2sb5rf_4 wsb wa f2sb5rf_4 wex f2sb5rf_3 sup_set_class f2sb5rf_1 sup_set_class wceq f2sb5rf_0 f2sb5rf_1 f2sb5rf_3 wsb f2sb5rf_2 f2sb5rf_4 f2sb5rf_0 f2sb5rf_1 f2sb5rf_3 f2sb5rf_4 e2sb5rf_1 nfsb sb5rf anbi2i 3bitr4ri exbii bitri $.
$}
$( Reversed double substitution.  (Contributed by NM, 3-Feb-2005.)
       (Revised by Mario Carneiro, 6-Oct-2016.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d x y $.
	$d x w $.
	$d y z $.
	$d z w $.
	f2sb6rf_0 $f wff ph $.
	f2sb6rf_1 $f set x $.
	f2sb6rf_2 $f set y $.
	f2sb6rf_3 $f set z $.
	f2sb6rf_4 $f set w $.
	e2sb6rf_0 $e |- F/ z ph $.
	e2sb6rf_1 $e |- F/ w ph $.
	2sb6rf $p |- ( ph <-> A. z A. w ( ( z = x /\ w = y ) -> [ z / x ] [ w / y ] ph ) ) $= f2sb6rf_0 f2sb6rf_3 sup_set_class f2sb6rf_1 sup_set_class wceq f2sb6rf_0 f2sb6rf_1 f2sb6rf_3 wsb wi f2sb6rf_3 wal f2sb6rf_3 sup_set_class f2sb6rf_1 sup_set_class wceq f2sb6rf_4 sup_set_class f2sb6rf_2 sup_set_class wceq wa f2sb6rf_0 f2sb6rf_2 f2sb6rf_4 wsb f2sb6rf_1 f2sb6rf_3 wsb wi f2sb6rf_4 wal f2sb6rf_3 wal f2sb6rf_0 f2sb6rf_1 f2sb6rf_3 e2sb6rf_0 sb6rf f2sb6rf_3 sup_set_class f2sb6rf_1 sup_set_class wceq f2sb6rf_0 f2sb6rf_1 f2sb6rf_3 wsb wi f2sb6rf_3 sup_set_class f2sb6rf_1 sup_set_class wceq f2sb6rf_4 sup_set_class f2sb6rf_2 sup_set_class wceq wa f2sb6rf_0 f2sb6rf_2 f2sb6rf_4 wsb f2sb6rf_1 f2sb6rf_3 wsb wi f2sb6rf_4 wal f2sb6rf_3 f2sb6rf_3 sup_set_class f2sb6rf_1 sup_set_class wceq f2sb6rf_4 sup_set_class f2sb6rf_2 sup_set_class wceq f2sb6rf_0 f2sb6rf_1 f2sb6rf_3 wsb f2sb6rf_2 f2sb6rf_4 wsb wi wi f2sb6rf_4 wal f2sb6rf_3 sup_set_class f2sb6rf_1 sup_set_class wceq f2sb6rf_4 sup_set_class f2sb6rf_2 sup_set_class wceq f2sb6rf_0 f2sb6rf_1 f2sb6rf_3 wsb f2sb6rf_2 f2sb6rf_4 wsb wi f2sb6rf_4 wal wi f2sb6rf_3 sup_set_class f2sb6rf_1 sup_set_class wceq f2sb6rf_4 sup_set_class f2sb6rf_2 sup_set_class wceq wa f2sb6rf_0 f2sb6rf_2 f2sb6rf_4 wsb f2sb6rf_1 f2sb6rf_3 wsb wi f2sb6rf_4 wal f2sb6rf_3 sup_set_class f2sb6rf_1 sup_set_class wceq f2sb6rf_0 f2sb6rf_1 f2sb6rf_3 wsb wi f2sb6rf_3 sup_set_class f2sb6rf_1 sup_set_class wceq f2sb6rf_4 sup_set_class f2sb6rf_2 sup_set_class wceq f2sb6rf_0 f2sb6rf_1 f2sb6rf_3 wsb f2sb6rf_2 f2sb6rf_4 wsb wi f2sb6rf_4 19.21v f2sb6rf_3 sup_set_class f2sb6rf_1 sup_set_class wceq f2sb6rf_4 sup_set_class f2sb6rf_2 sup_set_class wceq wa f2sb6rf_0 f2sb6rf_2 f2sb6rf_4 wsb f2sb6rf_1 f2sb6rf_3 wsb wi f2sb6rf_3 sup_set_class f2sb6rf_1 sup_set_class wceq f2sb6rf_4 sup_set_class f2sb6rf_2 sup_set_class wceq f2sb6rf_0 f2sb6rf_1 f2sb6rf_3 wsb f2sb6rf_2 f2sb6rf_4 wsb wi wi f2sb6rf_4 f2sb6rf_3 sup_set_class f2sb6rf_1 sup_set_class wceq f2sb6rf_4 sup_set_class f2sb6rf_2 sup_set_class wceq wa f2sb6rf_0 f2sb6rf_2 f2sb6rf_4 wsb f2sb6rf_1 f2sb6rf_3 wsb wi f2sb6rf_3 sup_set_class f2sb6rf_1 sup_set_class wceq f2sb6rf_4 sup_set_class f2sb6rf_2 sup_set_class wceq wa f2sb6rf_0 f2sb6rf_1 f2sb6rf_3 wsb f2sb6rf_2 f2sb6rf_4 wsb wi f2sb6rf_3 sup_set_class f2sb6rf_1 sup_set_class wceq f2sb6rf_4 sup_set_class f2sb6rf_2 sup_set_class wceq f2sb6rf_0 f2sb6rf_1 f2sb6rf_3 wsb f2sb6rf_2 f2sb6rf_4 wsb wi wi f2sb6rf_0 f2sb6rf_2 f2sb6rf_4 wsb f2sb6rf_1 f2sb6rf_3 wsb f2sb6rf_0 f2sb6rf_1 f2sb6rf_3 wsb f2sb6rf_2 f2sb6rf_4 wsb f2sb6rf_3 sup_set_class f2sb6rf_1 sup_set_class wceq f2sb6rf_4 sup_set_class f2sb6rf_2 sup_set_class wceq wa f2sb6rf_0 f2sb6rf_2 f2sb6rf_4 f2sb6rf_1 f2sb6rf_3 sbcom2 imbi2i f2sb6rf_3 sup_set_class f2sb6rf_1 sup_set_class wceq f2sb6rf_4 sup_set_class f2sb6rf_2 sup_set_class wceq f2sb6rf_0 f2sb6rf_1 f2sb6rf_3 wsb f2sb6rf_2 f2sb6rf_4 wsb impexp bitri albii f2sb6rf_0 f2sb6rf_1 f2sb6rf_3 wsb f2sb6rf_4 sup_set_class f2sb6rf_2 sup_set_class wceq f2sb6rf_0 f2sb6rf_1 f2sb6rf_3 wsb f2sb6rf_2 f2sb6rf_4 wsb wi f2sb6rf_4 wal f2sb6rf_3 sup_set_class f2sb6rf_1 sup_set_class wceq f2sb6rf_0 f2sb6rf_1 f2sb6rf_3 wsb f2sb6rf_2 f2sb6rf_4 f2sb6rf_0 f2sb6rf_1 f2sb6rf_3 f2sb6rf_4 e2sb6rf_1 nfsb sb6rf imbi2i 3bitr4ri albii bitri $.
$}
$( An alternate definition of proper substitution ~ df-sb .  By introducing
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
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$d x z $.
	$d y z $.
	$d z ph $.
	fdfsb7_0 $f wff ph $.
	fdfsb7_1 $f set x $.
	fdfsb7_2 $f set y $.
	fdfsb7_3 $f set z $.
	dfsb7 $p |- ( [ y / x ] ph <-> E. z ( z = y /\ E. x ( x = z /\ ph ) ) ) $= fdfsb7_0 fdfsb7_1 fdfsb7_3 wsb fdfsb7_3 fdfsb7_2 wsb fdfsb7_1 sup_set_class fdfsb7_3 sup_set_class wceq fdfsb7_0 wa fdfsb7_1 wex fdfsb7_3 fdfsb7_2 wsb fdfsb7_0 fdfsb7_1 fdfsb7_2 wsb fdfsb7_3 sup_set_class fdfsb7_2 sup_set_class wceq fdfsb7_1 sup_set_class fdfsb7_3 sup_set_class wceq fdfsb7_0 wa fdfsb7_1 wex wa fdfsb7_3 wex fdfsb7_0 fdfsb7_1 fdfsb7_3 wsb fdfsb7_1 sup_set_class fdfsb7_3 sup_set_class wceq fdfsb7_0 wa fdfsb7_1 wex fdfsb7_3 fdfsb7_2 fdfsb7_0 fdfsb7_1 fdfsb7_3 sb5 sbbii fdfsb7_0 fdfsb7_1 fdfsb7_2 fdfsb7_3 fdfsb7_0 fdfsb7_3 nfv sbco2 fdfsb7_1 sup_set_class fdfsb7_3 sup_set_class wceq fdfsb7_0 wa fdfsb7_1 wex fdfsb7_3 fdfsb7_2 sb5 3bitr3i $.
$}
$( This version of ~ dfsb7 does not require that ` ph ` and ` z ` be
       distinct.  This permits it to be used as a definition for substitution
       in a formalization that omits the logically redundant axiom ~ ax-17 i.e.
       that doesn't have the concept of a variable not occurring in a wff.
       ( ~ df-sb is also suitable, but its mixing of free and bound variables
       is distasteful to some logicians.)  (Contributed by NM, 26-Jul-2006.)
       (Revised by Mario Carneiro, 6-Oct-2016.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$d x z $.
	$d y z $.
	fsb7f_0 $f wff ph $.
	fsb7f_1 $f set x $.
	fsb7f_2 $f set y $.
	fsb7f_3 $f set z $.
	esb7f_0 $e |- F/ z ph $.
	sb7f $p |- ( [ y / x ] ph <-> E. z ( z = y /\ E. x ( x = z /\ ph ) ) ) $= fsb7f_0 fsb7f_1 fsb7f_3 wsb fsb7f_3 fsb7f_2 wsb fsb7f_1 sup_set_class fsb7f_3 sup_set_class wceq fsb7f_0 wa fsb7f_1 wex fsb7f_3 fsb7f_2 wsb fsb7f_0 fsb7f_1 fsb7f_2 wsb fsb7f_3 sup_set_class fsb7f_2 sup_set_class wceq fsb7f_1 sup_set_class fsb7f_3 sup_set_class wceq fsb7f_0 wa fsb7f_1 wex wa fsb7f_3 wex fsb7f_0 fsb7f_1 fsb7f_3 wsb fsb7f_1 sup_set_class fsb7f_3 sup_set_class wceq fsb7f_0 wa fsb7f_1 wex fsb7f_3 fsb7f_2 fsb7f_0 fsb7f_1 fsb7f_3 sb5 sbbii fsb7f_0 fsb7f_1 fsb7f_2 fsb7f_3 esb7f_0 sbco2 fsb7f_1 sup_set_class fsb7f_3 sup_set_class wceq fsb7f_0 wa fsb7f_1 wex fsb7f_3 fsb7f_2 sb5 3bitr3i $.
$}
$( This version of ~ dfsb7 does not require that ` ph ` and ` z ` be
       distinct.  This permits it to be used as a definition for substitution
       in a formalization that omits the logically redundant axiom ~ ax-17 i.e.
       that doesn't have the concept of a variable not occurring in a wff.
       ( ~ df-sb is also suitable, but its mixing of free and bound variables
       is distasteful to some logicians.)  (Contributed by NM, 26-Jul-2006.)
       (Proof shortened by Andrew Salmon, 25-May-2011.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$d x z $.
	$d y z $.
	fsb7h_0 $f wff ph $.
	fsb7h_1 $f set x $.
	fsb7h_2 $f set y $.
	fsb7h_3 $f set z $.
	esb7h_0 $e |- ( ph -> A. z ph ) $.
	sb7h $p |- ( [ y / x ] ph <-> E. z ( z = y /\ E. x ( x = z /\ ph ) ) ) $= fsb7h_0 fsb7h_1 fsb7h_2 fsb7h_3 fsb7h_0 fsb7h_3 esb7h_0 nfi sb7f $.
$}
$( Hao Wang's identity axiom P6 in Irving Copi, _Symbolic Logic_ (5th ed.,
       1979), p. 328.  In traditional predicate calculus, this is a sole axiom
       for identity from which the usual ones can be derived.  (Contributed by
       NM, 9-May-2005.)  (Revised by Mario Carneiro, 6-Oct-2016.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$d x y $.
	fsb10f_0 $f wff ph $.
	fsb10f_1 $f set x $.
	fsb10f_2 $f set y $.
	fsb10f_3 $f set z $.
	esb10f_0 $e |- F/ x ph $.
	sb10f $p |- ( [ y / z ] ph <-> E. x ( x = y /\ [ x / z ] ph ) ) $= fsb10f_1 sup_set_class fsb10f_2 sup_set_class wceq fsb10f_0 fsb10f_3 fsb10f_1 wsb wa fsb10f_1 wex fsb10f_0 fsb10f_3 fsb10f_2 wsb fsb10f_0 fsb10f_3 fsb10f_1 wsb fsb10f_0 fsb10f_3 fsb10f_2 wsb fsb10f_1 fsb10f_2 fsb10f_0 fsb10f_3 fsb10f_2 fsb10f_1 esb10f_0 nfsb fsb10f_0 fsb10f_1 fsb10f_2 fsb10f_3 sbequ equsex bicomi $.
$}
$( An identity law for substitution.  Used in proof of Theorem 9.7 of
       [Megill] p. 449 (p. 16 of the preprint).  (Contributed by NM,
       5-Aug-1993.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$d x ph $.
	fsbid2v_0 $f wff ph $.
	fsbid2v_1 $f set x $.
	fsbid2v_2 $f set y $.
	sbid2v $p |- ( [ y / x ] [ x / y ] ph <-> ph ) $= fsbid2v_0 fsbid2v_1 fsbid2v_2 fsbid2v_0 fsbid2v_1 nfv sbid2 $.
$}
$( Elimination of substitution.  (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$d x y $.
	$d x ph $.
	fsbelx_0 $f wff ph $.
	fsbelx_1 $f set x $.
	fsbelx_2 $f set y $.
	sbelx $p |- ( ph <-> E. x ( x = y /\ [ x / y ] ph ) ) $= fsbelx_0 fsbelx_0 fsbelx_2 fsbelx_1 wsb fsbelx_1 fsbelx_2 wsb fsbelx_1 sup_set_class fsbelx_2 sup_set_class wceq fsbelx_0 fsbelx_2 fsbelx_1 wsb wa fsbelx_1 wex fsbelx_0 fsbelx_1 fsbelx_2 sbid2v fsbelx_0 fsbelx_2 fsbelx_1 wsb fsbelx_1 fsbelx_2 sb5 bitr3i $.
$}
$( Note:  A more general case could also be proved with
       "$d x z $.  $d y w $.  $d x ph $.  $d y ph $.", but with more
       difficulty. $)
$( Elimination of double substitution.  (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d x y z $.
	$d w y $.
	$d x y ph $.
	fsbel2x_0 $f wff ph $.
	fsbel2x_1 $f set x $.
	fsbel2x_2 $f set y $.
	fsbel2x_3 $f set z $.
	fsbel2x_4 $f set w $.
	sbel2x $p |- ( ph <-> E. x E. y ( ( x = z /\ y = w ) /\ [ y / w ] [ x / z ] ph ) ) $= fsbel2x_0 fsbel2x_1 sup_set_class fsbel2x_3 sup_set_class wceq fsbel2x_2 sup_set_class fsbel2x_4 sup_set_class wceq fsbel2x_0 fsbel2x_3 fsbel2x_1 wsb fsbel2x_4 fsbel2x_2 wsb wa wa fsbel2x_2 wex fsbel2x_1 wex fsbel2x_1 sup_set_class fsbel2x_3 sup_set_class wceq fsbel2x_2 sup_set_class fsbel2x_4 sup_set_class wceq wa fsbel2x_0 fsbel2x_3 fsbel2x_1 wsb fsbel2x_4 fsbel2x_2 wsb wa fsbel2x_2 wex fsbel2x_1 wex fsbel2x_1 sup_set_class fsbel2x_3 sup_set_class wceq fsbel2x_0 fsbel2x_3 fsbel2x_1 wsb wa fsbel2x_1 wex fsbel2x_1 sup_set_class fsbel2x_3 sup_set_class wceq fsbel2x_2 sup_set_class fsbel2x_4 sup_set_class wceq fsbel2x_0 fsbel2x_3 fsbel2x_1 wsb fsbel2x_4 fsbel2x_2 wsb wa fsbel2x_2 wex wa fsbel2x_1 wex fsbel2x_0 fsbel2x_1 sup_set_class fsbel2x_3 sup_set_class wceq fsbel2x_2 sup_set_class fsbel2x_4 sup_set_class wceq fsbel2x_0 fsbel2x_3 fsbel2x_1 wsb fsbel2x_4 fsbel2x_2 wsb wa wa fsbel2x_2 wex fsbel2x_1 wex fsbel2x_1 sup_set_class fsbel2x_3 sup_set_class wceq fsbel2x_0 fsbel2x_3 fsbel2x_1 wsb wa fsbel2x_1 sup_set_class fsbel2x_3 sup_set_class wceq fsbel2x_2 sup_set_class fsbel2x_4 sup_set_class wceq fsbel2x_0 fsbel2x_3 fsbel2x_1 wsb fsbel2x_4 fsbel2x_2 wsb wa fsbel2x_2 wex wa fsbel2x_1 fsbel2x_0 fsbel2x_3 fsbel2x_1 wsb fsbel2x_2 sup_set_class fsbel2x_4 sup_set_class wceq fsbel2x_0 fsbel2x_3 fsbel2x_1 wsb fsbel2x_4 fsbel2x_2 wsb wa fsbel2x_2 wex fsbel2x_1 sup_set_class fsbel2x_3 sup_set_class wceq fsbel2x_0 fsbel2x_3 fsbel2x_1 wsb fsbel2x_2 fsbel2x_4 sbelx anbi2i exbii fsbel2x_0 fsbel2x_1 fsbel2x_3 sbelx fsbel2x_1 sup_set_class fsbel2x_3 sup_set_class wceq fsbel2x_2 sup_set_class fsbel2x_4 sup_set_class wceq fsbel2x_0 fsbel2x_3 fsbel2x_1 wsb fsbel2x_4 fsbel2x_2 wsb wa fsbel2x_1 fsbel2x_2 exdistr 3bitr4i fsbel2x_1 sup_set_class fsbel2x_3 sup_set_class wceq fsbel2x_2 sup_set_class fsbel2x_4 sup_set_class wceq wa fsbel2x_0 fsbel2x_3 fsbel2x_1 wsb fsbel2x_4 fsbel2x_2 wsb wa fsbel2x_1 sup_set_class fsbel2x_3 sup_set_class wceq fsbel2x_2 sup_set_class fsbel2x_4 sup_set_class wceq fsbel2x_0 fsbel2x_3 fsbel2x_1 wsb fsbel2x_4 fsbel2x_2 wsb wa wa fsbel2x_1 fsbel2x_2 fsbel2x_1 sup_set_class fsbel2x_3 sup_set_class wceq fsbel2x_2 sup_set_class fsbel2x_4 sup_set_class wceq fsbel2x_0 fsbel2x_3 fsbel2x_1 wsb fsbel2x_4 fsbel2x_2 wsb anass 2exbii bitr4i $.
$}
$( A theorem used in elimination of disjoint variable restriction on ` x `
       and ` y ` by replacing it with a distinctor ` -. A. x x = z ` .
       (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$d x y $.
	fsbal1_0 $f wff ph $.
	fsbal1_1 $f set x $.
	fsbal1_2 $f set y $.
	fsbal1_3 $f set z $.
	sbal1 $p |- ( -. A. x x = z -> ( [ z / y ] A. x ph <-> A. x [ z / y ] ph ) ) $= fsbal1_2 sup_set_class fsbal1_3 sup_set_class wceq fsbal1_2 wal fsbal1_1 sup_set_class fsbal1_3 sup_set_class wceq fsbal1_1 wal wn fsbal1_0 fsbal1_1 wal fsbal1_2 fsbal1_3 wsb fsbal1_0 fsbal1_2 fsbal1_3 wsb fsbal1_1 wal wb wi fsbal1_2 sup_set_class fsbal1_3 sup_set_class wceq fsbal1_2 wal fsbal1_0 fsbal1_1 wal fsbal1_2 fsbal1_3 wsb fsbal1_0 fsbal1_2 fsbal1_3 wsb fsbal1_1 wal wb fsbal1_1 sup_set_class fsbal1_3 sup_set_class wceq fsbal1_1 wal wn fsbal1_2 sup_set_class fsbal1_3 sup_set_class wceq fsbal1_2 wal fsbal1_0 fsbal1_1 wal fsbal1_0 fsbal1_1 wal fsbal1_2 fsbal1_3 wsb fsbal1_0 fsbal1_2 fsbal1_3 wsb fsbal1_1 wal fsbal1_2 sup_set_class fsbal1_3 sup_set_class wceq fsbal1_0 fsbal1_1 wal fsbal1_0 fsbal1_1 wal fsbal1_2 fsbal1_3 wsb wb fsbal1_2 fsbal1_0 fsbal1_1 wal fsbal1_2 fsbal1_3 sbequ12 sps fsbal1_0 fsbal1_0 fsbal1_2 fsbal1_3 wsb fsbal1_2 fsbal1_3 fsbal1_1 fsbal1_2 sup_set_class fsbal1_3 sup_set_class wceq fsbal1_0 fsbal1_0 fsbal1_2 fsbal1_3 wsb wb fsbal1_2 fsbal1_0 fsbal1_2 fsbal1_3 sbequ12 sps dral2 bitr3d a1d fsbal1_2 sup_set_class fsbal1_3 sup_set_class wceq fsbal1_2 wal wn fsbal1_1 sup_set_class fsbal1_3 sup_set_class wceq fsbal1_1 wal wn fsbal1_0 fsbal1_1 wal fsbal1_2 fsbal1_3 wsb fsbal1_0 fsbal1_2 fsbal1_3 wsb fsbal1_1 wal wb fsbal1_2 sup_set_class fsbal1_3 sup_set_class wceq fsbal1_2 wal wn fsbal1_1 sup_set_class fsbal1_3 sup_set_class wceq fsbal1_1 wal wn wa fsbal1_0 fsbal1_1 wal fsbal1_2 fsbal1_3 wsb fsbal1_0 fsbal1_2 fsbal1_3 wsb fsbal1_1 wal fsbal1_1 sup_set_class fsbal1_3 sup_set_class wceq fsbal1_1 wal wn fsbal1_0 fsbal1_1 wal fsbal1_2 fsbal1_3 wsb fsbal1_0 fsbal1_2 fsbal1_3 wsb fsbal1_1 wal wi fsbal1_2 sup_set_class fsbal1_3 sup_set_class wceq fsbal1_2 wal wn fsbal1_1 sup_set_class fsbal1_3 sup_set_class wceq fsbal1_1 wal wn fsbal1_0 fsbal1_1 wal fsbal1_2 fsbal1_3 wsb fsbal1_0 fsbal1_1 wal fsbal1_2 fsbal1_3 wsb fsbal1_1 wal fsbal1_0 fsbal1_2 fsbal1_3 wsb fsbal1_1 wal fsbal1_1 sup_set_class fsbal1_3 sup_set_class wceq fsbal1_1 wal wn fsbal1_0 fsbal1_1 wal fsbal1_2 fsbal1_3 wsb fsbal1_1 fsbal1_0 fsbal1_1 wal fsbal1_2 fsbal1_3 fsbal1_1 fsbal1_0 fsbal1_1 nfa1 nfsb4 nfrd fsbal1_0 fsbal1_1 wal fsbal1_2 fsbal1_3 wsb fsbal1_0 fsbal1_2 fsbal1_3 wsb fsbal1_1 fsbal1_0 fsbal1_1 wal fsbal1_0 fsbal1_2 fsbal1_3 fsbal1_0 fsbal1_1 sp sbimi alimi syl6 adantl fsbal1_2 sup_set_class fsbal1_3 sup_set_class wceq fsbal1_2 wal wn fsbal1_0 fsbal1_2 fsbal1_3 wsb fsbal1_1 wal fsbal1_2 sup_set_class fsbal1_3 sup_set_class wceq fsbal1_0 wi fsbal1_1 wal fsbal1_2 wal fsbal1_1 sup_set_class fsbal1_3 sup_set_class wceq fsbal1_1 wal wn fsbal1_0 fsbal1_1 wal fsbal1_2 fsbal1_3 wsb fsbal1_2 sup_set_class fsbal1_3 sup_set_class wceq fsbal1_2 wal wn fsbal1_0 fsbal1_2 fsbal1_3 wsb fsbal1_1 wal fsbal1_2 sup_set_class fsbal1_3 sup_set_class wceq fsbal1_0 wi fsbal1_2 wal fsbal1_1 wal fsbal1_2 sup_set_class fsbal1_3 sup_set_class wceq fsbal1_0 wi fsbal1_1 wal fsbal1_2 wal fsbal1_0 fsbal1_2 fsbal1_3 wsb fsbal1_1 wal fsbal1_2 sup_set_class fsbal1_3 sup_set_class wceq fsbal1_0 wi fsbal1_2 wal fsbal1_1 wal wi fsbal1_2 fsbal1_3 fsbal1_1 fsbal1_2 sup_set_class fsbal1_3 sup_set_class wceq fsbal1_2 wal wn fsbal1_0 fsbal1_2 fsbal1_3 wsb fsbal1_2 sup_set_class fsbal1_3 sup_set_class wceq fsbal1_0 wi fsbal1_2 wal fsbal1_1 fsbal1_0 fsbal1_2 fsbal1_3 sb4 al2imi hbnaes fsbal1_2 sup_set_class fsbal1_3 sup_set_class wceq fsbal1_0 wi fsbal1_1 fsbal1_2 ax-7 syl6 fsbal1_2 sup_set_class fsbal1_3 sup_set_class wceq fsbal1_0 wi fsbal1_1 wal fsbal1_2 wal fsbal1_0 fsbal1_1 wal fsbal1_2 fsbal1_3 wsb wi fsbal1_1 fsbal1_3 fsbal1_2 fsbal1_1 sup_set_class fsbal1_3 sup_set_class wceq fsbal1_1 wal wn fsbal1_2 wal fsbal1_2 sup_set_class fsbal1_3 sup_set_class wceq fsbal1_0 wi fsbal1_1 wal fsbal1_2 wal fsbal1_2 sup_set_class fsbal1_3 sup_set_class wceq fsbal1_0 fsbal1_1 wal wi fsbal1_2 wal fsbal1_0 fsbal1_1 wal fsbal1_2 fsbal1_3 wsb fsbal1_1 sup_set_class fsbal1_3 sup_set_class wceq fsbal1_1 wal wn fsbal1_2 sup_set_class fsbal1_3 sup_set_class wceq fsbal1_0 wi fsbal1_1 wal fsbal1_2 sup_set_class fsbal1_3 sup_set_class wceq fsbal1_0 fsbal1_1 wal wi fsbal1_2 fsbal1_1 sup_set_class fsbal1_3 sup_set_class wceq fsbal1_1 wal wn fsbal1_2 sup_set_class fsbal1_3 sup_set_class wceq fsbal1_2 sup_set_class fsbal1_3 sup_set_class wceq fsbal1_1 wal fsbal1_2 sup_set_class fsbal1_3 sup_set_class wceq fsbal1_0 wi fsbal1_1 wal fsbal1_0 fsbal1_1 wal fsbal1_1 fsbal1_3 fsbal1_2 dveeq2 fsbal1_2 sup_set_class fsbal1_3 sup_set_class wceq fsbal1_0 fsbal1_1 alim syl9 al2imi fsbal1_0 fsbal1_1 wal fsbal1_2 fsbal1_3 sb2 syl6 hbnaes sylan9 impbid ex pm2.61i $.
$}
$( Move universal quantifier in and out of substitution.  (Contributed by
       NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$d x y $.
	$d x z $.
	fsbal_0 $f wff ph $.
	fsbal_1 $f set x $.
	fsbal_2 $f set y $.
	fsbal_3 $f set z $.
	sbal $p |- ( [ z / y ] A. x ph <-> A. x [ z / y ] ph ) $= fsbal_1 sup_set_class fsbal_3 sup_set_class wceq fsbal_1 wal fsbal_0 fsbal_1 wal fsbal_2 fsbal_3 wsb fsbal_0 fsbal_2 fsbal_3 wsb fsbal_1 wal wb fsbal_1 sup_set_class fsbal_3 sup_set_class wceq fsbal_1 wal fsbal_0 fsbal_2 fsbal_3 wsb fsbal_0 fsbal_1 wal fsbal_2 fsbal_3 wsb fsbal_0 fsbal_2 fsbal_3 wsb fsbal_1 wal fsbal_1 sup_set_class fsbal_3 sup_set_class wceq fsbal_1 wal fsbal_2 fsbal_3 wsb fsbal_0 fsbal_0 fsbal_1 wal wb fsbal_2 fsbal_3 wsb fsbal_1 sup_set_class fsbal_3 sup_set_class wceq fsbal_1 wal fsbal_0 fsbal_2 fsbal_3 wsb fsbal_0 fsbal_1 wal fsbal_2 fsbal_3 wsb wb fsbal_1 sup_set_class fsbal_3 sup_set_class wceq fsbal_1 wal fsbal_0 fsbal_0 fsbal_1 wal wb fsbal_2 fsbal_3 fsbal_0 fsbal_1 fsbal_3 fsbal_1 a16gb sbimi fsbal_1 fsbal_3 fsbal_2 fsbal_3 sbequ5 fsbal_0 fsbal_0 fsbal_1 wal fsbal_2 fsbal_3 sbbi 3imtr3i fsbal_0 fsbal_2 fsbal_3 wsb fsbal_1 fsbal_3 fsbal_1 a16gb bitr3d fsbal_0 fsbal_1 fsbal_2 fsbal_3 sbal1 pm2.61i $.
$}
$( Move existential quantifier in and out of substitution.  (Contributed by
       NM, 27-Sep-2003.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$d x y $.
	$d x z $.
	fsbex_0 $f wff ph $.
	fsbex_1 $f set x $.
	fsbex_2 $f set y $.
	fsbex_3 $f set z $.
	sbex $p |- ( [ z / y ] E. x ph <-> E. x [ z / y ] ph ) $= fsbex_0 wn fsbex_1 wal wn fsbex_2 fsbex_3 wsb fsbex_0 fsbex_2 fsbex_3 wsb wn fsbex_1 wal wn fsbex_0 fsbex_1 wex fsbex_2 fsbex_3 wsb fsbex_0 fsbex_2 fsbex_3 wsb fsbex_1 wex fsbex_0 wn fsbex_1 wal wn fsbex_2 fsbex_3 wsb fsbex_0 wn fsbex_1 wal fsbex_2 fsbex_3 wsb fsbex_0 fsbex_2 fsbex_3 wsb wn fsbex_1 wal fsbex_0 wn fsbex_1 wal fsbex_2 fsbex_3 sbn fsbex_0 wn fsbex_1 wal fsbex_2 fsbex_3 wsb fsbex_0 wn fsbex_2 fsbex_3 wsb fsbex_1 wal fsbex_0 fsbex_2 fsbex_3 wsb wn fsbex_1 wal fsbex_0 wn fsbex_1 fsbex_2 fsbex_3 sbal fsbex_0 wn fsbex_2 fsbex_3 wsb fsbex_0 fsbex_2 fsbex_3 wsb wn fsbex_1 fsbex_0 fsbex_2 fsbex_3 sbn albii bitri xchbinx fsbex_0 fsbex_1 wex fsbex_0 wn fsbex_1 wal wn fsbex_2 fsbex_3 fsbex_0 fsbex_1 df-ex sbbii fsbex_0 fsbex_2 fsbex_3 wsb fsbex_1 df-ex 3bitr4i $.
$}
$( Quantify with new variable inside substitution.  (Contributed by NM,
       18-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v z $.
	$d x z $.
	$d y z $.
	fsbalv_0 $f wff ph $.
	fsbalv_1 $f wff ps $.
	fsbalv_2 $f set x $.
	fsbalv_3 $f set y $.
	fsbalv_4 $f set z $.
	esbalv_0 $e |- ( [ y / x ] ph <-> ps ) $.
	sbalv $p |- ( [ y / x ] A. z ph <-> A. z ps ) $= fsbalv_0 fsbalv_4 wal fsbalv_2 fsbalv_3 wsb fsbalv_0 fsbalv_2 fsbalv_3 wsb fsbalv_4 wal fsbalv_1 fsbalv_4 wal fsbalv_0 fsbalv_4 fsbalv_2 fsbalv_3 sbal fsbalv_0 fsbalv_2 fsbalv_3 wsb fsbalv_1 fsbalv_4 esbalv_0 albii bitri $.
$}
$( An equivalent expression for existence.  (Contributed by NM,
       2-Feb-2005.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$d x y $.
	$d y ph $.
	fexsb_0 $f wff ph $.
	fexsb_1 $f set x $.
	fexsb_2 $f set y $.
	exsb $p |- ( E. x ph <-> E. y A. x ( x = y -> ph ) ) $= fexsb_0 fexsb_1 sup_set_class fexsb_2 sup_set_class wceq fexsb_0 wi fexsb_1 wal fexsb_1 fexsb_2 fexsb_0 fexsb_2 nfv fexsb_1 sup_set_class fexsb_2 sup_set_class wceq fexsb_0 wi fexsb_1 nfa1 fexsb_1 sup_set_class fexsb_2 sup_set_class wceq fexsb_0 fexsb_1 sup_set_class fexsb_2 sup_set_class wceq fexsb_0 wi fexsb_1 wal fexsb_0 fexsb_1 fexsb_2 ax11v fexsb_1 sup_set_class fexsb_2 sup_set_class wceq fexsb_0 wi fexsb_1 wal fexsb_1 sup_set_class fexsb_2 sup_set_class wceq fexsb_0 fexsb_1 sup_set_class fexsb_2 sup_set_class wceq fexsb_0 wi fexsb_1 sp com12 impbid cbvex $.
$}
$( An equivalent expression for existence.  Obsolete as of 19-Jun-2017.
       (Contributed by NM, 2-Feb-2005.)  (New usage is discouraged.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$d x y $.
	$d y ph $.
	fexsbOLD_0 $f wff ph $.
	fexsbOLD_1 $f set x $.
	fexsbOLD_2 $f set y $.
	exsbOLD $p |- ( E. x ph <-> E. y A. x ( x = y -> ph ) ) $= fexsbOLD_0 fexsbOLD_1 wex fexsbOLD_0 fexsbOLD_1 fexsbOLD_2 wsb fexsbOLD_2 wex fexsbOLD_1 sup_set_class fexsbOLD_2 sup_set_class wceq fexsbOLD_0 wi fexsbOLD_1 wal fexsbOLD_2 wex fexsbOLD_0 fexsbOLD_1 fexsbOLD_2 fexsbOLD_0 fexsbOLD_2 nfv sb8e fexsbOLD_0 fexsbOLD_1 fexsbOLD_2 wsb fexsbOLD_1 sup_set_class fexsbOLD_2 sup_set_class wceq fexsbOLD_0 wi fexsbOLD_1 wal fexsbOLD_2 fexsbOLD_0 fexsbOLD_1 fexsbOLD_2 sb6 exbii bitri $.
$}
$( An equivalent expression for double existence.  (Contributed by NM,
       2-Feb-2005.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d x y z $.
	$d y w $.
	$d z w ph $.
	f2exsb_0 $f wff ph $.
	f2exsb_1 $f set x $.
	f2exsb_2 $f set y $.
	f2exsb_3 $f set z $.
	f2exsb_4 $f set w $.
	2exsb $p |- ( E. x E. y ph <-> E. z E. w A. x A. y ( ( x = z /\ y = w ) -> ph ) ) $= f2exsb_0 f2exsb_2 wex f2exsb_1 wex f2exsb_2 sup_set_class f2exsb_4 sup_set_class wceq f2exsb_0 wi f2exsb_2 wal f2exsb_1 wex f2exsb_4 wex f2exsb_1 sup_set_class f2exsb_3 sup_set_class wceq f2exsb_2 sup_set_class f2exsb_4 sup_set_class wceq wa f2exsb_0 wi f2exsb_2 wal f2exsb_1 wal f2exsb_4 wex f2exsb_3 wex f2exsb_0 f2exsb_2 wex f2exsb_1 wex f2exsb_2 sup_set_class f2exsb_4 sup_set_class wceq f2exsb_0 wi f2exsb_2 wal f2exsb_4 wex f2exsb_1 wex f2exsb_2 sup_set_class f2exsb_4 sup_set_class wceq f2exsb_0 wi f2exsb_2 wal f2exsb_1 wex f2exsb_4 wex f2exsb_0 f2exsb_2 wex f2exsb_2 sup_set_class f2exsb_4 sup_set_class wceq f2exsb_0 wi f2exsb_2 wal f2exsb_4 wex f2exsb_1 f2exsb_0 f2exsb_2 f2exsb_4 exsb exbii f2exsb_2 sup_set_class f2exsb_4 sup_set_class wceq f2exsb_0 wi f2exsb_2 wal f2exsb_1 f2exsb_4 excom bitri f2exsb_2 sup_set_class f2exsb_4 sup_set_class wceq f2exsb_0 wi f2exsb_2 wal f2exsb_1 wex f2exsb_4 wex f2exsb_1 sup_set_class f2exsb_3 sup_set_class wceq f2exsb_2 sup_set_class f2exsb_4 sup_set_class wceq wa f2exsb_0 wi f2exsb_2 wal f2exsb_1 wal f2exsb_3 wex f2exsb_4 wex f2exsb_1 sup_set_class f2exsb_3 sup_set_class wceq f2exsb_2 sup_set_class f2exsb_4 sup_set_class wceq wa f2exsb_0 wi f2exsb_2 wal f2exsb_1 wal f2exsb_4 wex f2exsb_3 wex f2exsb_2 sup_set_class f2exsb_4 sup_set_class wceq f2exsb_0 wi f2exsb_2 wal f2exsb_1 wex f2exsb_1 sup_set_class f2exsb_3 sup_set_class wceq f2exsb_2 sup_set_class f2exsb_4 sup_set_class wceq wa f2exsb_0 wi f2exsb_2 wal f2exsb_1 wal f2exsb_3 wex f2exsb_4 f2exsb_2 sup_set_class f2exsb_4 sup_set_class wceq f2exsb_0 wi f2exsb_2 wal f2exsb_1 wex f2exsb_1 sup_set_class f2exsb_3 sup_set_class wceq f2exsb_2 sup_set_class f2exsb_4 sup_set_class wceq f2exsb_0 wi f2exsb_2 wal wi f2exsb_1 wal f2exsb_3 wex f2exsb_1 sup_set_class f2exsb_3 sup_set_class wceq f2exsb_2 sup_set_class f2exsb_4 sup_set_class wceq wa f2exsb_0 wi f2exsb_2 wal f2exsb_1 wal f2exsb_3 wex f2exsb_2 sup_set_class f2exsb_4 sup_set_class wceq f2exsb_0 wi f2exsb_2 wal f2exsb_1 f2exsb_3 exsb f2exsb_1 sup_set_class f2exsb_3 sup_set_class wceq f2exsb_2 sup_set_class f2exsb_4 sup_set_class wceq f2exsb_0 wi f2exsb_2 wal wi f2exsb_1 wal f2exsb_1 sup_set_class f2exsb_3 sup_set_class wceq f2exsb_2 sup_set_class f2exsb_4 sup_set_class wceq wa f2exsb_0 wi f2exsb_2 wal f2exsb_1 wal f2exsb_3 f2exsb_1 sup_set_class f2exsb_3 sup_set_class wceq f2exsb_2 sup_set_class f2exsb_4 sup_set_class wceq f2exsb_0 wi f2exsb_2 wal wi f2exsb_1 sup_set_class f2exsb_3 sup_set_class wceq f2exsb_2 sup_set_class f2exsb_4 sup_set_class wceq wa f2exsb_0 wi f2exsb_2 wal f2exsb_1 f2exsb_1 sup_set_class f2exsb_3 sup_set_class wceq f2exsb_2 sup_set_class f2exsb_4 sup_set_class wceq wa f2exsb_0 wi f2exsb_2 wal f2exsb_1 sup_set_class f2exsb_3 sup_set_class wceq f2exsb_2 sup_set_class f2exsb_4 sup_set_class wceq f2exsb_0 wi wi f2exsb_2 wal f2exsb_1 sup_set_class f2exsb_3 sup_set_class wceq f2exsb_2 sup_set_class f2exsb_4 sup_set_class wceq f2exsb_0 wi f2exsb_2 wal wi f2exsb_1 sup_set_class f2exsb_3 sup_set_class wceq f2exsb_2 sup_set_class f2exsb_4 sup_set_class wceq wa f2exsb_0 wi f2exsb_1 sup_set_class f2exsb_3 sup_set_class wceq f2exsb_2 sup_set_class f2exsb_4 sup_set_class wceq f2exsb_0 wi wi f2exsb_2 f2exsb_1 sup_set_class f2exsb_3 sup_set_class wceq f2exsb_2 sup_set_class f2exsb_4 sup_set_class wceq f2exsb_0 impexp albii f2exsb_1 sup_set_class f2exsb_3 sup_set_class wceq f2exsb_2 sup_set_class f2exsb_4 sup_set_class wceq f2exsb_0 wi f2exsb_2 19.21v bitr2i albii exbii bitri exbii f2exsb_1 sup_set_class f2exsb_3 sup_set_class wceq f2exsb_2 sup_set_class f2exsb_4 sup_set_class wceq wa f2exsb_0 wi f2exsb_2 wal f2exsb_1 wal f2exsb_4 f2exsb_3 excom bitri bitri $.
$}
$( Version of ~ dvelim that doesn't use ~ ax-10 .  (See ~ dvelimh for a
       version that doesn't use ~ ax-11 .)  (Contributed by NM, 17-May-2008.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v z $.
	$d z ps $.
	$d x z $.
	$d y z $.
	fdvelimALT_0 $f wff ph $.
	fdvelimALT_1 $f wff ps $.
	fdvelimALT_2 $f set x $.
	fdvelimALT_3 $f set y $.
	fdvelimALT_4 $f set z $.
	edvelimALT_0 $e |- ( ph -> A. x ph ) $.
	edvelimALT_1 $e |- ( z = y -> ( ph <-> ps ) ) $.
	dvelimALT $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $= fdvelimALT_2 sup_set_class fdvelimALT_3 sup_set_class wceq fdvelimALT_2 wal wn fdvelimALT_4 sup_set_class fdvelimALT_3 sup_set_class wceq fdvelimALT_0 wi fdvelimALT_4 wal fdvelimALT_4 sup_set_class fdvelimALT_3 sup_set_class wceq fdvelimALT_0 wi fdvelimALT_4 wal fdvelimALT_2 wal fdvelimALT_1 fdvelimALT_1 fdvelimALT_2 wal fdvelimALT_2 sup_set_class fdvelimALT_3 sup_set_class wceq fdvelimALT_2 wal wn fdvelimALT_4 sup_set_class fdvelimALT_3 sup_set_class wceq fdvelimALT_0 wi fdvelimALT_2 fdvelimALT_4 fdvelimALT_2 sup_set_class fdvelimALT_3 sup_set_class wceq fdvelimALT_2 wal wn fdvelimALT_4 ax-17 fdvelimALT_2 sup_set_class fdvelimALT_4 sup_set_class wceq fdvelimALT_2 wal fdvelimALT_2 sup_set_class fdvelimALT_3 sup_set_class wceq fdvelimALT_2 wal wn fdvelimALT_4 sup_set_class fdvelimALT_3 sup_set_class wceq fdvelimALT_0 wi fdvelimALT_4 sup_set_class fdvelimALT_3 sup_set_class wceq fdvelimALT_0 wi fdvelimALT_2 wal wi wi fdvelimALT_2 sup_set_class fdvelimALT_4 sup_set_class wceq fdvelimALT_2 wal fdvelimALT_4 sup_set_class fdvelimALT_3 sup_set_class wceq fdvelimALT_0 wi fdvelimALT_4 sup_set_class fdvelimALT_3 sup_set_class wceq fdvelimALT_0 wi fdvelimALT_2 wal wi fdvelimALT_2 sup_set_class fdvelimALT_3 sup_set_class wceq fdvelimALT_2 wal wn fdvelimALT_4 sup_set_class fdvelimALT_3 sup_set_class wceq fdvelimALT_0 wi fdvelimALT_2 fdvelimALT_4 ax16ALT a1d fdvelimALT_2 sup_set_class fdvelimALT_4 sup_set_class wceq fdvelimALT_2 wal wn fdvelimALT_2 sup_set_class fdvelimALT_3 sup_set_class wceq fdvelimALT_2 wal wn fdvelimALT_4 sup_set_class fdvelimALT_3 sup_set_class wceq fdvelimALT_0 wi fdvelimALT_4 sup_set_class fdvelimALT_3 sup_set_class wceq fdvelimALT_0 wi fdvelimALT_2 wal wi fdvelimALT_2 sup_set_class fdvelimALT_4 sup_set_class wceq fdvelimALT_2 wal wn fdvelimALT_2 sup_set_class fdvelimALT_3 sup_set_class wceq fdvelimALT_2 wal wn wa fdvelimALT_4 sup_set_class fdvelimALT_3 sup_set_class wceq fdvelimALT_0 fdvelimALT_2 fdvelimALT_2 sup_set_class fdvelimALT_4 sup_set_class wceq fdvelimALT_2 wal wn fdvelimALT_2 sup_set_class fdvelimALT_3 sup_set_class wceq fdvelimALT_2 wal wn fdvelimALT_2 fdvelimALT_2 sup_set_class fdvelimALT_4 sup_set_class wceq fdvelimALT_2 hbn1 fdvelimALT_2 sup_set_class fdvelimALT_3 sup_set_class wceq fdvelimALT_2 hbn1 hban fdvelimALT_2 sup_set_class fdvelimALT_4 sup_set_class wceq fdvelimALT_2 wal wn fdvelimALT_2 sup_set_class fdvelimALT_3 sup_set_class wceq fdvelimALT_2 wal wn fdvelimALT_4 sup_set_class fdvelimALT_3 sup_set_class wceq fdvelimALT_4 sup_set_class fdvelimALT_3 sup_set_class wceq fdvelimALT_2 wal wi fdvelimALT_4 fdvelimALT_3 fdvelimALT_2 ax12o imp fdvelimALT_0 fdvelimALT_0 fdvelimALT_2 wal wi fdvelimALT_2 sup_set_class fdvelimALT_4 sup_set_class wceq fdvelimALT_2 wal wn fdvelimALT_2 sup_set_class fdvelimALT_3 sup_set_class wceq fdvelimALT_2 wal wn wa edvelimALT_0 a1i hbimd ex pm2.61i hbald fdvelimALT_0 fdvelimALT_1 fdvelimALT_4 fdvelimALT_3 fdvelimALT_1 fdvelimALT_4 ax-17 edvelimALT_1 equsalh fdvelimALT_4 sup_set_class fdvelimALT_3 sup_set_class wceq fdvelimALT_0 wi fdvelimALT_4 wal fdvelimALT_1 fdvelimALT_2 fdvelimALT_0 fdvelimALT_1 fdvelimALT_4 fdvelimALT_3 fdvelimALT_1 fdvelimALT_4 ax-17 edvelimALT_1 equsalh albii 3imtr3g $.
$}
$( Move quantifier in and out of substitution.  (Contributed by NM,
       2-Jan-2002.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$d z y $.
	$d z x $.
	fsbal2_0 $f wff ph $.
	fsbal2_1 $f set x $.
	fsbal2_2 $f set y $.
	fsbal2_3 $f set z $.
	sbal2 $p |- ( -. A. x x = y -> ( [ z / y ] A. x ph <-> A. x [ z / y ] ph ) ) $= fsbal2_1 sup_set_class fsbal2_2 sup_set_class wceq fsbal2_1 wal wn fsbal2_2 sup_set_class fsbal2_3 sup_set_class wceq fsbal2_0 fsbal2_1 wal wi fsbal2_2 wal fsbal2_2 sup_set_class fsbal2_3 sup_set_class wceq fsbal2_0 wi fsbal2_2 wal fsbal2_1 wal fsbal2_0 fsbal2_1 wal fsbal2_2 fsbal2_3 wsb fsbal2_0 fsbal2_2 fsbal2_3 wsb fsbal2_1 wal fsbal2_2 sup_set_class fsbal2_3 sup_set_class wceq fsbal2_0 wi fsbal2_2 wal fsbal2_1 wal fsbal2_2 sup_set_class fsbal2_3 sup_set_class wceq fsbal2_0 wi fsbal2_1 wal fsbal2_2 wal fsbal2_1 sup_set_class fsbal2_2 sup_set_class wceq fsbal2_1 wal wn fsbal2_2 sup_set_class fsbal2_3 sup_set_class wceq fsbal2_0 fsbal2_1 wal wi fsbal2_2 wal fsbal2_2 sup_set_class fsbal2_3 sup_set_class wceq fsbal2_0 wi fsbal2_2 fsbal2_1 alcom fsbal2_1 sup_set_class fsbal2_2 sup_set_class wceq fsbal2_1 wal wn fsbal2_2 sup_set_class fsbal2_3 sup_set_class wceq fsbal2_0 wi fsbal2_1 wal fsbal2_2 sup_set_class fsbal2_3 sup_set_class wceq fsbal2_0 fsbal2_1 wal wi fsbal2_2 fsbal2_1 fsbal2_2 fsbal2_2 nfnae fsbal2_1 sup_set_class fsbal2_2 sup_set_class wceq fsbal2_1 wal wn fsbal2_2 sup_set_class fsbal2_3 sup_set_class wceq fsbal2_1 wnf fsbal2_2 sup_set_class fsbal2_3 sup_set_class wceq fsbal2_0 wi fsbal2_1 wal fsbal2_2 sup_set_class fsbal2_3 sup_set_class wceq fsbal2_0 fsbal2_1 wal wi wb fsbal2_1 sup_set_class fsbal2_2 sup_set_class wceq fsbal2_1 wal wn fsbal2_2 sup_set_class fsbal2_3 sup_set_class wceq fsbal2_1 fsbal2_1 fsbal2_2 fsbal2_1 nfnae fsbal2_1 fsbal2_2 fsbal2_3 dveeq1 nfd fsbal2_2 sup_set_class fsbal2_3 sup_set_class wceq fsbal2_0 fsbal2_1 19.21t syl albid syl5rbbr fsbal2_0 fsbal2_1 wal fsbal2_2 fsbal2_3 sb6 fsbal2_0 fsbal2_2 fsbal2_3 wsb fsbal2_2 sup_set_class fsbal2_3 sup_set_class wceq fsbal2_0 wi fsbal2_2 wal fsbal2_1 fsbal2_0 fsbal2_2 fsbal2_3 sb6 albii 3bitr4g $.
$}

