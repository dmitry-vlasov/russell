$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/The_intersection_of_a_class.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Indexed union and intersection

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$c U_  $.
$( Underlined big cup. $)
$c |^|_  $.
$( Underlined big cap. $)
$( Extend class notation to include indexed union.  Note:  Historically
     (prior to 21-Oct-2005), set.mm used the notation ` U. x e. A B ` , with
     the same union symbol as ~ cuni .  While that syntax was unambiguous, it
     did not allow for LALR parsing of the syntax constructions in set.mm.  The
     new syntax uses as distinguished symbol ` U_ ` instead of ` U. ` and does
     allow LALR parsing.  Thanks to Peter Backes for suggesting this change. $)
${
	$v x $.
	$v A $.
	$v B $.
	fciun_0 $f set x $.
	fciun_1 $f class A $.
	fciun_2 $f class B $.
	ciun $a class U_ x e. A B $.
$}
$( Extend class notation to include indexed intersection.  Note:
     Historically (prior to 21-Oct-2005), set.mm used the notation
     ` |^| x e. A B ` , with the same intersection symbol as ~ cint .  Although
     that syntax was unambiguous, it did not allow for LALR parsing of the
     syntax constructions in set.mm.  The new syntax uses a distinguished
     symbol ` |^|_ ` instead of ` |^| ` and does allow LALR parsing.  Thanks to
     Peter Backes for suggesting this change. $)
${
	$v x $.
	$v A $.
	$v B $.
	fciin_0 $f set x $.
	fciin_1 $f class A $.
	fciin_2 $f class B $.
	ciin $a class |^|_ x e. A B $.
$}
$( Define indexed union.  Definition indexed union in [Stoll] p. 45.  In
       most applications, ` A ` is independent of ` x ` (although this is not
       required by the definition), and ` B ` depends on ` x ` i.e. can be read
       informally as ` B ( x ) ` .  We call ` x ` the index, ` A ` the index
       set, and ` B ` the indexed set.  In most books, ` x e. A ` is written as
       a subscript or underneath a union symbol ` U. ` .  We use a special
       union symbol ` U_ ` to make it easier to distinguish from plain class
       union.  In many theorems, you will see that ` x ` and ` A ` are in the
       same distinct variable group (meaning ` A ` cannot depend on ` x ` ) and
       that ` B ` and ` x ` do not share a distinct variable group (meaning
       that can be thought of as ` B ( x ) ` i.e. can be substituted with a
       class expression containing ` x ` ).  An alternate definition tying
       indexed union to ordinary union is ~ dfiun2 .  Theorem ~ uniiun provides
       a definition of ordinary union in terms of indexed union.  Theorems
       ~ fniunfv and ~ funiunfv are useful when ` B ` is a function.
       (Contributed by NM, 27-Jun-1998.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$d x y $.
	$d y A $.
	$d y B $.
	fdf-iun_0 $f set x $.
	fdf-iun_1 $f set y $.
	fdf-iun_2 $f class A $.
	fdf-iun_3 $f class B $.
	df-iun $a |- U_ x e. A B = { y | E. x e. A y e. B } $.
$}
$( Define indexed intersection.  Definition of [Stoll] p. 45.  See the
       remarks for its sibling operation of indexed union ~ df-iun .  An
       alternate definition tying indexed intersection to ordinary intersection
       is ~ dfiin2 .  Theorem ~ intiin provides a definition of ordinary
       intersection in terms of indexed intersection.  (Contributed by NM,
       27-Jun-1998.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$d x y $.
	$d y A $.
	$d y B $.
	fdf-iin_0 $f set x $.
	fdf-iin_1 $f set y $.
	fdf-iin_2 $f class A $.
	fdf-iin_3 $f class B $.
	df-iin $a |- |^|_ x e. A B = { y | A. x e. A y e. B } $.
$}
$( Membership in indexed union.  (Contributed by NM, 3-Sep-2003.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$d x y A $.
	$d y B $.
	$d y C $.
	ieliun_0 $f set y $.
	feliun_0 $f set x $.
	feliun_1 $f class A $.
	feliun_2 $f class B $.
	feliun_3 $f class C $.
	eliun $p |- ( A e. U_ x e. B C <-> E. x e. B A e. C ) $= feliun_1 feliun_0 feliun_2 feliun_3 ciun wcel feliun_1 cvv wcel feliun_1 feliun_3 wcel feliun_0 feliun_2 wrex feliun_1 feliun_0 feliun_2 feliun_3 ciun elex feliun_1 feliun_3 wcel feliun_1 cvv wcel feliun_0 feliun_2 feliun_1 feliun_3 elex rexlimivw ieliun_0 cv feliun_3 wcel feliun_0 feliun_2 wrex feliun_1 feliun_3 wcel feliun_0 feliun_2 wrex ieliun_0 feliun_1 feliun_0 feliun_2 feliun_3 ciun cvv ieliun_0 cv feliun_1 wceq ieliun_0 cv feliun_3 wcel feliun_1 feliun_3 wcel feliun_0 feliun_2 ieliun_0 cv feliun_1 feliun_3 eleq1 rexbidv feliun_0 ieliun_0 feliun_2 feliun_3 df-iun elab2g pm5.21nii $.
$}
$( Membership in indexed intersection.  (Contributed by NM, 3-Sep-2003.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$v V $.
	$d x y A $.
	$d y B $.
	$d y C $.
	ieliin_0 $f set y $.
	feliin_0 $f set x $.
	feliin_1 $f class A $.
	feliin_2 $f class B $.
	feliin_3 $f class C $.
	feliin_4 $f class V $.
	eliin $p |- ( A e. V -> ( A e. |^|_ x e. B C <-> A. x e. B A e. C ) ) $= ieliin_0 cv feliin_3 wcel feliin_0 feliin_2 wral feliin_1 feliin_3 wcel feliin_0 feliin_2 wral ieliin_0 feliin_1 feliin_0 feliin_2 feliin_3 ciin feliin_4 ieliin_0 cv feliin_1 wceq ieliin_0 cv feliin_3 wcel feliin_1 feliin_3 wcel feliin_0 feliin_2 ieliin_0 cv feliin_1 feliin_3 eleq1 ralbidv feliin_0 ieliin_0 feliin_2 feliin_3 df-iin elab2g $.
$}
$( Commutation of indexed unions.  (Contributed by NM, 18-Dec-2008.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v A $.
	$v B $.
	$v C $.
	$d y z A $.
	$d x z B $.
	$d z C $.
	$d x y $.
	iiuncom_0 $f set z $.
	fiuncom_0 $f set x $.
	fiuncom_1 $f set y $.
	fiuncom_2 $f class A $.
	fiuncom_3 $f class B $.
	fiuncom_4 $f class C $.
	iuncom $p |- U_ x e. A U_ y e. B C = U_ y e. B U_ x e. A C $= iiuncom_0 fiuncom_0 fiuncom_2 fiuncom_1 fiuncom_3 fiuncom_4 ciun ciun fiuncom_1 fiuncom_3 fiuncom_0 fiuncom_2 fiuncom_4 ciun ciun iiuncom_0 cv fiuncom_1 fiuncom_3 fiuncom_4 ciun wcel fiuncom_0 fiuncom_2 wrex iiuncom_0 cv fiuncom_0 fiuncom_2 fiuncom_4 ciun wcel fiuncom_1 fiuncom_3 wrex iiuncom_0 cv fiuncom_0 fiuncom_2 fiuncom_1 fiuncom_3 fiuncom_4 ciun ciun wcel iiuncom_0 cv fiuncom_1 fiuncom_3 fiuncom_0 fiuncom_2 fiuncom_4 ciun ciun wcel iiuncom_0 cv fiuncom_4 wcel fiuncom_1 fiuncom_3 wrex fiuncom_0 fiuncom_2 wrex iiuncom_0 cv fiuncom_4 wcel fiuncom_0 fiuncom_2 wrex fiuncom_1 fiuncom_3 wrex iiuncom_0 cv fiuncom_1 fiuncom_3 fiuncom_4 ciun wcel fiuncom_0 fiuncom_2 wrex iiuncom_0 cv fiuncom_0 fiuncom_2 fiuncom_4 ciun wcel fiuncom_1 fiuncom_3 wrex iiuncom_0 cv fiuncom_4 wcel fiuncom_0 fiuncom_1 fiuncom_2 fiuncom_3 rexcom iiuncom_0 cv fiuncom_1 fiuncom_3 fiuncom_4 ciun wcel iiuncom_0 cv fiuncom_4 wcel fiuncom_1 fiuncom_3 wrex fiuncom_0 fiuncom_2 fiuncom_1 iiuncom_0 cv fiuncom_3 fiuncom_4 eliun rexbii iiuncom_0 cv fiuncom_0 fiuncom_2 fiuncom_4 ciun wcel iiuncom_0 cv fiuncom_4 wcel fiuncom_0 fiuncom_2 wrex fiuncom_1 fiuncom_3 fiuncom_0 iiuncom_0 cv fiuncom_2 fiuncom_4 eliun rexbii 3bitr4i fiuncom_0 iiuncom_0 cv fiuncom_2 fiuncom_1 fiuncom_3 fiuncom_4 ciun eliun fiuncom_1 iiuncom_0 cv fiuncom_3 fiuncom_0 fiuncom_2 fiuncom_4 ciun eliun 3bitr4i eqriv $.
$}
$( Commutation of union with indexed union.  (Contributed by Mario
       Carneiro, 18-Jan-2014.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v A $.
	$v B $.
	$d y z A $.
	$d y z B $.
	$d x y z $.
	iiuncom4_0 $f set y $.
	iiuncom4_1 $f set z $.
	fiuncom4_0 $f set x $.
	fiuncom4_1 $f class A $.
	fiuncom4_2 $f class B $.
	iuncom4 $p |- U_ x e. A U. B = U. U_ x e. A B $= iiuncom4_0 fiuncom4_0 fiuncom4_1 fiuncom4_2 cuni ciun fiuncom4_0 fiuncom4_1 fiuncom4_2 ciun cuni iiuncom4_0 cv fiuncom4_2 cuni wcel fiuncom4_0 fiuncom4_1 wrex iiuncom4_0 cv iiuncom4_1 cv wcel iiuncom4_1 fiuncom4_0 fiuncom4_1 fiuncom4_2 ciun wrex iiuncom4_0 cv fiuncom4_0 fiuncom4_1 fiuncom4_2 cuni ciun wcel iiuncom4_0 cv fiuncom4_0 fiuncom4_1 fiuncom4_2 ciun cuni wcel iiuncom4_0 cv iiuncom4_1 cv wcel iiuncom4_1 fiuncom4_2 wrex fiuncom4_0 fiuncom4_1 wrex iiuncom4_1 cv fiuncom4_2 wcel fiuncom4_0 fiuncom4_1 wrex iiuncom4_0 cv iiuncom4_1 cv wcel wa iiuncom4_1 wex iiuncom4_0 cv fiuncom4_2 cuni wcel fiuncom4_0 fiuncom4_1 wrex iiuncom4_0 cv iiuncom4_1 cv wcel iiuncom4_1 fiuncom4_0 fiuncom4_1 fiuncom4_2 ciun wrex iiuncom4_0 cv iiuncom4_1 cv wcel iiuncom4_1 fiuncom4_2 wrex fiuncom4_0 fiuncom4_1 wrex iiuncom4_1 cv fiuncom4_2 wcel iiuncom4_0 cv iiuncom4_1 cv wcel wa fiuncom4_0 fiuncom4_1 wrex iiuncom4_1 wex iiuncom4_1 cv fiuncom4_2 wcel fiuncom4_0 fiuncom4_1 wrex iiuncom4_0 cv iiuncom4_1 cv wcel wa iiuncom4_1 wex iiuncom4_0 cv iiuncom4_1 cv wcel iiuncom4_1 fiuncom4_2 wrex fiuncom4_0 fiuncom4_1 wrex iiuncom4_1 cv fiuncom4_2 wcel iiuncom4_0 cv iiuncom4_1 cv wcel wa iiuncom4_1 wex fiuncom4_0 fiuncom4_1 wrex iiuncom4_1 cv fiuncom4_2 wcel iiuncom4_0 cv iiuncom4_1 cv wcel wa fiuncom4_0 fiuncom4_1 wrex iiuncom4_1 wex iiuncom4_0 cv iiuncom4_1 cv wcel iiuncom4_1 fiuncom4_2 wrex iiuncom4_1 cv fiuncom4_2 wcel iiuncom4_0 cv iiuncom4_1 cv wcel wa iiuncom4_1 wex fiuncom4_0 fiuncom4_1 iiuncom4_0 cv iiuncom4_1 cv wcel iiuncom4_1 fiuncom4_2 df-rex rexbii iiuncom4_1 cv fiuncom4_2 wcel iiuncom4_0 cv iiuncom4_1 cv wcel wa fiuncom4_0 iiuncom4_1 fiuncom4_1 rexcom4 bitri iiuncom4_1 cv fiuncom4_2 wcel iiuncom4_0 cv iiuncom4_1 cv wcel wa fiuncom4_0 fiuncom4_1 wrex iiuncom4_1 cv fiuncom4_2 wcel fiuncom4_0 fiuncom4_1 wrex iiuncom4_0 cv iiuncom4_1 cv wcel wa iiuncom4_1 iiuncom4_1 cv fiuncom4_2 wcel iiuncom4_0 cv iiuncom4_1 cv wcel fiuncom4_0 fiuncom4_1 r19.41v exbii bitri iiuncom4_0 cv fiuncom4_2 cuni wcel iiuncom4_0 cv iiuncom4_1 cv wcel iiuncom4_1 fiuncom4_2 wrex fiuncom4_0 fiuncom4_1 iiuncom4_1 iiuncom4_0 cv fiuncom4_2 eluni2 rexbii iiuncom4_0 cv iiuncom4_1 cv wcel iiuncom4_1 fiuncom4_0 fiuncom4_1 fiuncom4_2 ciun wrex iiuncom4_1 cv fiuncom4_0 fiuncom4_1 fiuncom4_2 ciun wcel iiuncom4_0 cv iiuncom4_1 cv wcel wa iiuncom4_1 wex iiuncom4_1 cv fiuncom4_2 wcel fiuncom4_0 fiuncom4_1 wrex iiuncom4_0 cv iiuncom4_1 cv wcel wa iiuncom4_1 wex iiuncom4_0 cv iiuncom4_1 cv wcel iiuncom4_1 fiuncom4_0 fiuncom4_1 fiuncom4_2 ciun df-rex iiuncom4_1 cv fiuncom4_0 fiuncom4_1 fiuncom4_2 ciun wcel iiuncom4_0 cv iiuncom4_1 cv wcel wa iiuncom4_1 cv fiuncom4_2 wcel fiuncom4_0 fiuncom4_1 wrex iiuncom4_0 cv iiuncom4_1 cv wcel wa iiuncom4_1 iiuncom4_1 cv fiuncom4_0 fiuncom4_1 fiuncom4_2 ciun wcel iiuncom4_1 cv fiuncom4_2 wcel fiuncom4_0 fiuncom4_1 wrex iiuncom4_0 cv iiuncom4_1 cv wcel fiuncom4_0 iiuncom4_1 cv fiuncom4_1 fiuncom4_2 eliun anbi1i exbii bitri 3bitr4i fiuncom4_0 iiuncom4_0 cv fiuncom4_1 fiuncom4_2 cuni eliun iiuncom4_1 iiuncom4_0 cv fiuncom4_0 fiuncom4_1 fiuncom4_2 ciun eluni2 3bitr4i eqriv $.
$}
$( Indexed union of a constant class, i.e. where ` B ` does not depend on
       ` x ` .  (Contributed by NM, 5-Sep-2004.)  (Proof shortened by Andrew
       Salmon, 25-Jul-2011.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$d x y A $.
	$d x y B $.
	iiunconst_0 $f set y $.
	fiunconst_0 $f set x $.
	fiunconst_1 $f class A $.
	fiunconst_2 $f class B $.
	iunconst $p |- ( A =/= (/) -> U_ x e. A B = B ) $= fiunconst_1 c0 wne iiunconst_0 fiunconst_0 fiunconst_1 fiunconst_2 ciun fiunconst_2 fiunconst_1 c0 wne iiunconst_0 cv fiunconst_2 wcel iiunconst_0 cv fiunconst_2 wcel fiunconst_0 fiunconst_1 wrex iiunconst_0 cv fiunconst_0 fiunconst_1 fiunconst_2 ciun wcel iiunconst_0 cv fiunconst_2 wcel fiunconst_0 fiunconst_1 r19.9rzv fiunconst_0 iiunconst_0 cv fiunconst_1 fiunconst_2 eliun syl6rbbr eqrdv $.
$}
$( Indexed intersection of a constant class, i.e. where ` B ` does not
       depend on ` x ` .  (Contributed by Mario Carneiro, 6-Feb-2015.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$d x y A $.
	$d x y B $.
	iiinconst_0 $f set y $.
	fiinconst_0 $f set x $.
	fiinconst_1 $f class A $.
	fiinconst_2 $f class B $.
	iinconst $p |- ( A =/= (/) -> |^|_ x e. A B = B ) $= fiinconst_1 c0 wne iiinconst_0 fiinconst_0 fiinconst_1 fiinconst_2 ciin fiinconst_2 fiinconst_1 c0 wne iiinconst_0 cv fiinconst_2 wcel iiinconst_0 cv fiinconst_2 wcel fiinconst_0 fiinconst_1 wral iiinconst_0 cv fiinconst_0 fiinconst_1 fiinconst_2 ciin wcel iiinconst_0 cv fiinconst_2 wcel fiinconst_0 fiinconst_1 r19.3rzv iiinconst_0 cv cvv wcel iiinconst_0 cv fiinconst_0 fiinconst_1 fiinconst_2 ciin wcel iiinconst_0 cv fiinconst_2 wcel fiinconst_0 fiinconst_1 wral wb iiinconst_0 vex fiinconst_0 iiinconst_0 cv fiinconst_1 fiinconst_2 cvv eliin ax-mp syl6rbbr eqrdv $.
$}
$( Law combining indexed union with indexed intersection.  Eq. 14 in
       [KuratowskiMostowski] p. 109.  This theorem also appears as the last
       example at ~ http://en.wikipedia.org/wiki/Union%5F%28set%5Ftheory%29 .
       (Contributed by NM, 17-Aug-2004.)  (Proof shortened by Andrew Salmon,
       25-Jul-2011.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v A $.
	$v B $.
	$v C $.
	$d x y $.
	$d y z A $.
	$d x z B $.
	$d z C $.
	iiuniin_0 $f set z $.
	fiuniin_0 $f set x $.
	fiuniin_1 $f set y $.
	fiuniin_2 $f class A $.
	fiuniin_3 $f class B $.
	fiuniin_4 $f class C $.
	iuniin $p |- U_ x e. A |^|_ y e. B C C_ |^|_ y e. B U_ x e. A C $= iiuniin_0 fiuniin_0 fiuniin_2 fiuniin_1 fiuniin_3 fiuniin_4 ciin ciun fiuniin_1 fiuniin_3 fiuniin_0 fiuniin_2 fiuniin_4 ciun ciin iiuniin_0 cv fiuniin_1 fiuniin_3 fiuniin_4 ciin wcel fiuniin_0 fiuniin_2 wrex iiuniin_0 cv fiuniin_0 fiuniin_2 fiuniin_4 ciun wcel fiuniin_1 fiuniin_3 wral iiuniin_0 cv fiuniin_0 fiuniin_2 fiuniin_1 fiuniin_3 fiuniin_4 ciin ciun wcel iiuniin_0 cv fiuniin_1 fiuniin_3 fiuniin_0 fiuniin_2 fiuniin_4 ciun ciin wcel iiuniin_0 cv fiuniin_4 wcel fiuniin_1 fiuniin_3 wral fiuniin_0 fiuniin_2 wrex iiuniin_0 cv fiuniin_4 wcel fiuniin_0 fiuniin_2 wrex fiuniin_1 fiuniin_3 wral iiuniin_0 cv fiuniin_1 fiuniin_3 fiuniin_4 ciin wcel fiuniin_0 fiuniin_2 wrex iiuniin_0 cv fiuniin_0 fiuniin_2 fiuniin_4 ciun wcel fiuniin_1 fiuniin_3 wral iiuniin_0 cv fiuniin_4 wcel fiuniin_0 fiuniin_1 fiuniin_2 fiuniin_3 r19.12 iiuniin_0 cv fiuniin_1 fiuniin_3 fiuniin_4 ciin wcel iiuniin_0 cv fiuniin_4 wcel fiuniin_1 fiuniin_3 wral fiuniin_0 fiuniin_2 iiuniin_0 cv cvv wcel iiuniin_0 cv fiuniin_1 fiuniin_3 fiuniin_4 ciin wcel iiuniin_0 cv fiuniin_4 wcel fiuniin_1 fiuniin_3 wral wb iiuniin_0 vex fiuniin_1 iiuniin_0 cv fiuniin_3 fiuniin_4 cvv eliin ax-mp rexbii iiuniin_0 cv fiuniin_0 fiuniin_2 fiuniin_4 ciun wcel iiuniin_0 cv fiuniin_4 wcel fiuniin_0 fiuniin_2 wrex fiuniin_1 fiuniin_3 fiuniin_0 iiuniin_0 cv fiuniin_2 fiuniin_4 eliun ralbii 3imtr4i fiuniin_0 iiuniin_0 cv fiuniin_2 fiuniin_1 fiuniin_3 fiuniin_4 ciin eliun iiuniin_0 cv cvv wcel iiuniin_0 cv fiuniin_1 fiuniin_3 fiuniin_0 fiuniin_2 fiuniin_4 ciun ciin wcel iiuniin_0 cv fiuniin_0 fiuniin_2 fiuniin_4 ciun wcel fiuniin_1 fiuniin_3 wral wb iiuniin_0 vex fiuniin_1 iiuniin_0 cv fiuniin_3 fiuniin_0 fiuniin_2 fiuniin_4 ciun cvv eliin ax-mp 3imtr4i ssriv $.
$}
$( Subclass theorem for indexed union.  (Contributed by NM, 10-Dec-2004.)
       (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$d x y A $.
	$d x y B $.
	$d y C $.
	iiunss1_0 $f set y $.
	fiunss1_0 $f set x $.
	fiunss1_1 $f class A $.
	fiunss1_2 $f class B $.
	fiunss1_3 $f class C $.
	iunss1 $p |- ( A C_ B -> U_ x e. A C C_ U_ x e. B C ) $= fiunss1_1 fiunss1_2 wss iiunss1_0 fiunss1_0 fiunss1_1 fiunss1_3 ciun fiunss1_0 fiunss1_2 fiunss1_3 ciun fiunss1_1 fiunss1_2 wss iiunss1_0 cv fiunss1_3 wcel fiunss1_0 fiunss1_1 wrex iiunss1_0 cv fiunss1_3 wcel fiunss1_0 fiunss1_2 wrex iiunss1_0 cv fiunss1_0 fiunss1_1 fiunss1_3 ciun wcel iiunss1_0 cv fiunss1_0 fiunss1_2 fiunss1_3 ciun wcel iiunss1_0 cv fiunss1_3 wcel fiunss1_0 fiunss1_1 fiunss1_2 ssrexv fiunss1_0 iiunss1_0 cv fiunss1_1 fiunss1_3 eliun fiunss1_0 iiunss1_0 cv fiunss1_2 fiunss1_3 eliun 3imtr4g ssrdv $.
$}
$( Subclass theorem for indexed union.  (Contributed by NM,
       24-Jan-2012.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$d x y A $.
	$d x y B $.
	$d y C $.
	iiinss1_0 $f set y $.
	fiinss1_0 $f set x $.
	fiinss1_1 $f class A $.
	fiinss1_2 $f class B $.
	fiinss1_3 $f class C $.
	iinss1 $p |- ( A C_ B -> |^|_ x e. B C C_ |^|_ x e. A C ) $= fiinss1_1 fiinss1_2 wss iiinss1_0 fiinss1_0 fiinss1_2 fiinss1_3 ciin fiinss1_0 fiinss1_1 fiinss1_3 ciin fiinss1_1 fiinss1_2 wss iiinss1_0 cv fiinss1_3 wcel fiinss1_0 fiinss1_2 wral iiinss1_0 cv fiinss1_3 wcel fiinss1_0 fiinss1_1 wral iiinss1_0 cv fiinss1_0 fiinss1_2 fiinss1_3 ciin wcel iiinss1_0 cv fiinss1_0 fiinss1_1 fiinss1_3 ciin wcel iiinss1_0 cv fiinss1_3 wcel fiinss1_0 fiinss1_1 fiinss1_2 ssralv iiinss1_0 cv cvv wcel iiinss1_0 cv fiinss1_0 fiinss1_2 fiinss1_3 ciin wcel iiinss1_0 cv fiinss1_3 wcel fiinss1_0 fiinss1_2 wral wb iiinss1_0 vex fiinss1_0 iiinss1_0 cv fiinss1_2 fiinss1_3 cvv eliin ax-mp iiinss1_0 cv cvv wcel iiinss1_0 cv fiinss1_0 fiinss1_1 fiinss1_3 ciin wcel iiinss1_0 cv fiinss1_3 wcel fiinss1_0 fiinss1_1 wral wb iiinss1_0 vex fiinss1_0 iiinss1_0 cv fiinss1_1 fiinss1_3 cvv eliin ax-mp 3imtr4g ssrdv $.
$}
$( Equality theorem for indexed union.  (Contributed by NM,
       27-Jun-1998.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$d x A $.
	$d x B $.
	fiuneq1_0 $f set x $.
	fiuneq1_1 $f class A $.
	fiuneq1_2 $f class B $.
	fiuneq1_3 $f class C $.
	iuneq1 $p |- ( A = B -> U_ x e. A C = U_ x e. B C ) $= fiuneq1_1 fiuneq1_2 wss fiuneq1_2 fiuneq1_1 wss wa fiuneq1_0 fiuneq1_1 fiuneq1_3 ciun fiuneq1_0 fiuneq1_2 fiuneq1_3 ciun wss fiuneq1_0 fiuneq1_2 fiuneq1_3 ciun fiuneq1_0 fiuneq1_1 fiuneq1_3 ciun wss wa fiuneq1_1 fiuneq1_2 wceq fiuneq1_0 fiuneq1_1 fiuneq1_3 ciun fiuneq1_0 fiuneq1_2 fiuneq1_3 ciun wceq fiuneq1_1 fiuneq1_2 wss fiuneq1_0 fiuneq1_1 fiuneq1_3 ciun fiuneq1_0 fiuneq1_2 fiuneq1_3 ciun wss fiuneq1_2 fiuneq1_1 wss fiuneq1_0 fiuneq1_2 fiuneq1_3 ciun fiuneq1_0 fiuneq1_1 fiuneq1_3 ciun wss fiuneq1_0 fiuneq1_1 fiuneq1_2 fiuneq1_3 iunss1 fiuneq1_0 fiuneq1_2 fiuneq1_1 fiuneq1_3 iunss1 anim12i fiuneq1_1 fiuneq1_2 eqss fiuneq1_0 fiuneq1_1 fiuneq1_3 ciun fiuneq1_0 fiuneq1_2 fiuneq1_3 ciun eqss 3imtr4i $.
$}
$( Equality theorem for restricted existential quantifier.  (Contributed by
       NM, 27-Jun-1998.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$d x y A $.
	$d x y B $.
	$d y C $.
	iiineq1_0 $f set y $.
	fiineq1_0 $f set x $.
	fiineq1_1 $f class A $.
	fiineq1_2 $f class B $.
	fiineq1_3 $f class C $.
	iineq1 $p |- ( A = B -> |^|_ x e. A C = |^|_ x e. B C ) $= fiineq1_1 fiineq1_2 wceq iiineq1_0 cv fiineq1_3 wcel fiineq1_0 fiineq1_1 wral iiineq1_0 cab iiineq1_0 cv fiineq1_3 wcel fiineq1_0 fiineq1_2 wral iiineq1_0 cab fiineq1_0 fiineq1_1 fiineq1_3 ciin fiineq1_0 fiineq1_2 fiineq1_3 ciin fiineq1_1 fiineq1_2 wceq iiineq1_0 cv fiineq1_3 wcel fiineq1_0 fiineq1_1 wral iiineq1_0 cv fiineq1_3 wcel fiineq1_0 fiineq1_2 wral iiineq1_0 iiineq1_0 cv fiineq1_3 wcel fiineq1_0 fiineq1_1 fiineq1_2 raleq abbidv fiineq1_0 iiineq1_0 fiineq1_1 fiineq1_3 df-iin fiineq1_0 iiineq1_0 fiineq1_2 fiineq1_3 df-iin 3eqtr4g $.
$}
$( Subclass theorem for indexed union.  (Contributed by NM, 26-Nov-2003.)
       (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$d x y $.
	$d y A $.
	$d y B $.
	$d y C $.
	iss2iun_0 $f set y $.
	fss2iun_0 $f set x $.
	fss2iun_1 $f class A $.
	fss2iun_2 $f class B $.
	fss2iun_3 $f class C $.
	ss2iun $p |- ( A. x e. A B C_ C -> U_ x e. A B C_ U_ x e. A C ) $= fss2iun_2 fss2iun_3 wss fss2iun_0 fss2iun_1 wral iss2iun_0 fss2iun_0 fss2iun_1 fss2iun_2 ciun fss2iun_0 fss2iun_1 fss2iun_3 ciun fss2iun_2 fss2iun_3 wss fss2iun_0 fss2iun_1 wral iss2iun_0 cv fss2iun_2 wcel fss2iun_0 fss2iun_1 wrex iss2iun_0 cv fss2iun_3 wcel fss2iun_0 fss2iun_1 wrex iss2iun_0 cv fss2iun_0 fss2iun_1 fss2iun_2 ciun wcel iss2iun_0 cv fss2iun_0 fss2iun_1 fss2iun_3 ciun wcel fss2iun_2 fss2iun_3 wss fss2iun_0 fss2iun_1 wral iss2iun_0 cv fss2iun_2 wcel iss2iun_0 cv fss2iun_3 wcel wi fss2iun_0 fss2iun_1 wral iss2iun_0 cv fss2iun_2 wcel fss2iun_0 fss2iun_1 wrex iss2iun_0 cv fss2iun_3 wcel fss2iun_0 fss2iun_1 wrex wi fss2iun_2 fss2iun_3 wss iss2iun_0 cv fss2iun_2 wcel iss2iun_0 cv fss2iun_3 wcel wi fss2iun_0 fss2iun_1 fss2iun_2 fss2iun_3 iss2iun_0 cv ssel ralimi iss2iun_0 cv fss2iun_2 wcel iss2iun_0 cv fss2iun_3 wcel fss2iun_0 fss2iun_1 rexim syl fss2iun_0 iss2iun_0 cv fss2iun_1 fss2iun_2 eliun fss2iun_0 iss2iun_0 cv fss2iun_1 fss2iun_3 eliun 3imtr4g ssrdv $.
$}
$( Equality theorem for indexed union.  (Contributed by NM,
       22-Oct-2003.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	fiuneq2_0 $f set x $.
	fiuneq2_1 $f class A $.
	fiuneq2_2 $f class B $.
	fiuneq2_3 $f class C $.
	iuneq2 $p |- ( A. x e. A B = C -> U_ x e. A B = U_ x e. A C ) $= fiuneq2_2 fiuneq2_3 wss fiuneq2_0 fiuneq2_1 wral fiuneq2_3 fiuneq2_2 wss fiuneq2_0 fiuneq2_1 wral wa fiuneq2_0 fiuneq2_1 fiuneq2_2 ciun fiuneq2_0 fiuneq2_1 fiuneq2_3 ciun wss fiuneq2_0 fiuneq2_1 fiuneq2_3 ciun fiuneq2_0 fiuneq2_1 fiuneq2_2 ciun wss wa fiuneq2_2 fiuneq2_3 wceq fiuneq2_0 fiuneq2_1 wral fiuneq2_0 fiuneq2_1 fiuneq2_2 ciun fiuneq2_0 fiuneq2_1 fiuneq2_3 ciun wceq fiuneq2_2 fiuneq2_3 wss fiuneq2_0 fiuneq2_1 wral fiuneq2_0 fiuneq2_1 fiuneq2_2 ciun fiuneq2_0 fiuneq2_1 fiuneq2_3 ciun wss fiuneq2_3 fiuneq2_2 wss fiuneq2_0 fiuneq2_1 wral fiuneq2_0 fiuneq2_1 fiuneq2_3 ciun fiuneq2_0 fiuneq2_1 fiuneq2_2 ciun wss fiuneq2_0 fiuneq2_1 fiuneq2_2 fiuneq2_3 ss2iun fiuneq2_0 fiuneq2_1 fiuneq2_3 fiuneq2_2 ss2iun anim12i fiuneq2_2 fiuneq2_3 wceq fiuneq2_0 fiuneq2_1 wral fiuneq2_2 fiuneq2_3 wss fiuneq2_3 fiuneq2_2 wss wa fiuneq2_0 fiuneq2_1 wral fiuneq2_2 fiuneq2_3 wss fiuneq2_0 fiuneq2_1 wral fiuneq2_3 fiuneq2_2 wss fiuneq2_0 fiuneq2_1 wral wa fiuneq2_2 fiuneq2_3 wceq fiuneq2_2 fiuneq2_3 wss fiuneq2_3 fiuneq2_2 wss wa fiuneq2_0 fiuneq2_1 fiuneq2_2 fiuneq2_3 eqss ralbii fiuneq2_2 fiuneq2_3 wss fiuneq2_3 fiuneq2_2 wss fiuneq2_0 fiuneq2_1 r19.26 bitri fiuneq2_0 fiuneq2_1 fiuneq2_2 ciun fiuneq2_0 fiuneq2_1 fiuneq2_3 ciun eqss 3imtr4i $.
$}
$( Equality theorem for indexed intersection.  (Contributed by NM,
       22-Oct-2003.)  (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$d x y $.
	$d y A $.
	$d y B $.
	$d y C $.
	iiineq2_0 $f set y $.
	fiineq2_0 $f set x $.
	fiineq2_1 $f class A $.
	fiineq2_2 $f class B $.
	fiineq2_3 $f class C $.
	iineq2 $p |- ( A. x e. A B = C -> |^|_ x e. A B = |^|_ x e. A C ) $= fiineq2_2 fiineq2_3 wceq fiineq2_0 fiineq2_1 wral iiineq2_0 cv fiineq2_2 wcel fiineq2_0 fiineq2_1 wral iiineq2_0 cab iiineq2_0 cv fiineq2_3 wcel fiineq2_0 fiineq2_1 wral iiineq2_0 cab fiineq2_0 fiineq2_1 fiineq2_2 ciin fiineq2_0 fiineq2_1 fiineq2_3 ciin fiineq2_2 fiineq2_3 wceq fiineq2_0 fiineq2_1 wral iiineq2_0 cv fiineq2_2 wcel fiineq2_0 fiineq2_1 wral iiineq2_0 cv fiineq2_3 wcel fiineq2_0 fiineq2_1 wral iiineq2_0 fiineq2_2 fiineq2_3 wceq fiineq2_0 fiineq2_1 wral iiineq2_0 cv fiineq2_2 wcel iiineq2_0 cv fiineq2_3 wcel wb fiineq2_0 fiineq2_1 wral iiineq2_0 cv fiineq2_2 wcel fiineq2_0 fiineq2_1 wral iiineq2_0 cv fiineq2_3 wcel fiineq2_0 fiineq2_1 wral wb fiineq2_2 fiineq2_3 wceq iiineq2_0 cv fiineq2_2 wcel iiineq2_0 cv fiineq2_3 wcel wb fiineq2_0 fiineq2_1 fiineq2_2 fiineq2_3 iiineq2_0 cv eleq2 ralimi iiineq2_0 cv fiineq2_2 wcel iiineq2_0 cv fiineq2_3 wcel fiineq2_0 fiineq2_1 ralbi syl abbidv fiineq2_0 iiineq2_0 fiineq2_1 fiineq2_2 df-iin fiineq2_0 iiineq2_0 fiineq2_1 fiineq2_3 df-iin 3eqtr4g $.
$}
$( Equality inference for indexed union.  (Contributed by NM,
       22-Oct-2003.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	fiuneq2i_0 $f set x $.
	fiuneq2i_1 $f class A $.
	fiuneq2i_2 $f class B $.
	fiuneq2i_3 $f class C $.
	eiuneq2i_0 $e |- ( x e. A -> B = C ) $.
	iuneq2i $p |- U_ x e. A B = U_ x e. A C $= fiuneq2i_2 fiuneq2i_3 wceq fiuneq2i_0 fiuneq2i_1 fiuneq2i_2 ciun fiuneq2i_0 fiuneq2i_1 fiuneq2i_3 ciun wceq fiuneq2i_0 fiuneq2i_1 fiuneq2i_0 fiuneq2i_1 fiuneq2i_2 fiuneq2i_3 iuneq2 eiuneq2i_0 mprg $.
$}
$( Equality inference for indexed intersection.  (Contributed by NM,
       22-Oct-2003.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	fiineq2i_0 $f set x $.
	fiineq2i_1 $f class A $.
	fiineq2i_2 $f class B $.
	fiineq2i_3 $f class C $.
	eiineq2i_0 $e |- ( x e. A -> B = C ) $.
	iineq2i $p |- |^|_ x e. A B = |^|_ x e. A C $= fiineq2i_2 fiineq2i_3 wceq fiineq2i_0 fiineq2i_1 fiineq2i_2 ciin fiineq2i_0 fiineq2i_1 fiineq2i_3 ciin wceq fiineq2i_0 fiineq2i_1 fiineq2i_0 fiineq2i_1 fiineq2i_2 fiineq2i_3 iineq2 eiineq2i_0 mprg $.
$}
$( Equality deduction for indexed intersection.  (Contributed by NM,
       7-Dec-2011.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	fiineq2d_0 $f wff ph $.
	fiineq2d_1 $f set x $.
	fiineq2d_2 $f class A $.
	fiineq2d_3 $f class B $.
	fiineq2d_4 $f class C $.
	eiineq2d_0 $e |- F/ x ph $.
	eiineq2d_1 $e |- ( ( ph /\ x e. A ) -> B = C ) $.
	iineq2d $p |- ( ph -> |^|_ x e. A B = |^|_ x e. A C ) $= fiineq2d_0 fiineq2d_3 fiineq2d_4 wceq fiineq2d_1 fiineq2d_2 wral fiineq2d_1 fiineq2d_2 fiineq2d_3 ciin fiineq2d_1 fiineq2d_2 fiineq2d_4 ciin wceq fiineq2d_0 fiineq2d_3 fiineq2d_4 wceq fiineq2d_1 fiineq2d_2 eiineq2d_0 fiineq2d_0 fiineq2d_1 cv fiineq2d_2 wcel fiineq2d_3 fiineq2d_4 wceq eiineq2d_1 ex ralrimi fiineq2d_1 fiineq2d_2 fiineq2d_3 fiineq2d_4 iineq2 syl $.
$}
$( Equality deduction for indexed union.  (Contributed by NM,
       3-Aug-2004.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$d x ph $.
	fiuneq2dv_0 $f wff ph $.
	fiuneq2dv_1 $f set x $.
	fiuneq2dv_2 $f class A $.
	fiuneq2dv_3 $f class B $.
	fiuneq2dv_4 $f class C $.
	eiuneq2dv_0 $e |- ( ( ph /\ x e. A ) -> B = C ) $.
	iuneq2dv $p |- ( ph -> U_ x e. A B = U_ x e. A C ) $= fiuneq2dv_0 fiuneq2dv_3 fiuneq2dv_4 wceq fiuneq2dv_1 fiuneq2dv_2 wral fiuneq2dv_1 fiuneq2dv_2 fiuneq2dv_3 ciun fiuneq2dv_1 fiuneq2dv_2 fiuneq2dv_4 ciun wceq fiuneq2dv_0 fiuneq2dv_3 fiuneq2dv_4 wceq fiuneq2dv_1 fiuneq2dv_2 eiuneq2dv_0 ralrimiva fiuneq2dv_1 fiuneq2dv_2 fiuneq2dv_3 fiuneq2dv_4 iuneq2 syl $.
$}
$( Equality deduction for indexed intersection.  (Contributed by NM,
       3-Aug-2004.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$d x ph $.
	fiineq2dv_0 $f wff ph $.
	fiineq2dv_1 $f set x $.
	fiineq2dv_2 $f class A $.
	fiineq2dv_3 $f class B $.
	fiineq2dv_4 $f class C $.
	eiineq2dv_0 $e |- ( ( ph /\ x e. A ) -> B = C ) $.
	iineq2dv $p |- ( ph -> |^|_ x e. A B = |^|_ x e. A C ) $= fiineq2dv_0 fiineq2dv_1 fiineq2dv_2 fiineq2dv_3 fiineq2dv_4 fiineq2dv_0 fiineq2dv_1 nfv eiineq2dv_0 iineq2d $.
$}
$( Equality theorem for indexed union, deduction version.  (Contributed by
       Drahflow, 22-Oct-2015.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$d x A $.
	$d x B $.
	fiuneq1d_0 $f wff ph $.
	fiuneq1d_1 $f set x $.
	fiuneq1d_2 $f class A $.
	fiuneq1d_3 $f class B $.
	fiuneq1d_4 $f class C $.
	eiuneq1d_0 $e |- ( ph -> A = B ) $.
	iuneq1d $p |- ( ph -> U_ x e. A C = U_ x e. B C ) $= fiuneq1d_0 fiuneq1d_2 fiuneq1d_3 wceq fiuneq1d_1 fiuneq1d_2 fiuneq1d_4 ciun fiuneq1d_1 fiuneq1d_3 fiuneq1d_4 ciun wceq eiuneq1d_0 fiuneq1d_1 fiuneq1d_2 fiuneq1d_3 fiuneq1d_4 iuneq1 syl $.
$}
$( Equality deduction for indexed union, deduction version.  (Contributed
         by Drahflow, 22-Oct-2015.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$d x A $.
	$d x B $.
	$d x ph $.
	fiuneq12d_0 $f wff ph $.
	fiuneq12d_1 $f set x $.
	fiuneq12d_2 $f class A $.
	fiuneq12d_3 $f class B $.
	fiuneq12d_4 $f class C $.
	fiuneq12d_5 $f class D $.
	eiuneq12d_0 $e |- ( ph -> A = B ) $.
	eiuneq12d_1 $e |- ( ph -> C = D ) $.
	iuneq12d $p |- ( ph -> U_ x e. A C = U_ x e. B D ) $= fiuneq12d_0 fiuneq12d_1 fiuneq12d_2 fiuneq12d_4 ciun fiuneq12d_1 fiuneq12d_3 fiuneq12d_4 ciun fiuneq12d_1 fiuneq12d_3 fiuneq12d_5 ciun fiuneq12d_0 fiuneq12d_1 fiuneq12d_2 fiuneq12d_3 fiuneq12d_4 eiuneq12d_0 iuneq1d fiuneq12d_0 fiuneq12d_1 fiuneq12d_3 fiuneq12d_4 fiuneq12d_5 fiuneq12d_0 fiuneq12d_4 fiuneq12d_5 wceq fiuneq12d_1 cv fiuneq12d_3 wcel eiuneq12d_1 adantr iuneq2dv eqtrd $.
$}
$( Equality deduction for indexed union.  (Contributed by Drahflow,
       22-Oct-2015.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$d x ph $.
	$d x A $.
	fiuneq2d_0 $f wff ph $.
	fiuneq2d_1 $f set x $.
	fiuneq2d_2 $f class A $.
	fiuneq2d_3 $f class B $.
	fiuneq2d_4 $f class C $.
	eiuneq2d_0 $e |- ( ph -> B = C ) $.
	iuneq2d $p |- ( ph -> U_ x e. A B = U_ x e. A C ) $= fiuneq2d_0 fiuneq2d_1 fiuneq2d_2 fiuneq2d_3 fiuneq2d_4 fiuneq2d_0 fiuneq2d_3 fiuneq2d_4 wceq fiuneq2d_1 cv fiuneq2d_2 wcel eiuneq2d_0 adantr iuneq2dv $.
$}
$( Bound-variable hypothesis builder for indexed union.  (Contributed by
       Mario Carneiro, 25-Jan-2014.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v A $.
	$v B $.
	$d z A $.
	$d z B $.
	$d x z $.
	$d y z $.
	infiun_0 $f set z $.
	fnfiun_0 $f set x $.
	fnfiun_1 $f set y $.
	fnfiun_2 $f class A $.
	fnfiun_3 $f class B $.
	enfiun_0 $e |- F/_ y A $.
	enfiun_1 $e |- F/_ y B $.
	nfiun $p |- F/_ y U_ x e. A B $= fnfiun_1 fnfiun_0 fnfiun_2 fnfiun_3 ciun infiun_0 cv fnfiun_3 wcel fnfiun_0 fnfiun_2 wrex infiun_0 cab fnfiun_0 infiun_0 fnfiun_2 fnfiun_3 df-iun infiun_0 cv fnfiun_3 wcel fnfiun_0 fnfiun_2 wrex fnfiun_1 infiun_0 infiun_0 cv fnfiun_3 wcel fnfiun_1 fnfiun_0 fnfiun_2 enfiun_0 fnfiun_1 infiun_0 fnfiun_3 enfiun_1 nfcri nfrex nfab nfcxfr $.
$}
$( Bound-variable hypothesis builder for indexed intersection.
       (Contributed by Mario Carneiro, 25-Jan-2014.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v A $.
	$v B $.
	$d z A $.
	$d z B $.
	$d x z $.
	$d y z $.
	infiin_0 $f set z $.
	fnfiin_0 $f set x $.
	fnfiin_1 $f set y $.
	fnfiin_2 $f class A $.
	fnfiin_3 $f class B $.
	enfiin_0 $e |- F/_ y A $.
	enfiin_1 $e |- F/_ y B $.
	nfiin $p |- F/_ y |^|_ x e. A B $= fnfiin_1 fnfiin_0 fnfiin_2 fnfiin_3 ciin infiin_0 cv fnfiin_3 wcel fnfiin_0 fnfiin_2 wral infiin_0 cab fnfiin_0 infiin_0 fnfiin_2 fnfiin_3 df-iin infiin_0 cv fnfiin_3 wcel fnfiin_0 fnfiin_2 wral fnfiin_1 infiin_0 infiin_0 cv fnfiin_3 wcel fnfiin_1 fnfiin_0 fnfiin_2 enfiin_0 fnfiin_1 infiin_0 fnfiin_3 enfiin_1 nfcri nfral nfab nfcxfr $.
$}
$( Bound-variable hypothesis builder for indexed union.  (Contributed by
       NM, 12-Oct-2003.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$d y A $.
	$d y B $.
	$d x y $.
	infiu1_0 $f set y $.
	fnfiu1_0 $f set x $.
	fnfiu1_1 $f class A $.
	fnfiu1_2 $f class B $.
	nfiu1 $p |- F/_ x U_ x e. A B $= fnfiu1_0 fnfiu1_0 fnfiu1_1 fnfiu1_2 ciun infiu1_0 cv fnfiu1_2 wcel fnfiu1_0 fnfiu1_1 wrex infiu1_0 cab fnfiu1_0 infiu1_0 fnfiu1_1 fnfiu1_2 df-iun infiu1_0 cv fnfiu1_2 wcel fnfiu1_0 fnfiu1_1 wrex fnfiu1_0 infiu1_0 infiu1_0 cv fnfiu1_2 wcel fnfiu1_0 fnfiu1_1 nfre1 nfab nfcxfr $.
$}
$( Bound-variable hypothesis builder for indexed intersection.
       (Contributed by NM, 15-Oct-2003.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$d y A $.
	$d y B $.
	$d x y $.
	infii1_0 $f set y $.
	fnfii1_0 $f set x $.
	fnfii1_1 $f class A $.
	fnfii1_2 $f class B $.
	nfii1 $p |- F/_ x |^|_ x e. A B $= fnfii1_0 fnfii1_0 fnfii1_1 fnfii1_2 ciin infii1_0 cv fnfii1_2 wcel fnfii1_0 fnfii1_1 wral infii1_0 cab fnfii1_0 infii1_0 fnfii1_1 fnfii1_2 df-iin infii1_0 cv fnfii1_2 wcel fnfii1_0 fnfii1_1 wral fnfii1_0 infii1_0 infii1_0 cv fnfii1_2 wcel fnfii1_0 fnfii1_1 nfra1 nfab nfcxfr $.
$}
$( Alternate definition of indexed union when ` B ` is a set.  Definition
       15(a) of [Suppes] p. 44.  (Contributed by NM, 23-Mar-2006.)  (Proof
       shortened by Andrew Salmon, 25-Jul-2011.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v A $.
	$v B $.
	$v C $.
	$d y z A $.
	$d y z B $.
	$d C z $.
	$d x y z $.
	idfiun2g_0 $f set z $.
	fdfiun2g_0 $f set x $.
	fdfiun2g_1 $f set y $.
	fdfiun2g_2 $f class A $.
	fdfiun2g_3 $f class B $.
	fdfiun2g_4 $f class C $.
	dfiun2g $p |- ( A. x e. A B e. C -> U_ x e. A B = U. { y | E. x e. A y = B } ) $= fdfiun2g_3 fdfiun2g_4 wcel fdfiun2g_0 fdfiun2g_2 wral idfiun2g_0 fdfiun2g_0 fdfiun2g_2 fdfiun2g_3 ciun fdfiun2g_1 cv fdfiun2g_3 wceq fdfiun2g_0 fdfiun2g_2 wrex fdfiun2g_1 cab cuni fdfiun2g_3 fdfiun2g_4 wcel fdfiun2g_0 fdfiun2g_2 wral idfiun2g_0 cv fdfiun2g_3 wcel fdfiun2g_0 fdfiun2g_2 wrex idfiun2g_0 cv fdfiun2g_1 cv wcel fdfiun2g_1 cv fdfiun2g_3 wceq fdfiun2g_0 fdfiun2g_2 wrex wa fdfiun2g_1 wex idfiun2g_0 cv fdfiun2g_0 fdfiun2g_2 fdfiun2g_3 ciun wcel idfiun2g_0 cv fdfiun2g_1 cv fdfiun2g_3 wceq fdfiun2g_0 fdfiun2g_2 wrex fdfiun2g_1 cab cuni wcel fdfiun2g_3 fdfiun2g_4 wcel fdfiun2g_0 fdfiun2g_2 wral idfiun2g_0 cv fdfiun2g_3 wcel fdfiun2g_0 fdfiun2g_2 wrex fdfiun2g_1 cv fdfiun2g_3 wceq idfiun2g_0 cv fdfiun2g_1 cv wcel wa fdfiun2g_0 fdfiun2g_2 wrex fdfiun2g_1 wex idfiun2g_0 cv fdfiun2g_1 cv wcel fdfiun2g_1 cv fdfiun2g_3 wceq fdfiun2g_0 fdfiun2g_2 wrex wa fdfiun2g_1 wex fdfiun2g_3 fdfiun2g_4 wcel fdfiun2g_0 fdfiun2g_2 wral idfiun2g_0 cv fdfiun2g_3 wcel fdfiun2g_0 fdfiun2g_2 wrex fdfiun2g_1 cv fdfiun2g_3 wceq idfiun2g_0 cv fdfiun2g_1 cv wcel wa fdfiun2g_1 wex fdfiun2g_0 fdfiun2g_2 wrex fdfiun2g_1 cv fdfiun2g_3 wceq idfiun2g_0 cv fdfiun2g_1 cv wcel wa fdfiun2g_0 fdfiun2g_2 wrex fdfiun2g_1 wex fdfiun2g_3 fdfiun2g_4 wcel fdfiun2g_0 fdfiun2g_2 wral idfiun2g_0 cv fdfiun2g_3 wcel fdfiun2g_1 cv fdfiun2g_3 wceq idfiun2g_0 cv fdfiun2g_1 cv wcel wa fdfiun2g_1 wex fdfiun2g_0 fdfiun2g_2 fdfiun2g_3 fdfiun2g_4 wcel fdfiun2g_0 fdfiun2g_2 nfra1 fdfiun2g_3 fdfiun2g_4 wcel fdfiun2g_0 fdfiun2g_2 wral fdfiun2g_0 cv fdfiun2g_2 wcel idfiun2g_0 cv fdfiun2g_3 wcel fdfiun2g_1 cv fdfiun2g_3 wceq idfiun2g_0 cv fdfiun2g_1 cv wcel wa fdfiun2g_1 wex wb fdfiun2g_3 fdfiun2g_4 wcel fdfiun2g_0 fdfiun2g_2 wral fdfiun2g_0 cv fdfiun2g_2 wcel fdfiun2g_3 fdfiun2g_4 wcel idfiun2g_0 cv fdfiun2g_3 wcel fdfiun2g_1 cv fdfiun2g_3 wceq idfiun2g_0 cv fdfiun2g_1 cv wcel wa fdfiun2g_1 wex wb fdfiun2g_3 fdfiun2g_4 wcel fdfiun2g_0 fdfiun2g_2 rsp fdfiun2g_1 idfiun2g_0 cv fdfiun2g_3 fdfiun2g_4 clel3g syl6 imp rexbida fdfiun2g_1 cv fdfiun2g_3 wceq idfiun2g_0 cv fdfiun2g_1 cv wcel wa fdfiun2g_0 fdfiun2g_1 fdfiun2g_2 rexcom4 syl6bb fdfiun2g_1 cv fdfiun2g_3 wceq idfiun2g_0 cv fdfiun2g_1 cv wcel wa fdfiun2g_0 fdfiun2g_2 wrex fdfiun2g_1 wex fdfiun2g_1 cv fdfiun2g_3 wceq fdfiun2g_0 fdfiun2g_2 wrex idfiun2g_0 cv fdfiun2g_1 cv wcel wa fdfiun2g_1 wex idfiun2g_0 cv fdfiun2g_1 cv wcel fdfiun2g_1 cv fdfiun2g_3 wceq fdfiun2g_0 fdfiun2g_2 wrex wa fdfiun2g_1 wex fdfiun2g_1 cv fdfiun2g_3 wceq idfiun2g_0 cv fdfiun2g_1 cv wcel wa fdfiun2g_0 fdfiun2g_2 wrex fdfiun2g_1 cv fdfiun2g_3 wceq fdfiun2g_0 fdfiun2g_2 wrex idfiun2g_0 cv fdfiun2g_1 cv wcel wa fdfiun2g_1 fdfiun2g_1 cv fdfiun2g_3 wceq idfiun2g_0 cv fdfiun2g_1 cv wcel fdfiun2g_0 fdfiun2g_2 r19.41v exbii fdfiun2g_1 cv fdfiun2g_3 wceq fdfiun2g_0 fdfiun2g_2 wrex idfiun2g_0 cv fdfiun2g_1 cv wcel fdfiun2g_1 exancom bitri syl6bb fdfiun2g_0 idfiun2g_0 cv fdfiun2g_2 fdfiun2g_3 eliun fdfiun2g_1 cv fdfiun2g_3 wceq fdfiun2g_0 fdfiun2g_2 wrex fdfiun2g_1 idfiun2g_0 cv eluniab 3bitr4g eqrdv $.
$}
$( Alternate definition of indexed intersection when ` B ` is a set.
       (Contributed by Jeff Hankins, 27-Aug-2009.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$v A $.
	$v B $.
	$v C $.
	$d y z w A $.
	$d y z w B $.
	$d w C z $.
	$d w x y z $.
	idfiin2g_0 $f set z $.
	idfiin2g_1 $f set w $.
	fdfiin2g_0 $f set x $.
	fdfiin2g_1 $f set y $.
	fdfiin2g_2 $f class A $.
	fdfiin2g_3 $f class B $.
	fdfiin2g_4 $f class C $.
	dfiin2g $p |- ( A. x e. A B e. C -> |^|_ x e. A B = |^| { y | E. x e. A y = B } ) $= fdfiin2g_3 fdfiin2g_4 wcel fdfiin2g_0 fdfiin2g_2 wral idfiin2g_1 cv fdfiin2g_3 wcel fdfiin2g_0 fdfiin2g_2 wral idfiin2g_1 cab idfiin2g_0 cv fdfiin2g_1 cv fdfiin2g_3 wceq fdfiin2g_0 fdfiin2g_2 wrex fdfiin2g_1 cab wcel idfiin2g_1 cv idfiin2g_0 cv wcel wi idfiin2g_0 wal idfiin2g_1 cab fdfiin2g_0 fdfiin2g_2 fdfiin2g_3 ciin fdfiin2g_1 cv fdfiin2g_3 wceq fdfiin2g_0 fdfiin2g_2 wrex fdfiin2g_1 cab cint fdfiin2g_3 fdfiin2g_4 wcel fdfiin2g_0 fdfiin2g_2 wral idfiin2g_1 cv fdfiin2g_3 wcel fdfiin2g_0 fdfiin2g_2 wral idfiin2g_0 cv fdfiin2g_1 cv fdfiin2g_3 wceq fdfiin2g_0 fdfiin2g_2 wrex fdfiin2g_1 cab wcel idfiin2g_1 cv idfiin2g_0 cv wcel wi idfiin2g_0 wal idfiin2g_1 idfiin2g_1 cv fdfiin2g_3 wcel fdfiin2g_0 fdfiin2g_2 wral fdfiin2g_0 cv fdfiin2g_2 wcel idfiin2g_1 cv fdfiin2g_3 wcel wi fdfiin2g_0 wal fdfiin2g_3 fdfiin2g_4 wcel fdfiin2g_0 fdfiin2g_2 wral idfiin2g_0 cv fdfiin2g_1 cv fdfiin2g_3 wceq fdfiin2g_0 fdfiin2g_2 wrex fdfiin2g_1 cab wcel idfiin2g_1 cv idfiin2g_0 cv wcel wi idfiin2g_0 wal idfiin2g_1 cv fdfiin2g_3 wcel fdfiin2g_0 fdfiin2g_2 df-ral fdfiin2g_3 fdfiin2g_4 wcel fdfiin2g_0 fdfiin2g_2 wral fdfiin2g_0 cv fdfiin2g_2 wcel idfiin2g_1 cv fdfiin2g_3 wcel wi fdfiin2g_0 wal fdfiin2g_0 cv fdfiin2g_2 wcel idfiin2g_0 cv fdfiin2g_3 wceq idfiin2g_1 cv idfiin2g_0 cv wcel wi idfiin2g_0 wal wi fdfiin2g_0 wal idfiin2g_0 cv fdfiin2g_1 cv fdfiin2g_3 wceq fdfiin2g_0 fdfiin2g_2 wrex fdfiin2g_1 cab wcel idfiin2g_1 cv idfiin2g_0 cv wcel wi idfiin2g_0 wal fdfiin2g_3 fdfiin2g_4 wcel fdfiin2g_0 fdfiin2g_2 wral fdfiin2g_0 cv fdfiin2g_2 wcel fdfiin2g_3 fdfiin2g_4 wcel wi fdfiin2g_0 wal fdfiin2g_0 cv fdfiin2g_2 wcel idfiin2g_1 cv fdfiin2g_3 wcel wi fdfiin2g_0 wal fdfiin2g_0 cv fdfiin2g_2 wcel idfiin2g_0 cv fdfiin2g_3 wceq idfiin2g_1 cv idfiin2g_0 cv wcel wi idfiin2g_0 wal wi fdfiin2g_0 wal wb fdfiin2g_3 fdfiin2g_4 wcel fdfiin2g_0 fdfiin2g_2 df-ral fdfiin2g_0 cv fdfiin2g_2 wcel fdfiin2g_3 fdfiin2g_4 wcel wi fdfiin2g_0 wal fdfiin2g_0 cv fdfiin2g_2 wcel idfiin2g_1 cv fdfiin2g_3 wcel wi fdfiin2g_0 cv fdfiin2g_2 wcel idfiin2g_0 cv fdfiin2g_3 wceq idfiin2g_1 cv idfiin2g_0 cv wcel wi idfiin2g_0 wal wi wb fdfiin2g_0 wal fdfiin2g_0 cv fdfiin2g_2 wcel idfiin2g_1 cv fdfiin2g_3 wcel wi fdfiin2g_0 wal fdfiin2g_0 cv fdfiin2g_2 wcel idfiin2g_0 cv fdfiin2g_3 wceq idfiin2g_1 cv idfiin2g_0 cv wcel wi idfiin2g_0 wal wi fdfiin2g_0 wal wb fdfiin2g_0 cv fdfiin2g_2 wcel fdfiin2g_3 fdfiin2g_4 wcel wi fdfiin2g_0 cv fdfiin2g_2 wcel idfiin2g_1 cv fdfiin2g_3 wcel wi fdfiin2g_0 cv fdfiin2g_2 wcel idfiin2g_0 cv fdfiin2g_3 wceq idfiin2g_1 cv idfiin2g_0 cv wcel wi idfiin2g_0 wal wi wb fdfiin2g_0 fdfiin2g_0 cv fdfiin2g_2 wcel fdfiin2g_3 fdfiin2g_4 wcel wi fdfiin2g_0 cv fdfiin2g_2 wcel idfiin2g_1 cv fdfiin2g_3 wcel idfiin2g_0 cv fdfiin2g_3 wceq idfiin2g_1 cv idfiin2g_0 cv wcel wi idfiin2g_0 wal fdfiin2g_3 fdfiin2g_4 wcel idfiin2g_1 cv fdfiin2g_3 wcel idfiin2g_0 cv fdfiin2g_3 wceq idfiin2g_1 cv idfiin2g_0 cv wcel wi idfiin2g_0 wal wb fdfiin2g_0 cv fdfiin2g_2 wcel fdfiin2g_3 fdfiin2g_4 wcel idfiin2g_1 cv fdfiin2g_3 wcel idfiin2g_0 cv fdfiin2g_3 wceq idfiin2g_1 cv idfiin2g_0 cv wcel wi idfiin2g_0 wal idfiin2g_1 cv fdfiin2g_3 wcel idfiin2g_0 cv fdfiin2g_3 wceq idfiin2g_1 cv idfiin2g_0 cv wcel wi idfiin2g_0 idfiin2g_0 cv fdfiin2g_3 wceq idfiin2g_1 cv idfiin2g_0 cv wcel idfiin2g_1 cv fdfiin2g_3 wcel idfiin2g_0 cv fdfiin2g_3 idfiin2g_1 cv eleq2 biimprcd alrimiv fdfiin2g_3 fdfiin2g_4 wcel idfiin2g_0 cv fdfiin2g_3 wceq idfiin2g_1 cv idfiin2g_0 cv wcel wi idfiin2g_0 wal fdfiin2g_3 fdfiin2g_3 wceq idfiin2g_1 cv fdfiin2g_3 wcel fdfiin2g_3 eqid idfiin2g_0 cv fdfiin2g_3 wceq idfiin2g_1 cv idfiin2g_0 cv wcel wi fdfiin2g_3 fdfiin2g_3 wceq idfiin2g_1 cv fdfiin2g_3 wcel wi idfiin2g_0 fdfiin2g_3 fdfiin2g_4 idfiin2g_0 cv fdfiin2g_3 wceq idfiin2g_0 cv fdfiin2g_3 wceq fdfiin2g_3 fdfiin2g_3 wceq idfiin2g_1 cv idfiin2g_0 cv wcel idfiin2g_1 cv fdfiin2g_3 wcel idfiin2g_0 cv fdfiin2g_3 fdfiin2g_3 eqeq1 idfiin2g_0 cv fdfiin2g_3 idfiin2g_1 cv eleq2 imbi12d spcgv mpii impbid2 imim2i pm5.74d alimi fdfiin2g_0 cv fdfiin2g_2 wcel idfiin2g_1 cv fdfiin2g_3 wcel wi fdfiin2g_0 cv fdfiin2g_2 wcel idfiin2g_0 cv fdfiin2g_3 wceq idfiin2g_1 cv idfiin2g_0 cv wcel wi idfiin2g_0 wal wi fdfiin2g_0 albi syl sylbi idfiin2g_0 cv fdfiin2g_3 wceq idfiin2g_1 cv idfiin2g_0 cv wcel wi fdfiin2g_0 fdfiin2g_2 wral idfiin2g_0 wal fdfiin2g_0 cv fdfiin2g_2 wcel idfiin2g_0 cv fdfiin2g_3 wceq idfiin2g_1 cv idfiin2g_0 cv wcel wi wi idfiin2g_0 wal fdfiin2g_0 wal idfiin2g_0 cv fdfiin2g_1 cv fdfiin2g_3 wceq fdfiin2g_0 fdfiin2g_2 wrex fdfiin2g_1 cab wcel idfiin2g_1 cv idfiin2g_0 cv wcel wi idfiin2g_0 wal fdfiin2g_0 cv fdfiin2g_2 wcel idfiin2g_0 cv fdfiin2g_3 wceq idfiin2g_1 cv idfiin2g_0 cv wcel wi idfiin2g_0 wal wi fdfiin2g_0 wal idfiin2g_0 cv fdfiin2g_3 wceq idfiin2g_1 cv idfiin2g_0 cv wcel wi fdfiin2g_0 fdfiin2g_2 wral idfiin2g_0 wal fdfiin2g_0 cv fdfiin2g_2 wcel idfiin2g_0 cv fdfiin2g_3 wceq idfiin2g_1 cv idfiin2g_0 cv wcel wi wi fdfiin2g_0 wal idfiin2g_0 wal fdfiin2g_0 cv fdfiin2g_2 wcel idfiin2g_0 cv fdfiin2g_3 wceq idfiin2g_1 cv idfiin2g_0 cv wcel wi wi idfiin2g_0 wal fdfiin2g_0 wal idfiin2g_0 cv fdfiin2g_3 wceq idfiin2g_1 cv idfiin2g_0 cv wcel wi fdfiin2g_0 fdfiin2g_2 wral fdfiin2g_0 cv fdfiin2g_2 wcel idfiin2g_0 cv fdfiin2g_3 wceq idfiin2g_1 cv idfiin2g_0 cv wcel wi wi fdfiin2g_0 wal idfiin2g_0 idfiin2g_0 cv fdfiin2g_3 wceq idfiin2g_1 cv idfiin2g_0 cv wcel wi fdfiin2g_0 fdfiin2g_2 df-ral albii fdfiin2g_0 cv fdfiin2g_2 wcel idfiin2g_0 cv fdfiin2g_3 wceq idfiin2g_1 cv idfiin2g_0 cv wcel wi wi fdfiin2g_0 idfiin2g_0 alcom bitr4i idfiin2g_0 cv fdfiin2g_3 wceq idfiin2g_1 cv idfiin2g_0 cv wcel wi fdfiin2g_0 fdfiin2g_2 wral idfiin2g_0 cv fdfiin2g_1 cv fdfiin2g_3 wceq fdfiin2g_0 fdfiin2g_2 wrex fdfiin2g_1 cab wcel idfiin2g_1 cv idfiin2g_0 cv wcel wi idfiin2g_0 idfiin2g_0 cv fdfiin2g_3 wceq idfiin2g_1 cv idfiin2g_0 cv wcel wi fdfiin2g_0 fdfiin2g_2 wral idfiin2g_0 cv fdfiin2g_3 wceq fdfiin2g_0 fdfiin2g_2 wrex idfiin2g_1 cv idfiin2g_0 cv wcel wi idfiin2g_0 cv fdfiin2g_1 cv fdfiin2g_3 wceq fdfiin2g_0 fdfiin2g_2 wrex fdfiin2g_1 cab wcel idfiin2g_1 cv idfiin2g_0 cv wcel wi idfiin2g_0 cv fdfiin2g_3 wceq idfiin2g_1 cv idfiin2g_0 cv wcel fdfiin2g_0 fdfiin2g_2 r19.23v idfiin2g_0 cv fdfiin2g_1 cv fdfiin2g_3 wceq fdfiin2g_0 fdfiin2g_2 wrex fdfiin2g_1 cab wcel idfiin2g_0 cv fdfiin2g_3 wceq fdfiin2g_0 fdfiin2g_2 wrex idfiin2g_1 cv idfiin2g_0 cv wcel fdfiin2g_1 cv fdfiin2g_3 wceq fdfiin2g_0 fdfiin2g_2 wrex idfiin2g_0 cv fdfiin2g_3 wceq fdfiin2g_0 fdfiin2g_2 wrex fdfiin2g_1 idfiin2g_0 cv idfiin2g_0 vex fdfiin2g_1 cv idfiin2g_0 cv wceq fdfiin2g_1 cv fdfiin2g_3 wceq idfiin2g_0 cv fdfiin2g_3 wceq fdfiin2g_0 fdfiin2g_2 fdfiin2g_1 cv idfiin2g_0 cv fdfiin2g_3 eqeq1 rexbidv elab imbi1i bitr4i albii fdfiin2g_0 cv fdfiin2g_2 wcel idfiin2g_0 cv fdfiin2g_3 wceq idfiin2g_1 cv idfiin2g_0 cv wcel wi wi idfiin2g_0 wal fdfiin2g_0 cv fdfiin2g_2 wcel idfiin2g_0 cv fdfiin2g_3 wceq idfiin2g_1 cv idfiin2g_0 cv wcel wi idfiin2g_0 wal wi fdfiin2g_0 fdfiin2g_0 cv fdfiin2g_2 wcel idfiin2g_0 cv fdfiin2g_3 wceq idfiin2g_1 cv idfiin2g_0 cv wcel wi idfiin2g_0 19.21v albii 3bitr3ri syl6bb syl5bb abbidv fdfiin2g_0 idfiin2g_1 fdfiin2g_2 fdfiin2g_3 df-iin idfiin2g_1 idfiin2g_0 fdfiin2g_1 cv fdfiin2g_3 wceq fdfiin2g_0 fdfiin2g_2 wrex fdfiin2g_1 cab df-int 3eqtr4g $.
$}
$( Alternate definition of indexed union when ` B ` is a set.  Definition
       15(a) of [Suppes] p. 44.  (Contributed by NM, 27-Jun-1998.)  (Revised by
       David Abernethy, 19-Jun-2012.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$d x y $.
	$d y A $.
	$d y B $.
	fdfiun2_0 $f set x $.
	fdfiun2_1 $f set y $.
	fdfiun2_2 $f class A $.
	fdfiun2_3 $f class B $.
	edfiun2_0 $e |- B e. _V $.
	dfiun2 $p |- U_ x e. A B = U. { y | E. x e. A y = B } $= fdfiun2_3 cvv wcel fdfiun2_0 fdfiun2_2 fdfiun2_3 ciun fdfiun2_1 cv fdfiun2_3 wceq fdfiun2_0 fdfiun2_2 wrex fdfiun2_1 cab cuni wceq fdfiun2_0 fdfiun2_2 fdfiun2_0 fdfiun2_1 fdfiun2_2 fdfiun2_3 cvv dfiun2g fdfiun2_3 cvv wcel fdfiun2_0 cv fdfiun2_2 wcel edfiun2_0 a1i mprg $.
$}
$( Alternate definition of indexed intersection when ` B ` is a set.
       Definition 15(b) of [Suppes] p. 44.  (Contributed by NM, 28-Jun-1998.)
       (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$d x y $.
	$d y A $.
	$d y B $.
	fdfiin2_0 $f set x $.
	fdfiin2_1 $f set y $.
	fdfiin2_2 $f class A $.
	fdfiin2_3 $f class B $.
	edfiin2_0 $e |- B e. _V $.
	dfiin2 $p |- |^|_ x e. A B = |^| { y | E. x e. A y = B } $= fdfiin2_3 cvv wcel fdfiin2_0 fdfiin2_2 fdfiin2_3 ciin fdfiin2_1 cv fdfiin2_3 wceq fdfiin2_0 fdfiin2_2 wrex fdfiin2_1 cab cint wceq fdfiin2_0 fdfiin2_2 fdfiin2_0 fdfiin2_1 fdfiin2_2 fdfiin2_3 cvv dfiin2g fdfiin2_3 cvv wcel fdfiin2_0 cv fdfiin2_2 wcel edfiin2_0 a1i mprg $.
$}
$( Rule used to change the bound variables in an indexed union, with the
       substitution specified implicitly by the hypothesis.  (Contributed by
       NM, 26-Mar-2006.)  (Revised by Andrew Salmon, 25-Jul-2011.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v A $.
	$v B $.
	$v C $.
	$d z y A $.
	$d z x A $.
	$d z B $.
	$d z C $.
	icbviun_0 $f set z $.
	fcbviun_0 $f set x $.
	fcbviun_1 $f set y $.
	fcbviun_2 $f class A $.
	fcbviun_3 $f class B $.
	fcbviun_4 $f class C $.
	ecbviun_0 $e |- F/_ y B $.
	ecbviun_1 $e |- F/_ x C $.
	ecbviun_2 $e |- ( x = y -> B = C ) $.
	cbviun $p |- U_ x e. A B = U_ y e. A C $= icbviun_0 cv fcbviun_3 wcel fcbviun_0 fcbviun_2 wrex icbviun_0 cab icbviun_0 cv fcbviun_4 wcel fcbviun_1 fcbviun_2 wrex icbviun_0 cab fcbviun_0 fcbviun_2 fcbviun_3 ciun fcbviun_1 fcbviun_2 fcbviun_4 ciun icbviun_0 cv fcbviun_3 wcel fcbviun_0 fcbviun_2 wrex icbviun_0 cv fcbviun_4 wcel fcbviun_1 fcbviun_2 wrex icbviun_0 icbviun_0 cv fcbviun_3 wcel icbviun_0 cv fcbviun_4 wcel fcbviun_0 fcbviun_1 fcbviun_2 fcbviun_1 icbviun_0 fcbviun_3 ecbviun_0 nfcri fcbviun_0 icbviun_0 fcbviun_4 ecbviun_1 nfcri fcbviun_0 cv fcbviun_1 cv wceq fcbviun_3 fcbviun_4 icbviun_0 cv ecbviun_2 eleq2d cbvrex abbii fcbviun_0 icbviun_0 fcbviun_2 fcbviun_3 df-iun fcbviun_1 icbviun_0 fcbviun_2 fcbviun_4 df-iun 3eqtr4i $.
$}
$( Change bound variables in an indexed intersection.  (Contributed by Jeff
       Hankins, 26-Aug-2009.)  (Revised by Mario Carneiro, 14-Oct-2016.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v A $.
	$v B $.
	$v C $.
	$d z y A $.
	$d z x A $.
	$d z B $.
	$d z C $.
	icbviin_0 $f set z $.
	fcbviin_0 $f set x $.
	fcbviin_1 $f set y $.
	fcbviin_2 $f class A $.
	fcbviin_3 $f class B $.
	fcbviin_4 $f class C $.
	ecbviin_0 $e |- F/_ y B $.
	ecbviin_1 $e |- F/_ x C $.
	ecbviin_2 $e |- ( x = y -> B = C ) $.
	cbviin $p |- |^|_ x e. A B = |^|_ y e. A C $= icbviin_0 cv fcbviin_3 wcel fcbviin_0 fcbviin_2 wral icbviin_0 cab icbviin_0 cv fcbviin_4 wcel fcbviin_1 fcbviin_2 wral icbviin_0 cab fcbviin_0 fcbviin_2 fcbviin_3 ciin fcbviin_1 fcbviin_2 fcbviin_4 ciin icbviin_0 cv fcbviin_3 wcel fcbviin_0 fcbviin_2 wral icbviin_0 cv fcbviin_4 wcel fcbviin_1 fcbviin_2 wral icbviin_0 icbviin_0 cv fcbviin_3 wcel icbviin_0 cv fcbviin_4 wcel fcbviin_0 fcbviin_1 fcbviin_2 fcbviin_1 icbviin_0 fcbviin_3 ecbviin_0 nfcri fcbviin_0 icbviin_0 fcbviin_4 ecbviin_1 nfcri fcbviin_0 cv fcbviin_1 cv wceq fcbviin_3 fcbviin_4 icbviin_0 cv ecbviin_2 eleq2d cbvral abbii fcbviin_0 icbviin_0 fcbviin_2 fcbviin_3 df-iin fcbviin_1 icbviin_0 fcbviin_2 fcbviin_4 df-iin 3eqtr4i $.
$}
$( Rule used to change the bound variables in an indexed union, with the
       substitution specified implicitly by the hypothesis.  (Contributed by
       NM, 15-Sep-2003.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$d x A $.
	$d y A $.
	$d y B $.
	$d x C $.
	fcbviunv_0 $f set x $.
	fcbviunv_1 $f set y $.
	fcbviunv_2 $f class A $.
	fcbviunv_3 $f class B $.
	fcbviunv_4 $f class C $.
	ecbviunv_0 $e |- ( x = y -> B = C ) $.
	cbviunv $p |- U_ x e. A B = U_ y e. A C $= fcbviunv_0 fcbviunv_1 fcbviunv_2 fcbviunv_3 fcbviunv_4 fcbviunv_1 fcbviunv_3 nfcv fcbviunv_0 fcbviunv_4 nfcv ecbviunv_0 cbviun $.
$}
$( Change bound variables in an indexed intersection.  (Contributed by Jeff
       Hankins, 26-Aug-2009.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$d x A $.
	$d y A $.
	$d y B $.
	$d x C $.
	fcbviinv_0 $f set x $.
	fcbviinv_1 $f set y $.
	fcbviinv_2 $f class A $.
	fcbviinv_3 $f class B $.
	fcbviinv_4 $f class C $.
	ecbviinv_0 $e |- ( x = y -> B = C ) $.
	cbviinv $p |- |^|_ x e. A B = |^|_ y e. A C $= fcbviinv_0 fcbviinv_1 fcbviinv_2 fcbviinv_3 fcbviinv_4 fcbviinv_1 fcbviinv_3 nfcv fcbviinv_0 fcbviinv_4 nfcv ecbviinv_0 cbviin $.
$}
$( Subset theorem for an indexed union.  (Contributed by NM, 13-Sep-2003.)
       (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$d x y C $.
	$d y A $.
	$d y B $.
	iiunss_0 $f set y $.
	fiunss_0 $f set x $.
	fiunss_1 $f class A $.
	fiunss_2 $f class B $.
	fiunss_3 $f class C $.
	iunss $p |- ( U_ x e. A B C_ C <-> A. x e. A B C_ C ) $= fiunss_0 fiunss_1 fiunss_2 ciun fiunss_3 wss iiunss_0 cv fiunss_2 wcel fiunss_0 fiunss_1 wrex iiunss_0 cab fiunss_3 wss iiunss_0 cv fiunss_2 wcel fiunss_0 fiunss_1 wrex iiunss_0 cv fiunss_3 wcel wi iiunss_0 wal fiunss_2 fiunss_3 wss fiunss_0 fiunss_1 wral fiunss_0 fiunss_1 fiunss_2 ciun iiunss_0 cv fiunss_2 wcel fiunss_0 fiunss_1 wrex iiunss_0 cab fiunss_3 fiunss_0 iiunss_0 fiunss_1 fiunss_2 df-iun sseq1i iiunss_0 cv fiunss_2 wcel fiunss_0 fiunss_1 wrex iiunss_0 fiunss_3 abss fiunss_2 fiunss_3 wss fiunss_0 fiunss_1 wral iiunss_0 cv fiunss_2 wcel iiunss_0 cv fiunss_3 wcel wi iiunss_0 wal fiunss_0 fiunss_1 wral iiunss_0 cv fiunss_2 wcel iiunss_0 cv fiunss_3 wcel wi fiunss_0 fiunss_1 wral iiunss_0 wal iiunss_0 cv fiunss_2 wcel fiunss_0 fiunss_1 wrex iiunss_0 cv fiunss_3 wcel wi iiunss_0 wal fiunss_2 fiunss_3 wss iiunss_0 cv fiunss_2 wcel iiunss_0 cv fiunss_3 wcel wi iiunss_0 wal fiunss_0 fiunss_1 iiunss_0 fiunss_2 fiunss_3 dfss2 ralbii iiunss_0 cv fiunss_2 wcel iiunss_0 cv fiunss_3 wcel wi fiunss_0 iiunss_0 fiunss_1 ralcom4 iiunss_0 cv fiunss_2 wcel iiunss_0 cv fiunss_3 wcel wi fiunss_0 fiunss_1 wral iiunss_0 cv fiunss_2 wcel fiunss_0 fiunss_1 wrex iiunss_0 cv fiunss_3 wcel wi iiunss_0 iiunss_0 cv fiunss_2 wcel iiunss_0 cv fiunss_3 wcel fiunss_0 fiunss_1 r19.23v albii 3bitrri 3bitri $.
$}
$( Subset implication for an indexed union.  (Contributed by NM,
       3-Sep-2003.)  (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$d x y C $.
	$d y A $.
	$d y B $.
	issiun_0 $f set y $.
	fssiun_0 $f set x $.
	fssiun_1 $f class A $.
	fssiun_2 $f class B $.
	fssiun_3 $f class C $.
	ssiun $p |- ( E. x e. A C C_ B -> C C_ U_ x e. A B ) $= fssiun_3 fssiun_2 wss fssiun_0 fssiun_1 wrex issiun_0 fssiun_3 fssiun_0 fssiun_1 fssiun_2 ciun fssiun_3 fssiun_2 wss fssiun_0 fssiun_1 wrex issiun_0 cv fssiun_3 wcel issiun_0 cv fssiun_2 wcel fssiun_0 fssiun_1 wrex issiun_0 cv fssiun_0 fssiun_1 fssiun_2 ciun wcel fssiun_3 fssiun_2 wss fssiun_0 fssiun_1 wrex issiun_0 cv fssiun_3 wcel issiun_0 cv fssiun_2 wcel wi fssiun_0 fssiun_1 wrex issiun_0 cv fssiun_3 wcel issiun_0 cv fssiun_2 wcel fssiun_0 fssiun_1 wrex wi fssiun_3 fssiun_2 wss issiun_0 cv fssiun_3 wcel issiun_0 cv fssiun_2 wcel wi fssiun_0 fssiun_1 fssiun_3 fssiun_2 issiun_0 cv ssel reximi issiun_0 cv fssiun_3 wcel issiun_0 cv fssiun_2 wcel fssiun_0 fssiun_1 r19.37av syl fssiun_0 issiun_0 cv fssiun_1 fssiun_2 eliun syl6ibr ssrdv $.
$}
$( Identity law for subset of an indexed union.  (Contributed by NM,
       12-Oct-2003.)  (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$d y A $.
	$d y B $.
	$d x y $.
	issiun2_0 $f set y $.
	fssiun2_0 $f set x $.
	fssiun2_1 $f class A $.
	fssiun2_2 $f class B $.
	ssiun2 $p |- ( x e. A -> B C_ U_ x e. A B ) $= fssiun2_0 cv fssiun2_1 wcel issiun2_0 fssiun2_2 fssiun2_0 fssiun2_1 fssiun2_2 ciun fssiun2_0 cv fssiun2_1 wcel issiun2_0 cv fssiun2_2 wcel issiun2_0 cv fssiun2_2 wcel fssiun2_0 fssiun2_1 wrex issiun2_0 cv fssiun2_0 fssiun2_1 fssiun2_2 ciun wcel fssiun2_0 cv fssiun2_1 wcel issiun2_0 cv fssiun2_2 wcel issiun2_0 cv fssiun2_2 wcel fssiun2_0 fssiun2_1 wrex issiun2_0 cv fssiun2_2 wcel fssiun2_0 fssiun2_1 rspe ex fssiun2_0 issiun2_0 cv fssiun2_1 fssiun2_2 eliun syl6ibr ssrdv $.
$}
$( Subset relationship for an indexed union.  (Contributed by NM,
       26-Oct-2003.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$d x A $.
	$d x C $.
	$d x D $.
	fssiun2s_0 $f set x $.
	fssiun2s_1 $f class A $.
	fssiun2s_2 $f class B $.
	fssiun2s_3 $f class C $.
	fssiun2s_4 $f class D $.
	essiun2s_0 $e |- ( x = C -> B = D ) $.
	ssiun2s $p |- ( C e. A -> D C_ U_ x e. A B ) $= fssiun2s_2 fssiun2s_0 fssiun2s_1 fssiun2s_2 ciun wss fssiun2s_4 fssiun2s_0 fssiun2s_1 fssiun2s_2 ciun wss fssiun2s_0 fssiun2s_3 fssiun2s_1 fssiun2s_0 fssiun2s_3 nfcv fssiun2s_0 fssiun2s_4 fssiun2s_0 fssiun2s_1 fssiun2s_2 ciun fssiun2s_0 fssiun2s_4 nfcv fssiun2s_0 fssiun2s_1 fssiun2s_2 nfiu1 nfss fssiun2s_0 cv fssiun2s_3 wceq fssiun2s_2 fssiun2s_4 fssiun2s_0 fssiun2s_1 fssiun2s_2 ciun essiun2s_0 sseq1d fssiun2s_0 fssiun2s_1 fssiun2s_2 ssiun2 vtoclgaf $.
$}
$( A subclass condition on the members of two indexed classes ` C ( x ) `
       and ` D ( y ) ` that implies a subclass relation on their indexed
       unions.  Generalization of Proposition 8.6 of [TakeutiZaring] p. 59.
       Compare ~ uniss2 .  (Contributed by NM, 9-Dec-2004.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$d x y $.
	$d x B $.
	$d y C $.
	$d x D $.
	fiunss2_0 $f set x $.
	fiunss2_1 $f set y $.
	fiunss2_2 $f class A $.
	fiunss2_3 $f class B $.
	fiunss2_4 $f class C $.
	fiunss2_5 $f class D $.
	iunss2 $p |- ( A. x e. A E. y e. B C C_ D -> U_ x e. A C C_ U_ y e. B D ) $= fiunss2_4 fiunss2_5 wss fiunss2_1 fiunss2_3 wrex fiunss2_0 fiunss2_2 wral fiunss2_4 fiunss2_1 fiunss2_3 fiunss2_5 ciun wss fiunss2_0 fiunss2_2 wral fiunss2_0 fiunss2_2 fiunss2_4 ciun fiunss2_1 fiunss2_3 fiunss2_5 ciun wss fiunss2_4 fiunss2_5 wss fiunss2_1 fiunss2_3 wrex fiunss2_4 fiunss2_1 fiunss2_3 fiunss2_5 ciun wss fiunss2_0 fiunss2_2 fiunss2_1 fiunss2_3 fiunss2_5 fiunss2_4 ssiun ralimi fiunss2_0 fiunss2_2 fiunss2_4 fiunss2_1 fiunss2_3 fiunss2_5 ciun iunss sylibr $.
$}
$( The indexed union of a class abstraction.  (Contributed by NM,
       27-Dec-2004.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v A $.
	$d y A $.
	$d x y $.
	fiunab_0 $f wff ph $.
	fiunab_1 $f set x $.
	fiunab_2 $f set y $.
	fiunab_3 $f class A $.
	iunab $p |- U_ x e. A { y | ph } = { y | E. x e. A ph } $= fiunab_1 fiunab_3 fiunab_0 fiunab_2 cab ciun fiunab_0 fiunab_1 fiunab_3 wrex fiunab_2 cab wceq fiunab_2 cv fiunab_1 fiunab_3 fiunab_0 fiunab_2 cab ciun wcel fiunab_2 cv fiunab_0 fiunab_1 fiunab_3 wrex fiunab_2 cab wcel wb fiunab_2 fiunab_2 fiunab_1 fiunab_3 fiunab_0 fiunab_2 cab ciun fiunab_0 fiunab_1 fiunab_3 wrex fiunab_2 cab fiunab_1 fiunab_2 fiunab_3 fiunab_0 fiunab_2 cab fiunab_2 fiunab_3 nfcv fiunab_0 fiunab_2 nfab1 nfiun fiunab_0 fiunab_1 fiunab_3 wrex fiunab_2 nfab1 cleqf fiunab_2 cv fiunab_0 fiunab_2 cab wcel fiunab_1 fiunab_3 wrex fiunab_0 fiunab_1 fiunab_3 wrex fiunab_2 cv fiunab_1 fiunab_3 fiunab_0 fiunab_2 cab ciun wcel fiunab_2 cv fiunab_0 fiunab_1 fiunab_3 wrex fiunab_2 cab wcel fiunab_2 cv fiunab_0 fiunab_2 cab wcel fiunab_0 fiunab_1 fiunab_3 fiunab_0 fiunab_2 abid rexbii fiunab_1 fiunab_2 cv fiunab_3 fiunab_0 fiunab_2 cab eliun fiunab_0 fiunab_1 fiunab_3 wrex fiunab_2 abid 3bitr4i mpgbir $.
$}
$( The indexed union of a restricted class abstraction.  (Contributed by
       NM, 3-Jan-2004.)  (Proof shortened by Mario Carneiro, 14-Nov-2016.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$d y A $.
	$d x y $.
	$d x B $.
	fiunrab_0 $f wff ph $.
	fiunrab_1 $f set x $.
	fiunrab_2 $f set y $.
	fiunrab_3 $f class A $.
	fiunrab_4 $f class B $.
	iunrab $p |- U_ x e. A { y e. B | ph } = { y e. B | E. x e. A ph } $= fiunrab_1 fiunrab_3 fiunrab_2 cv fiunrab_4 wcel fiunrab_0 wa fiunrab_2 cab ciun fiunrab_2 cv fiunrab_4 wcel fiunrab_0 wa fiunrab_1 fiunrab_3 wrex fiunrab_2 cab fiunrab_1 fiunrab_3 fiunrab_0 fiunrab_2 fiunrab_4 crab ciun fiunrab_0 fiunrab_1 fiunrab_3 wrex fiunrab_2 fiunrab_4 crab fiunrab_2 cv fiunrab_4 wcel fiunrab_0 wa fiunrab_1 fiunrab_2 fiunrab_3 iunab fiunrab_1 fiunrab_3 fiunrab_0 fiunrab_2 fiunrab_4 crab fiunrab_2 cv fiunrab_4 wcel fiunrab_0 wa fiunrab_2 cab fiunrab_0 fiunrab_2 fiunrab_4 crab fiunrab_2 cv fiunrab_4 wcel fiunrab_0 wa fiunrab_2 cab wceq fiunrab_1 cv fiunrab_3 wcel fiunrab_0 fiunrab_2 fiunrab_4 df-rab a1i iuneq2i fiunrab_0 fiunrab_1 fiunrab_3 wrex fiunrab_2 fiunrab_4 crab fiunrab_2 cv fiunrab_4 wcel fiunrab_0 fiunrab_1 fiunrab_3 wrex wa fiunrab_2 cab fiunrab_2 cv fiunrab_4 wcel fiunrab_0 wa fiunrab_1 fiunrab_3 wrex fiunrab_2 cab fiunrab_0 fiunrab_1 fiunrab_3 wrex fiunrab_2 fiunrab_4 df-rab fiunrab_2 cv fiunrab_4 wcel fiunrab_0 wa fiunrab_1 fiunrab_3 wrex fiunrab_2 cv fiunrab_4 wcel fiunrab_0 fiunrab_1 fiunrab_3 wrex wa fiunrab_2 fiunrab_2 cv fiunrab_4 wcel fiunrab_0 fiunrab_1 fiunrab_3 r19.42v abbii eqtr4i 3eqtr4i $.
$}
$( Indexed union with a class difference as its index.  (Contributed by NM,
       10-Dec-2004.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$d x y A $.
	$d x y B $.
	$d y C $.
	$d x D $.
	fiunxdif2_0 $f set x $.
	fiunxdif2_1 $f set y $.
	fiunxdif2_2 $f class A $.
	fiunxdif2_3 $f class B $.
	fiunxdif2_4 $f class C $.
	fiunxdif2_5 $f class D $.
	eiunxdif2_0 $e |- ( x = y -> C = D ) $.
	iunxdif2 $p |- ( A. x e. A E. y e. ( A \ B ) C C_ D -> U_ y e. ( A \ B ) D = U_ x e. A C ) $= fiunxdif2_4 fiunxdif2_5 wss fiunxdif2_1 fiunxdif2_2 fiunxdif2_3 cdif wrex fiunxdif2_0 fiunxdif2_2 wral fiunxdif2_1 fiunxdif2_2 fiunxdif2_3 cdif fiunxdif2_5 ciun fiunxdif2_0 fiunxdif2_2 fiunxdif2_4 ciun wss fiunxdif2_0 fiunxdif2_2 fiunxdif2_4 ciun fiunxdif2_1 fiunxdif2_2 fiunxdif2_3 cdif fiunxdif2_5 ciun wss wa fiunxdif2_1 fiunxdif2_2 fiunxdif2_3 cdif fiunxdif2_5 ciun fiunxdif2_0 fiunxdif2_2 fiunxdif2_4 ciun wceq fiunxdif2_4 fiunxdif2_5 wss fiunxdif2_1 fiunxdif2_2 fiunxdif2_3 cdif wrex fiunxdif2_0 fiunxdif2_2 wral fiunxdif2_0 fiunxdif2_2 fiunxdif2_4 ciun fiunxdif2_1 fiunxdif2_2 fiunxdif2_3 cdif fiunxdif2_5 ciun wss fiunxdif2_1 fiunxdif2_2 fiunxdif2_3 cdif fiunxdif2_5 ciun fiunxdif2_0 fiunxdif2_2 fiunxdif2_4 ciun wss fiunxdif2_0 fiunxdif2_1 fiunxdif2_2 fiunxdif2_2 fiunxdif2_3 cdif fiunxdif2_4 fiunxdif2_5 iunss2 fiunxdif2_1 fiunxdif2_2 fiunxdif2_3 cdif fiunxdif2_5 ciun fiunxdif2_1 fiunxdif2_2 fiunxdif2_5 ciun fiunxdif2_0 fiunxdif2_2 fiunxdif2_4 ciun fiunxdif2_2 fiunxdif2_3 cdif fiunxdif2_2 wss fiunxdif2_1 fiunxdif2_2 fiunxdif2_3 cdif fiunxdif2_5 ciun fiunxdif2_1 fiunxdif2_2 fiunxdif2_5 ciun wss fiunxdif2_2 fiunxdif2_3 difss fiunxdif2_1 fiunxdif2_2 fiunxdif2_3 cdif fiunxdif2_2 fiunxdif2_5 iunss1 ax-mp fiunxdif2_0 fiunxdif2_1 fiunxdif2_2 fiunxdif2_4 fiunxdif2_5 eiunxdif2_0 cbviunv sseqtr4i jctil fiunxdif2_1 fiunxdif2_2 fiunxdif2_3 cdif fiunxdif2_5 ciun fiunxdif2_0 fiunxdif2_2 fiunxdif2_4 ciun eqss sylibr $.
$}
$( Subset theorem for an indexed intersection.  (Contributed by FL,
       15-Oct-2012.)  (Proof shortened by Mario Carneiro, 14-Oct-2016.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$d y A $.
	$d y B $.
	$d y C $.
	$d x y $.
	issiinf_0 $f set y $.
	fssiinf_0 $f set x $.
	fssiinf_1 $f class A $.
	fssiinf_2 $f class B $.
	fssiinf_3 $f class C $.
	essiinf_0 $e |- F/_ x C $.
	ssiinf $p |- ( C C_ |^|_ x e. A B <-> A. x e. A C C_ B ) $= issiinf_0 cv fssiinf_0 fssiinf_1 fssiinf_2 ciin wcel issiinf_0 fssiinf_3 wral issiinf_0 cv fssiinf_2 wcel issiinf_0 fssiinf_3 wral fssiinf_0 fssiinf_1 wral fssiinf_3 fssiinf_0 fssiinf_1 fssiinf_2 ciin wss fssiinf_3 fssiinf_2 wss fssiinf_0 fssiinf_1 wral issiinf_0 cv fssiinf_0 fssiinf_1 fssiinf_2 ciin wcel issiinf_0 fssiinf_3 wral issiinf_0 cv fssiinf_2 wcel fssiinf_0 fssiinf_1 wral issiinf_0 fssiinf_3 wral issiinf_0 cv fssiinf_2 wcel issiinf_0 fssiinf_3 wral fssiinf_0 fssiinf_1 wral issiinf_0 cv fssiinf_0 fssiinf_1 fssiinf_2 ciin wcel issiinf_0 cv fssiinf_2 wcel fssiinf_0 fssiinf_1 wral issiinf_0 fssiinf_3 issiinf_0 cv cvv wcel issiinf_0 cv fssiinf_0 fssiinf_1 fssiinf_2 ciin wcel issiinf_0 cv fssiinf_2 wcel fssiinf_0 fssiinf_1 wral wb issiinf_0 vex fssiinf_0 issiinf_0 cv fssiinf_1 fssiinf_2 cvv eliin ax-mp ralbii issiinf_0 cv fssiinf_2 wcel issiinf_0 fssiinf_0 fssiinf_3 fssiinf_1 essiinf_0 issiinf_0 fssiinf_1 nfcv ralcomf bitri issiinf_0 fssiinf_3 fssiinf_0 fssiinf_1 fssiinf_2 ciin dfss3 fssiinf_3 fssiinf_2 wss issiinf_0 cv fssiinf_2 wcel issiinf_0 fssiinf_3 wral fssiinf_0 fssiinf_1 issiinf_0 fssiinf_3 fssiinf_2 dfss3 ralbii 3bitr4i $.
$}
$( Subset theorem for an indexed intersection.  (Contributed by NM,
       15-Oct-2003.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$d x C $.
	fssiin_0 $f set x $.
	fssiin_1 $f class A $.
	fssiin_2 $f class B $.
	fssiin_3 $f class C $.
	ssiin $p |- ( C C_ |^|_ x e. A B <-> A. x e. A C C_ B ) $= fssiin_0 fssiin_1 fssiin_2 fssiin_3 fssiin_0 fssiin_3 nfcv ssiinf $.
$}
$( Subset implication for an indexed intersection.  (Contributed by NM,
       15-Oct-2003.)  (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$d x y C $.
	$d y A $.
	$d y B $.
	iiinss_0 $f set y $.
	fiinss_0 $f set x $.
	fiinss_1 $f class A $.
	fiinss_2 $f class B $.
	fiinss_3 $f class C $.
	iinss $p |- ( E. x e. A B C_ C -> |^|_ x e. A B C_ C ) $= fiinss_2 fiinss_3 wss fiinss_0 fiinss_1 wrex iiinss_0 fiinss_0 fiinss_1 fiinss_2 ciin fiinss_3 iiinss_0 cv fiinss_0 fiinss_1 fiinss_2 ciin wcel iiinss_0 cv fiinss_2 wcel fiinss_0 fiinss_1 wral fiinss_2 fiinss_3 wss fiinss_0 fiinss_1 wrex iiinss_0 cv fiinss_3 wcel iiinss_0 cv cvv wcel iiinss_0 cv fiinss_0 fiinss_1 fiinss_2 ciin wcel iiinss_0 cv fiinss_2 wcel fiinss_0 fiinss_1 wral wb iiinss_0 vex fiinss_0 iiinss_0 cv fiinss_1 fiinss_2 cvv eliin ax-mp fiinss_2 fiinss_3 wss fiinss_0 fiinss_1 wrex iiinss_0 cv fiinss_2 wcel iiinss_0 cv fiinss_3 wcel wi fiinss_0 fiinss_1 wrex iiinss_0 cv fiinss_2 wcel fiinss_0 fiinss_1 wral iiinss_0 cv fiinss_3 wcel wi fiinss_2 fiinss_3 wss iiinss_0 cv fiinss_2 wcel iiinss_0 cv fiinss_3 wcel wi fiinss_0 fiinss_1 fiinss_2 fiinss_3 iiinss_0 cv ssel reximi iiinss_0 cv fiinss_2 wcel iiinss_0 cv fiinss_3 wcel fiinss_0 fiinss_1 r19.36av syl syl5bi ssrdv $.
$}
$( An indexed intersection is included in any of its members.  (Contributed
       by FL, 15-Oct-2012.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$d A y $.
	$d B y $.
	$d x y $.
	iiinss2_0 $f set y $.
	fiinss2_0 $f set x $.
	fiinss2_1 $f class A $.
	fiinss2_2 $f class B $.
	iinss2 $p |- ( x e. A -> |^|_ x e. A B C_ B ) $= fiinss2_0 cv fiinss2_1 wcel iiinss2_0 fiinss2_0 fiinss2_1 fiinss2_2 ciin fiinss2_2 iiinss2_0 cv fiinss2_0 fiinss2_1 fiinss2_2 ciin wcel fiinss2_0 cv fiinss2_1 wcel iiinss2_0 cv fiinss2_2 wcel iiinss2_0 cv fiinss2_0 fiinss2_1 fiinss2_2 ciin wcel iiinss2_0 cv fiinss2_2 wcel fiinss2_0 fiinss2_1 wral fiinss2_0 cv fiinss2_1 wcel iiinss2_0 cv fiinss2_2 wcel wi iiinss2_0 cv cvv wcel iiinss2_0 cv fiinss2_0 fiinss2_1 fiinss2_2 ciin wcel iiinss2_0 cv fiinss2_2 wcel fiinss2_0 fiinss2_1 wral wb iiinss2_0 vex fiinss2_0 iiinss2_0 cv fiinss2_1 fiinss2_2 cvv eliin ax-mp iiinss2_0 cv fiinss2_2 wcel fiinss2_0 fiinss2_1 rsp sylbi com12 ssrdv $.
$}
$( Class union in terms of indexed union.  Definition in [Stoll] p. 43.
       (Contributed by NM, 28-Jun-1998.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$d x y A $.
	iuniiun_0 $f set y $.
	funiiun_0 $f set x $.
	funiiun_1 $f class A $.
	uniiun $p |- U. A = U_ x e. A x $= funiiun_1 cuni iuniiun_0 cv funiiun_0 cv wcel funiiun_0 funiiun_1 wrex iuniiun_0 cab funiiun_0 funiiun_1 funiiun_0 cv ciun iuniiun_0 funiiun_0 funiiun_1 dfuni2 funiiun_0 iuniiun_0 funiiun_1 funiiun_0 cv df-iun eqtr4i $.
$}
$( Class intersection in terms of indexed intersection.  Definition in
       [Stoll] p. 44.  (Contributed by NM, 28-Jun-1998.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$d x y A $.
	iintiin_0 $f set y $.
	fintiin_0 $f set x $.
	fintiin_1 $f class A $.
	intiin $p |- |^| A = |^|_ x e. A x $= fintiin_1 cint iintiin_0 cv fintiin_0 cv wcel fintiin_0 fintiin_1 wral iintiin_0 cab fintiin_0 fintiin_1 fintiin_0 cv ciin iintiin_0 fintiin_0 fintiin_1 dfint2 fintiin_0 iintiin_0 fintiin_1 fintiin_0 cv df-iin eqtr4i $.
$}
$( An indexed union of singletons recovers the index set.  (Contributed by
       NM, 6-Sep-2005.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$d x y A $.
	iiunid_0 $f set y $.
	fiunid_0 $f set x $.
	fiunid_1 $f class A $.
	iunid $p |- U_ x e. A { x } = A $= fiunid_0 fiunid_1 fiunid_0 cv csn ciun fiunid_0 fiunid_1 fiunid_0 cv iiunid_0 cv wceq iiunid_0 cab ciun fiunid_1 fiunid_0 fiunid_1 fiunid_0 cv csn fiunid_0 cv iiunid_0 cv wceq iiunid_0 cab fiunid_0 cv csn fiunid_0 cv iiunid_0 cv wceq iiunid_0 cab wceq fiunid_0 cv fiunid_1 wcel fiunid_0 cv csn iiunid_0 cv fiunid_0 cv wceq iiunid_0 cab fiunid_0 cv iiunid_0 cv wceq iiunid_0 cab iiunid_0 fiunid_0 cv df-sn iiunid_0 cv fiunid_0 cv wceq fiunid_0 cv iiunid_0 cv wceq iiunid_0 iiunid_0 fiunid_0 equcom abbii eqtri a1i iuneq2i fiunid_0 fiunid_1 fiunid_0 cv iiunid_0 cv wceq iiunid_0 cab ciun fiunid_0 cv iiunid_0 cv wceq fiunid_0 fiunid_1 wrex iiunid_0 cab iiunid_0 cv fiunid_1 wcel iiunid_0 cab fiunid_1 fiunid_0 cv iiunid_0 cv wceq fiunid_0 iiunid_0 fiunid_1 iunab iiunid_0 cv fiunid_1 wcel fiunid_0 cv iiunid_0 cv wceq fiunid_0 fiunid_1 wrex iiunid_0 fiunid_0 iiunid_0 cv fiunid_1 risset abbii iiunid_0 fiunid_1 abid2 3eqtr2i eqtri $.
$}
$( An indexed union of the empty set is empty.  (Contributed by NM,
       26-Mar-2003.)  (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$d x y $.
	$d y A $.
	iiun0_0 $f set y $.
	fiun0_0 $f set x $.
	fiun0_1 $f class A $.
	iun0 $p |- U_ x e. A (/) = (/) $= iiun0_0 fiun0_0 fiun0_1 c0 ciun c0 iiun0_0 cv fiun0_0 fiun0_1 c0 ciun wcel iiun0_0 cv c0 wcel iiun0_0 cv fiun0_0 fiun0_1 c0 ciun wcel iiun0_0 cv c0 wcel fiun0_0 fiun0_1 wrex iiun0_0 cv c0 wcel fiun0_0 fiun0_1 iiun0_0 cv c0 wcel wn fiun0_0 cv fiun0_1 wcel iiun0_0 cv noel a1i nrex fiun0_0 iiun0_0 cv fiun0_1 c0 eliun mtbir iiun0_0 cv noel 2false eqriv $.
$}
$( An empty indexed union is empty.  (Contributed by NM, 4-Dec-2004.)
       (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$d x y $.
	$d y A $.
	i0iun_0 $f set y $.
	f0iun_0 $f set x $.
	f0iun_1 $f class A $.
	0iun $p |- U_ x e. (/) A = (/) $= i0iun_0 f0iun_0 c0 f0iun_1 ciun c0 i0iun_0 cv f0iun_0 c0 f0iun_1 ciun wcel i0iun_0 cv c0 wcel i0iun_0 cv f0iun_0 c0 f0iun_1 ciun wcel i0iun_0 cv f0iun_1 wcel f0iun_0 c0 wrex i0iun_0 cv f0iun_1 wcel f0iun_0 rex0 f0iun_0 i0iun_0 cv c0 f0iun_1 eliun mtbir i0iun_0 cv noel 2false eqriv $.
$}
$( An empty indexed intersection is the universal class.  (Contributed by
       NM, 20-Oct-2005.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$d x y $.
	$d y A $.
	i0iin_0 $f set y $.
	f0iin_0 $f set x $.
	f0iin_1 $f class A $.
	0iin $p |- |^|_ x e. (/) A = _V $= f0iin_0 c0 f0iin_1 ciin i0iin_0 cv f0iin_1 wcel f0iin_0 c0 wral i0iin_0 cab cvv f0iin_0 i0iin_0 c0 f0iin_1 df-iin i0iin_0 cv f0iin_1 wcel f0iin_0 c0 wral i0iin_0 cvv i0iin_0 cv cvv wcel i0iin_0 cv f0iin_1 wcel f0iin_0 c0 wral i0iin_0 vex i0iin_0 cv f0iin_1 wcel f0iin_0 ral0 2th abbi2i eqtr4i $.
$}
$( Indexed intersection with a universal index class.  When ` A ` doesn't
       depend on ` x ` , this evaluates to ` A ` by ~ 19.3 and ~ abid2 .  When
       ` A = x ` , this evaluates to ` (/) ` by ~ intiin and ~ intv .
       (Contributed by NM, 11-Sep-2008.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$d x y $.
	$d y A $.
	fviin_0 $f set x $.
	fviin_1 $f set y $.
	fviin_2 $f class A $.
	viin $p |- |^|_ x e. _V A = { y | A. x y e. A } $= fviin_0 cvv fviin_2 ciin fviin_1 cv fviin_2 wcel fviin_0 cvv wral fviin_1 cab fviin_1 cv fviin_2 wcel fviin_0 wal fviin_1 cab fviin_0 fviin_1 cvv fviin_2 df-iin fviin_1 cv fviin_2 wcel fviin_0 cvv wral fviin_1 cv fviin_2 wcel fviin_0 wal fviin_1 fviin_1 cv fviin_2 wcel fviin_0 ralv abbii eqtri $.
$}
$( There is a non-empty class in an indexed collection ` B ( x ) ` iff the
       indexed union of them is non-empty.  (Contributed by NM, 15-Oct-2003.)
       (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$d x y A $.
	$d y B $.
	iiunn0_0 $f set y $.
	fiunn0_0 $f set x $.
	fiunn0_1 $f class A $.
	fiunn0_2 $f class B $.
	iunn0 $p |- ( E. x e. A B =/= (/) <-> U_ x e. A B =/= (/) ) $= iiunn0_0 cv fiunn0_2 wcel iiunn0_0 wex fiunn0_0 fiunn0_1 wrex iiunn0_0 cv fiunn0_0 fiunn0_1 fiunn0_2 ciun wcel iiunn0_0 wex fiunn0_2 c0 wne fiunn0_0 fiunn0_1 wrex fiunn0_0 fiunn0_1 fiunn0_2 ciun c0 wne iiunn0_0 cv fiunn0_2 wcel iiunn0_0 wex fiunn0_0 fiunn0_1 wrex iiunn0_0 cv fiunn0_2 wcel fiunn0_0 fiunn0_1 wrex iiunn0_0 wex iiunn0_0 cv fiunn0_0 fiunn0_1 fiunn0_2 ciun wcel iiunn0_0 wex iiunn0_0 cv fiunn0_2 wcel fiunn0_0 iiunn0_0 fiunn0_1 rexcom4 iiunn0_0 cv fiunn0_0 fiunn0_1 fiunn0_2 ciun wcel iiunn0_0 cv fiunn0_2 wcel fiunn0_0 fiunn0_1 wrex iiunn0_0 fiunn0_0 iiunn0_0 cv fiunn0_1 fiunn0_2 eliun exbii bitr4i fiunn0_2 c0 wne iiunn0_0 cv fiunn0_2 wcel iiunn0_0 wex fiunn0_0 fiunn0_1 iiunn0_0 fiunn0_2 n0 rexbii iiunn0_0 fiunn0_0 fiunn0_1 fiunn0_2 ciun n0 3bitr4i $.
$}
$( Indexed intersection of a class builder.  (Contributed by NM,
       6-Dec-2011.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v A $.
	$d y A $.
	$d x y $.
	fiinab_0 $f wff ph $.
	fiinab_1 $f set x $.
	fiinab_2 $f set y $.
	fiinab_3 $f class A $.
	iinab $p |- |^|_ x e. A { y | ph } = { y | A. x e. A ph } $= fiinab_1 fiinab_3 fiinab_0 fiinab_2 cab ciin fiinab_0 fiinab_1 fiinab_3 wral fiinab_2 cab wceq fiinab_2 cv fiinab_1 fiinab_3 fiinab_0 fiinab_2 cab ciin wcel fiinab_2 cv fiinab_0 fiinab_1 fiinab_3 wral fiinab_2 cab wcel wb fiinab_2 fiinab_2 fiinab_1 fiinab_3 fiinab_0 fiinab_2 cab ciin fiinab_0 fiinab_1 fiinab_3 wral fiinab_2 cab fiinab_1 fiinab_2 fiinab_3 fiinab_0 fiinab_2 cab fiinab_2 fiinab_3 nfcv fiinab_0 fiinab_2 nfab1 nfiin fiinab_0 fiinab_1 fiinab_3 wral fiinab_2 nfab1 cleqf fiinab_2 cv fiinab_0 fiinab_2 cab wcel fiinab_1 fiinab_3 wral fiinab_0 fiinab_1 fiinab_3 wral fiinab_2 cv fiinab_1 fiinab_3 fiinab_0 fiinab_2 cab ciin wcel fiinab_2 cv fiinab_0 fiinab_1 fiinab_3 wral fiinab_2 cab wcel fiinab_2 cv fiinab_0 fiinab_2 cab wcel fiinab_0 fiinab_1 fiinab_3 fiinab_0 fiinab_2 abid ralbii fiinab_2 cv cvv wcel fiinab_2 cv fiinab_1 fiinab_3 fiinab_0 fiinab_2 cab ciin wcel fiinab_2 cv fiinab_0 fiinab_2 cab wcel fiinab_1 fiinab_3 wral wb fiinab_2 vex fiinab_1 fiinab_2 cv fiinab_3 fiinab_0 fiinab_2 cab cvv eliin ax-mp fiinab_0 fiinab_1 fiinab_3 wral fiinab_2 abid 3bitr4i mpgbir $.
$}
$( Indexed intersection of a restricted class builder.  (Contributed by NM,
       6-Dec-2011.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$d y A $.
	$d x y $.
	$d x A $.
	$d x B $.
	fiinrab_0 $f wff ph $.
	fiinrab_1 $f set x $.
	fiinrab_2 $f set y $.
	fiinrab_3 $f class A $.
	fiinrab_4 $f class B $.
	iinrab $p |- ( A =/= (/) -> |^|_ x e. A { y e. B | ph } = { y e. B | A. x e. A ph } ) $= fiinrab_3 c0 wne fiinrab_2 cv fiinrab_4 wcel fiinrab_0 wa fiinrab_1 fiinrab_3 wral fiinrab_2 cab fiinrab_2 cv fiinrab_4 wcel fiinrab_0 fiinrab_1 fiinrab_3 wral wa fiinrab_2 cab fiinrab_1 fiinrab_3 fiinrab_0 fiinrab_2 fiinrab_4 crab ciin fiinrab_0 fiinrab_1 fiinrab_3 wral fiinrab_2 fiinrab_4 crab fiinrab_3 c0 wne fiinrab_2 cv fiinrab_4 wcel fiinrab_0 wa fiinrab_1 fiinrab_3 wral fiinrab_2 cv fiinrab_4 wcel fiinrab_0 fiinrab_1 fiinrab_3 wral wa fiinrab_2 fiinrab_2 cv fiinrab_4 wcel fiinrab_0 fiinrab_1 fiinrab_3 r19.28zv abbidv fiinrab_1 fiinrab_3 fiinrab_0 fiinrab_2 fiinrab_4 crab ciin fiinrab_1 fiinrab_3 fiinrab_2 cv fiinrab_4 wcel fiinrab_0 wa fiinrab_2 cab ciin fiinrab_2 cv fiinrab_4 wcel fiinrab_0 wa fiinrab_1 fiinrab_3 wral fiinrab_2 cab fiinrab_1 fiinrab_3 fiinrab_0 fiinrab_2 fiinrab_4 crab fiinrab_2 cv fiinrab_4 wcel fiinrab_0 wa fiinrab_2 cab fiinrab_0 fiinrab_2 fiinrab_4 crab fiinrab_2 cv fiinrab_4 wcel fiinrab_0 wa fiinrab_2 cab wceq fiinrab_1 cv fiinrab_3 wcel fiinrab_0 fiinrab_2 fiinrab_4 df-rab a1i iineq2i fiinrab_2 cv fiinrab_4 wcel fiinrab_0 wa fiinrab_1 fiinrab_2 fiinrab_3 iinab eqtri fiinrab_0 fiinrab_1 fiinrab_3 wral fiinrab_2 fiinrab_4 df-rab 3eqtr4g $.
$}
$( Indexed intersection of a restricted class builder.  (Contributed by NM,
       6-Dec-2011.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$d y A $.
	$d x y $.
	$d x A $.
	$d x B $.
	$d y B $.
	fiinrab2_0 $f wff ph $.
	fiinrab2_1 $f set x $.
	fiinrab2_2 $f set y $.
	fiinrab2_3 $f class A $.
	fiinrab2_4 $f class B $.
	iinrab2 $p |- ( |^|_ x e. A { y e. B | ph } i^i B ) = { y e. B | A. x e. A ph } $= fiinrab2_1 fiinrab2_3 fiinrab2_0 fiinrab2_2 fiinrab2_4 crab ciin fiinrab2_4 cin fiinrab2_0 fiinrab2_1 fiinrab2_3 wral fiinrab2_2 fiinrab2_4 crab wceq fiinrab2_3 c0 fiinrab2_3 c0 wceq fiinrab2_1 fiinrab2_3 fiinrab2_0 fiinrab2_2 fiinrab2_4 crab ciin fiinrab2_4 cin fiinrab2_4 fiinrab2_0 fiinrab2_1 fiinrab2_3 wral fiinrab2_2 fiinrab2_4 crab fiinrab2_3 c0 wceq fiinrab2_1 fiinrab2_3 fiinrab2_0 fiinrab2_2 fiinrab2_4 crab ciin fiinrab2_4 cin cvv fiinrab2_4 cin fiinrab2_4 fiinrab2_3 c0 wceq fiinrab2_1 fiinrab2_3 fiinrab2_0 fiinrab2_2 fiinrab2_4 crab ciin cvv fiinrab2_4 fiinrab2_3 c0 wceq fiinrab2_1 fiinrab2_3 fiinrab2_0 fiinrab2_2 fiinrab2_4 crab ciin fiinrab2_1 c0 fiinrab2_0 fiinrab2_2 fiinrab2_4 crab ciin cvv fiinrab2_1 fiinrab2_3 c0 fiinrab2_0 fiinrab2_2 fiinrab2_4 crab iineq1 fiinrab2_1 fiinrab2_0 fiinrab2_2 fiinrab2_4 crab 0iin syl6eq ineq1d cvv fiinrab2_4 cin fiinrab2_4 cvv cin fiinrab2_4 cvv fiinrab2_4 incom fiinrab2_4 inv1 eqtri syl6eq fiinrab2_3 c0 wceq fiinrab2_0 fiinrab2_2 fiinrab2_4 wral fiinrab2_1 fiinrab2_3 wral fiinrab2_4 fiinrab2_0 fiinrab2_1 fiinrab2_3 wral fiinrab2_2 fiinrab2_4 crab wceq fiinrab2_0 fiinrab2_2 fiinrab2_4 wral fiinrab2_1 fiinrab2_3 rzal fiinrab2_4 fiinrab2_0 fiinrab2_1 fiinrab2_3 wral fiinrab2_2 fiinrab2_4 crab wceq fiinrab2_0 fiinrab2_1 fiinrab2_3 wral fiinrab2_2 fiinrab2_4 wral fiinrab2_0 fiinrab2_2 fiinrab2_4 wral fiinrab2_1 fiinrab2_3 wral fiinrab2_0 fiinrab2_1 fiinrab2_3 wral fiinrab2_2 fiinrab2_4 rabid2 fiinrab2_0 fiinrab2_2 fiinrab2_1 fiinrab2_4 fiinrab2_3 ralcom bitr2i sylib eqtrd fiinrab2_3 c0 wne fiinrab2_1 fiinrab2_3 fiinrab2_0 fiinrab2_2 fiinrab2_4 crab ciin fiinrab2_4 cin fiinrab2_0 fiinrab2_1 fiinrab2_3 wral fiinrab2_2 fiinrab2_4 crab fiinrab2_4 cin fiinrab2_0 fiinrab2_1 fiinrab2_3 wral fiinrab2_2 fiinrab2_4 crab fiinrab2_3 c0 wne fiinrab2_1 fiinrab2_3 fiinrab2_0 fiinrab2_2 fiinrab2_4 crab ciin fiinrab2_0 fiinrab2_1 fiinrab2_3 wral fiinrab2_2 fiinrab2_4 crab fiinrab2_4 fiinrab2_0 fiinrab2_1 fiinrab2_2 fiinrab2_3 fiinrab2_4 iinrab ineq1d fiinrab2_0 fiinrab2_1 fiinrab2_3 wral fiinrab2_2 fiinrab2_4 crab fiinrab2_4 wss fiinrab2_0 fiinrab2_1 fiinrab2_3 wral fiinrab2_2 fiinrab2_4 crab fiinrab2_0 fiinrab2_1 fiinrab2_3 wral fiinrab2_2 fiinrab2_4 crab fiinrab2_4 cin wceq fiinrab2_0 fiinrab2_1 fiinrab2_3 wral fiinrab2_2 fiinrab2_4 ssrab2 fiinrab2_0 fiinrab2_1 fiinrab2_3 wral fiinrab2_2 fiinrab2_4 crab fiinrab2_4 dfss mpbi syl6eqr pm2.61ine $.
$}
$( Indexed union of intersection.  Generalization of half of theorem
       "Distributive laws" in [Enderton] p. 30.  Use ~ uniiun to recover
       Enderton's theorem.  (Contributed by NM, 26-Mar-2004.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$d y A $.
	$d x y B $.
	$d y C $.
	iiunin2_0 $f set y $.
	fiunin2_0 $f set x $.
	fiunin2_1 $f class A $.
	fiunin2_2 $f class B $.
	fiunin2_3 $f class C $.
	iunin2 $p |- U_ x e. A ( B i^i C ) = ( B i^i U_ x e. A C ) $= iiunin2_0 fiunin2_0 fiunin2_1 fiunin2_2 fiunin2_3 cin ciun fiunin2_2 fiunin2_0 fiunin2_1 fiunin2_3 ciun cin iiunin2_0 cv fiunin2_2 fiunin2_3 cin wcel fiunin2_0 fiunin2_1 wrex iiunin2_0 cv fiunin2_2 wcel iiunin2_0 cv fiunin2_0 fiunin2_1 fiunin2_3 ciun wcel wa iiunin2_0 cv fiunin2_0 fiunin2_1 fiunin2_2 fiunin2_3 cin ciun wcel iiunin2_0 cv fiunin2_2 fiunin2_0 fiunin2_1 fiunin2_3 ciun cin wcel iiunin2_0 cv fiunin2_2 wcel iiunin2_0 cv fiunin2_3 wcel wa fiunin2_0 fiunin2_1 wrex iiunin2_0 cv fiunin2_2 wcel iiunin2_0 cv fiunin2_3 wcel fiunin2_0 fiunin2_1 wrex wa iiunin2_0 cv fiunin2_2 fiunin2_3 cin wcel fiunin2_0 fiunin2_1 wrex iiunin2_0 cv fiunin2_2 wcel iiunin2_0 cv fiunin2_0 fiunin2_1 fiunin2_3 ciun wcel wa iiunin2_0 cv fiunin2_2 wcel iiunin2_0 cv fiunin2_3 wcel fiunin2_0 fiunin2_1 r19.42v iiunin2_0 cv fiunin2_2 fiunin2_3 cin wcel iiunin2_0 cv fiunin2_2 wcel iiunin2_0 cv fiunin2_3 wcel wa fiunin2_0 fiunin2_1 iiunin2_0 cv fiunin2_2 fiunin2_3 elin rexbii iiunin2_0 cv fiunin2_0 fiunin2_1 fiunin2_3 ciun wcel iiunin2_0 cv fiunin2_3 wcel fiunin2_0 fiunin2_1 wrex iiunin2_0 cv fiunin2_2 wcel fiunin2_0 iiunin2_0 cv fiunin2_1 fiunin2_3 eliun anbi2i 3bitr4i fiunin2_0 iiunin2_0 cv fiunin2_1 fiunin2_2 fiunin2_3 cin eliun iiunin2_0 cv fiunin2_2 fiunin2_0 fiunin2_1 fiunin2_3 ciun elin 3bitr4i eqriv $.
$}
$( Indexed union of intersection.  Generalization of half of theorem
       "Distributive laws" in [Enderton] p. 30.  Use ~ uniiun to recover
       Enderton's theorem.  (Contributed by Mario Carneiro, 30-Aug-2015.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$d x B $.
	fiunin1_0 $f set x $.
	fiunin1_1 $f class A $.
	fiunin1_2 $f class B $.
	fiunin1_3 $f class C $.
	iunin1 $p |- U_ x e. A ( C i^i B ) = ( U_ x e. A C i^i B ) $= fiunin1_0 fiunin1_1 fiunin1_2 fiunin1_3 cin ciun fiunin1_2 fiunin1_0 fiunin1_1 fiunin1_3 ciun cin fiunin1_0 fiunin1_1 fiunin1_3 fiunin1_2 cin ciun fiunin1_0 fiunin1_1 fiunin1_3 ciun fiunin1_2 cin fiunin1_0 fiunin1_1 fiunin1_2 fiunin1_3 iunin2 fiunin1_0 fiunin1_1 fiunin1_3 fiunin1_2 cin fiunin1_2 fiunin1_3 cin fiunin1_3 fiunin1_2 cin fiunin1_2 fiunin1_3 cin wceq fiunin1_0 cv fiunin1_1 wcel fiunin1_3 fiunin1_2 incom a1i iuneq2i fiunin1_0 fiunin1_1 fiunin1_3 ciun fiunin1_2 incom 3eqtr4i $.
$}
$( Indexed intersection of union.  Generalization of half of theorem
       "Distributive laws" in [Enderton] p. 30.  Use ~ intiin to recover
       Enderton's theorem.  (Contributed by NM, 19-Aug-2004.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$d y A $.
	$d x y B $.
	$d y C $.
	iiinun2_0 $f set y $.
	fiinun2_0 $f set x $.
	fiinun2_1 $f class A $.
	fiinun2_2 $f class B $.
	fiinun2_3 $f class C $.
	iinun2 $p |- |^|_ x e. A ( B u. C ) = ( B u. |^|_ x e. A C ) $= iiinun2_0 fiinun2_0 fiinun2_1 fiinun2_2 fiinun2_3 cun ciin fiinun2_2 fiinun2_0 fiinun2_1 fiinun2_3 ciin cun iiinun2_0 cv fiinun2_2 fiinun2_3 cun wcel fiinun2_0 fiinun2_1 wral iiinun2_0 cv fiinun2_2 wcel iiinun2_0 cv fiinun2_0 fiinun2_1 fiinun2_3 ciin wcel wo iiinun2_0 cv fiinun2_0 fiinun2_1 fiinun2_2 fiinun2_3 cun ciin wcel iiinun2_0 cv fiinun2_2 fiinun2_0 fiinun2_1 fiinun2_3 ciin cun wcel iiinun2_0 cv fiinun2_2 wcel iiinun2_0 cv fiinun2_3 wcel wo fiinun2_0 fiinun2_1 wral iiinun2_0 cv fiinun2_2 wcel iiinun2_0 cv fiinun2_3 wcel fiinun2_0 fiinun2_1 wral wo iiinun2_0 cv fiinun2_2 fiinun2_3 cun wcel fiinun2_0 fiinun2_1 wral iiinun2_0 cv fiinun2_2 wcel iiinun2_0 cv fiinun2_0 fiinun2_1 fiinun2_3 ciin wcel wo iiinun2_0 cv fiinun2_2 wcel iiinun2_0 cv fiinun2_3 wcel fiinun2_0 fiinun2_1 r19.32v iiinun2_0 cv fiinun2_2 fiinun2_3 cun wcel iiinun2_0 cv fiinun2_2 wcel iiinun2_0 cv fiinun2_3 wcel wo fiinun2_0 fiinun2_1 iiinun2_0 cv fiinun2_2 fiinun2_3 elun ralbii iiinun2_0 cv fiinun2_0 fiinun2_1 fiinun2_3 ciin wcel iiinun2_0 cv fiinun2_3 wcel fiinun2_0 fiinun2_1 wral iiinun2_0 cv fiinun2_2 wcel iiinun2_0 cv cvv wcel iiinun2_0 cv fiinun2_0 fiinun2_1 fiinun2_3 ciin wcel iiinun2_0 cv fiinun2_3 wcel fiinun2_0 fiinun2_1 wral wb iiinun2_0 vex fiinun2_0 iiinun2_0 cv fiinun2_1 fiinun2_3 cvv eliin ax-mp orbi2i 3bitr4i iiinun2_0 cv cvv wcel iiinun2_0 cv fiinun2_0 fiinun2_1 fiinun2_2 fiinun2_3 cun ciin wcel iiinun2_0 cv fiinun2_2 fiinun2_3 cun wcel fiinun2_0 fiinun2_1 wral wb iiinun2_0 vex fiinun2_0 iiinun2_0 cv fiinun2_1 fiinun2_2 fiinun2_3 cun cvv eliin ax-mp iiinun2_0 cv fiinun2_2 fiinun2_0 fiinun2_1 fiinun2_3 ciin elun 3bitr4i eqriv $.
$}
$( Indexed union of class difference.  Generalization of half of theorem
       "De Morgan's laws" in [Enderton] p. 31.  Use ~ intiin to recover
       Enderton's theorem.  (Contributed by NM, 19-Aug-2004.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$d y A $.
	$d x y B $.
	$d y C $.
	iiundif2_0 $f set y $.
	fiundif2_0 $f set x $.
	fiundif2_1 $f class A $.
	fiundif2_2 $f class B $.
	fiundif2_3 $f class C $.
	iundif2 $p |- U_ x e. A ( B \ C ) = ( B \ |^|_ x e. A C ) $= iiundif2_0 fiundif2_0 fiundif2_1 fiundif2_2 fiundif2_3 cdif ciun fiundif2_2 fiundif2_0 fiundif2_1 fiundif2_3 ciin cdif iiundif2_0 cv fiundif2_2 fiundif2_3 cdif wcel fiundif2_0 fiundif2_1 wrex iiundif2_0 cv fiundif2_2 wcel iiundif2_0 cv fiundif2_0 fiundif2_1 fiundif2_3 ciin wcel wn wa iiundif2_0 cv fiundif2_0 fiundif2_1 fiundif2_2 fiundif2_3 cdif ciun wcel iiundif2_0 cv fiundif2_2 fiundif2_0 fiundif2_1 fiundif2_3 ciin cdif wcel iiundif2_0 cv fiundif2_2 fiundif2_3 cdif wcel fiundif2_0 fiundif2_1 wrex iiundif2_0 cv fiundif2_2 wcel iiundif2_0 cv fiundif2_3 wcel wn wa fiundif2_0 fiundif2_1 wrex iiundif2_0 cv fiundif2_2 wcel iiundif2_0 cv fiundif2_3 wcel wn fiundif2_0 fiundif2_1 wrex wa iiundif2_0 cv fiundif2_2 wcel iiundif2_0 cv fiundif2_0 fiundif2_1 fiundif2_3 ciin wcel wn wa iiundif2_0 cv fiundif2_2 fiundif2_3 cdif wcel iiundif2_0 cv fiundif2_2 wcel iiundif2_0 cv fiundif2_3 wcel wn wa fiundif2_0 fiundif2_1 iiundif2_0 cv fiundif2_2 fiundif2_3 eldif rexbii iiundif2_0 cv fiundif2_2 wcel iiundif2_0 cv fiundif2_3 wcel wn fiundif2_0 fiundif2_1 r19.42v iiundif2_0 cv fiundif2_3 wcel wn fiundif2_0 fiundif2_1 wrex iiundif2_0 cv fiundif2_0 fiundif2_1 fiundif2_3 ciin wcel wn iiundif2_0 cv fiundif2_2 wcel iiundif2_0 cv fiundif2_3 wcel wn fiundif2_0 fiundif2_1 wrex iiundif2_0 cv fiundif2_3 wcel fiundif2_0 fiundif2_1 wral iiundif2_0 cv fiundif2_0 fiundif2_1 fiundif2_3 ciin wcel iiundif2_0 cv fiundif2_3 wcel fiundif2_0 fiundif2_1 rexnal iiundif2_0 cv cvv wcel iiundif2_0 cv fiundif2_0 fiundif2_1 fiundif2_3 ciin wcel iiundif2_0 cv fiundif2_3 wcel fiundif2_0 fiundif2_1 wral wb iiundif2_0 vex fiundif2_0 iiundif2_0 cv fiundif2_1 fiundif2_3 cvv eliin ax-mp xchbinxr anbi2i 3bitri fiundif2_0 iiundif2_0 cv fiundif2_1 fiundif2_2 fiundif2_3 cdif eliun iiundif2_0 cv fiundif2_2 fiundif2_0 fiundif2_1 fiundif2_3 ciin eldif 3bitr4i eqriv $.
$}
$( Rearrange indexed unions over intersection.  (Contributed by NM,
       18-Dec-2008.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$d x B $.
	$d y C $.
	$d x D $.
	$d x y $.
	f2iunin_0 $f set x $.
	f2iunin_1 $f set y $.
	f2iunin_2 $f class A $.
	f2iunin_3 $f class B $.
	f2iunin_4 $f class C $.
	f2iunin_5 $f class D $.
	2iunin $p |- U_ x e. A U_ y e. B ( C i^i D ) = ( U_ x e. A C i^i U_ y e. B D ) $= f2iunin_0 f2iunin_2 f2iunin_1 f2iunin_3 f2iunin_4 f2iunin_5 cin ciun ciun f2iunin_0 f2iunin_2 f2iunin_4 f2iunin_1 f2iunin_3 f2iunin_5 ciun cin ciun f2iunin_0 f2iunin_2 f2iunin_4 ciun f2iunin_1 f2iunin_3 f2iunin_5 ciun cin f2iunin_0 f2iunin_2 f2iunin_1 f2iunin_3 f2iunin_4 f2iunin_5 cin ciun f2iunin_4 f2iunin_1 f2iunin_3 f2iunin_5 ciun cin f2iunin_1 f2iunin_3 f2iunin_4 f2iunin_5 cin ciun f2iunin_4 f2iunin_1 f2iunin_3 f2iunin_5 ciun cin wceq f2iunin_0 cv f2iunin_2 wcel f2iunin_1 f2iunin_3 f2iunin_4 f2iunin_5 iunin2 a1i iuneq2i f2iunin_0 f2iunin_2 f2iunin_1 f2iunin_3 f2iunin_5 ciun f2iunin_4 iunin1 eqtri $.
$}
$( Indexed intersection of class difference.  Generalization of half of
       theorem "De Morgan's laws" in [Enderton] p. 31.  Use ~ uniiun to recover
       Enderton's theorem.  (Contributed by NM, 5-Oct-2006.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$d x y A $.
	$d x y B $.
	$d y C $.
	iiindif2_0 $f set y $.
	fiindif2_0 $f set x $.
	fiindif2_1 $f class A $.
	fiindif2_2 $f class B $.
	fiindif2_3 $f class C $.
	iindif2 $p |- ( A =/= (/) -> |^|_ x e. A ( B \ C ) = ( B \ U_ x e. A C ) ) $= fiindif2_1 c0 wne iiindif2_0 fiindif2_0 fiindif2_1 fiindif2_2 fiindif2_3 cdif ciin fiindif2_2 fiindif2_0 fiindif2_1 fiindif2_3 ciun cdif fiindif2_1 c0 wne iiindif2_0 cv fiindif2_2 fiindif2_3 cdif wcel fiindif2_0 fiindif2_1 wral iiindif2_0 cv fiindif2_2 wcel iiindif2_0 cv fiindif2_0 fiindif2_1 fiindif2_3 ciun wcel wn wa iiindif2_0 cv fiindif2_0 fiindif2_1 fiindif2_2 fiindif2_3 cdif ciin wcel iiindif2_0 cv fiindif2_2 fiindif2_0 fiindif2_1 fiindif2_3 ciun cdif wcel fiindif2_1 c0 wne iiindif2_0 cv fiindif2_2 wcel iiindif2_0 cv fiindif2_3 wcel wn wa fiindif2_0 fiindif2_1 wral iiindif2_0 cv fiindif2_2 wcel iiindif2_0 cv fiindif2_3 wcel wn fiindif2_0 fiindif2_1 wral wa iiindif2_0 cv fiindif2_2 fiindif2_3 cdif wcel fiindif2_0 fiindif2_1 wral iiindif2_0 cv fiindif2_2 wcel iiindif2_0 cv fiindif2_0 fiindif2_1 fiindif2_3 ciun wcel wn wa iiindif2_0 cv fiindif2_2 wcel iiindif2_0 cv fiindif2_3 wcel wn fiindif2_0 fiindif2_1 r19.28zv iiindif2_0 cv fiindif2_2 wcel iiindif2_0 cv fiindif2_3 wcel wn wa iiindif2_0 cv fiindif2_2 fiindif2_3 cdif wcel fiindif2_0 fiindif2_1 iiindif2_0 cv fiindif2_2 fiindif2_3 cdif wcel iiindif2_0 cv fiindif2_2 wcel iiindif2_0 cv fiindif2_3 wcel wn wa iiindif2_0 cv fiindif2_2 fiindif2_3 eldif bicomi ralbii iiindif2_0 cv fiindif2_3 wcel wn fiindif2_0 fiindif2_1 wral iiindif2_0 cv fiindif2_0 fiindif2_1 fiindif2_3 ciun wcel wn iiindif2_0 cv fiindif2_2 wcel iiindif2_0 cv fiindif2_3 wcel wn fiindif2_0 fiindif2_1 wral iiindif2_0 cv fiindif2_3 wcel fiindif2_0 fiindif2_1 wrex iiindif2_0 cv fiindif2_0 fiindif2_1 fiindif2_3 ciun wcel iiindif2_0 cv fiindif2_3 wcel fiindif2_0 fiindif2_1 ralnex fiindif2_0 iiindif2_0 cv fiindif2_1 fiindif2_3 eliun xchbinxr anbi2i 3bitr3g iiindif2_0 cv cvv wcel iiindif2_0 cv fiindif2_0 fiindif2_1 fiindif2_2 fiindif2_3 cdif ciin wcel iiindif2_0 cv fiindif2_2 fiindif2_3 cdif wcel fiindif2_0 fiindif2_1 wral wb iiindif2_0 vex fiindif2_0 iiindif2_0 cv fiindif2_1 fiindif2_2 fiindif2_3 cdif cvv eliin ax-mp iiindif2_0 cv fiindif2_2 fiindif2_0 fiindif2_1 fiindif2_3 ciun eldif 3bitr4g eqrdv $.
$}
$( Indexed intersection of intersection.  Generalization of half of theorem
       "Distributive laws" in [Enderton] p. 30.  Use ~ intiin to recover
       Enderton's theorem.  (Contributed by Mario Carneiro, 19-Mar-2015.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$d x y A $.
	$d x y B $.
	$d y C $.
	iiinin2_0 $f set y $.
	fiinin2_0 $f set x $.
	fiinin2_1 $f class A $.
	fiinin2_2 $f class B $.
	fiinin2_3 $f class C $.
	iinin2 $p |- ( A =/= (/) -> |^|_ x e. A ( B i^i C ) = ( B i^i |^|_ x e. A C ) ) $= fiinin2_1 c0 wne iiinin2_0 fiinin2_0 fiinin2_1 fiinin2_2 fiinin2_3 cin ciin fiinin2_2 fiinin2_0 fiinin2_1 fiinin2_3 ciin cin fiinin2_1 c0 wne iiinin2_0 cv fiinin2_2 fiinin2_3 cin wcel fiinin2_0 fiinin2_1 wral iiinin2_0 cv fiinin2_2 wcel iiinin2_0 cv fiinin2_0 fiinin2_1 fiinin2_3 ciin wcel wa iiinin2_0 cv fiinin2_0 fiinin2_1 fiinin2_2 fiinin2_3 cin ciin wcel iiinin2_0 cv fiinin2_2 fiinin2_0 fiinin2_1 fiinin2_3 ciin cin wcel fiinin2_1 c0 wne iiinin2_0 cv fiinin2_2 wcel iiinin2_0 cv fiinin2_3 wcel wa fiinin2_0 fiinin2_1 wral iiinin2_0 cv fiinin2_2 wcel iiinin2_0 cv fiinin2_3 wcel fiinin2_0 fiinin2_1 wral wa iiinin2_0 cv fiinin2_2 fiinin2_3 cin wcel fiinin2_0 fiinin2_1 wral iiinin2_0 cv fiinin2_2 wcel iiinin2_0 cv fiinin2_0 fiinin2_1 fiinin2_3 ciin wcel wa iiinin2_0 cv fiinin2_2 wcel iiinin2_0 cv fiinin2_3 wcel fiinin2_0 fiinin2_1 r19.28zv iiinin2_0 cv fiinin2_2 fiinin2_3 cin wcel iiinin2_0 cv fiinin2_2 wcel iiinin2_0 cv fiinin2_3 wcel wa fiinin2_0 fiinin2_1 iiinin2_0 cv fiinin2_2 fiinin2_3 elin ralbii iiinin2_0 cv fiinin2_0 fiinin2_1 fiinin2_3 ciin wcel iiinin2_0 cv fiinin2_3 wcel fiinin2_0 fiinin2_1 wral iiinin2_0 cv fiinin2_2 wcel iiinin2_0 cv cvv wcel iiinin2_0 cv fiinin2_0 fiinin2_1 fiinin2_3 ciin wcel iiinin2_0 cv fiinin2_3 wcel fiinin2_0 fiinin2_1 wral wb iiinin2_0 vex fiinin2_0 iiinin2_0 cv fiinin2_1 fiinin2_3 cvv eliin ax-mp anbi2i 3bitr4g iiinin2_0 cv cvv wcel iiinin2_0 cv fiinin2_0 fiinin2_1 fiinin2_2 fiinin2_3 cin ciin wcel iiinin2_0 cv fiinin2_2 fiinin2_3 cin wcel fiinin2_0 fiinin2_1 wral wb iiinin2_0 vex fiinin2_0 iiinin2_0 cv fiinin2_1 fiinin2_2 fiinin2_3 cin cvv eliin ax-mp iiinin2_0 cv fiinin2_2 fiinin2_0 fiinin2_1 fiinin2_3 ciin elin 3bitr4g eqrdv $.
$}
$( Indexed intersection of intersection.  Generalization of half of theorem
       "Distributive laws" in [Enderton] p. 30.  Use ~ intiin to recover
       Enderton's theorem.  (Contributed by Mario Carneiro, 19-Mar-2015.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$d x A $.
	$d x B $.
	fiinin1_0 $f set x $.
	fiinin1_1 $f class A $.
	fiinin1_2 $f class B $.
	fiinin1_3 $f class C $.
	iinin1 $p |- ( A =/= (/) -> |^|_ x e. A ( C i^i B ) = ( |^|_ x e. A C i^i B ) ) $= fiinin1_1 c0 wne fiinin1_0 fiinin1_1 fiinin1_2 fiinin1_3 cin ciin fiinin1_2 fiinin1_0 fiinin1_1 fiinin1_3 ciin cin fiinin1_0 fiinin1_1 fiinin1_3 fiinin1_2 cin ciin fiinin1_0 fiinin1_1 fiinin1_3 ciin fiinin1_2 cin fiinin1_0 fiinin1_1 fiinin1_2 fiinin1_3 iinin2 fiinin1_0 fiinin1_1 fiinin1_3 fiinin1_2 cin fiinin1_2 fiinin1_3 cin fiinin1_3 fiinin1_2 cin fiinin1_2 fiinin1_3 cin wceq fiinin1_0 cv fiinin1_1 wcel fiinin1_3 fiinin1_2 incom a1i iineq2i fiinin1_0 fiinin1_1 fiinin1_3 ciin fiinin1_2 incom 3eqtr4g $.
$}
$( Elementhood in a relative intersection.  (Contributed by Mario Carneiro,
       30-Dec-2016.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v S $.
	$v X $.
	$d A x $.
	$d X x $.
	$d B x $.
	felriin_0 $f set x $.
	felriin_1 $f class A $.
	felriin_2 $f class B $.
	felriin_3 $f class S $.
	felriin_4 $f class X $.
	elriin $p |- ( B e. ( A i^i |^|_ x e. X S ) <-> ( B e. A /\ A. x e. X B e. S ) ) $= felriin_2 felriin_1 felriin_0 felriin_4 felriin_3 ciin cin wcel felriin_2 felriin_1 wcel felriin_2 felriin_0 felriin_4 felriin_3 ciin wcel wa felriin_2 felriin_1 wcel felriin_2 felriin_3 wcel felriin_0 felriin_4 wral wa felriin_2 felriin_1 felriin_0 felriin_4 felriin_3 ciin elin felriin_2 felriin_1 wcel felriin_2 felriin_0 felriin_4 felriin_3 ciin wcel felriin_2 felriin_3 wcel felriin_0 felriin_4 wral felriin_0 felriin_2 felriin_4 felriin_3 felriin_1 eliin pm5.32i bitri $.
$}
$( Relative intersection of an empty family.  (Contributed by Stefan
       O'Rear, 3-Apr-2015.) $)
${
	$v x $.
	$v A $.
	$v S $.
	$v X $.
	$d A x $.
	$d X x $.
	friin0_0 $f set x $.
	friin0_1 $f class A $.
	friin0_2 $f class S $.
	friin0_3 $f class X $.
	riin0 $p |- ( X = (/) -> ( A i^i |^|_ x e. X S ) = A ) $= friin0_3 c0 wceq friin0_1 friin0_0 friin0_3 friin0_2 ciin cin friin0_1 friin0_0 c0 friin0_2 ciin cin friin0_1 friin0_3 c0 wceq friin0_0 friin0_3 friin0_2 ciin friin0_0 c0 friin0_2 ciin friin0_1 friin0_0 friin0_3 c0 friin0_2 iineq1 ineq2d friin0_1 friin0_0 c0 friin0_2 ciin cin friin0_1 cvv cin friin0_1 friin0_0 c0 friin0_2 ciin cvv friin0_1 friin0_0 friin0_2 0iin ineq2i friin0_1 inv1 eqtri syl6eq $.
$}
$( Relative intersection of a nonempty family.  (Contributed by Stefan
       O'Rear, 3-Apr-2015.) $)
${
	$v x $.
	$v A $.
	$v S $.
	$v X $.
	$d A x $.
	$d X x $.
	friinn0_0 $f set x $.
	friinn0_1 $f class A $.
	friinn0_2 $f class S $.
	friinn0_3 $f class X $.
	riinn0 $p |- ( ( A. x e. X S C_ A /\ X =/= (/) ) -> ( A i^i |^|_ x e. X S ) = |^|_ x e. X S ) $= friinn0_2 friinn0_1 wss friinn0_0 friinn0_3 wral friinn0_3 c0 wne wa friinn0_1 friinn0_0 friinn0_3 friinn0_2 ciin cin friinn0_0 friinn0_3 friinn0_2 ciin friinn0_1 cin friinn0_0 friinn0_3 friinn0_2 ciin friinn0_1 friinn0_0 friinn0_3 friinn0_2 ciin incom friinn0_2 friinn0_1 wss friinn0_0 friinn0_3 wral friinn0_3 c0 wne wa friinn0_0 friinn0_3 friinn0_2 ciin friinn0_1 wss friinn0_0 friinn0_3 friinn0_2 ciin friinn0_1 cin friinn0_0 friinn0_3 friinn0_2 ciin wceq friinn0_2 friinn0_1 wss friinn0_0 friinn0_3 wral friinn0_3 c0 wne wa friinn0_2 friinn0_1 wss friinn0_0 friinn0_3 wrex friinn0_0 friinn0_3 friinn0_2 ciin friinn0_1 wss friinn0_3 c0 wne friinn0_2 friinn0_1 wss friinn0_0 friinn0_3 wral friinn0_2 friinn0_1 wss friinn0_0 friinn0_3 wrex friinn0_2 friinn0_1 wss friinn0_0 friinn0_3 r19.2z ancoms friinn0_0 friinn0_3 friinn0_2 friinn0_1 iinss syl friinn0_0 friinn0_3 friinn0_2 ciin friinn0_1 df-ss sylib syl5eq $.
$}
$( Relative intersection of a relative abstraction.  (Contributed by Stefan
       O'Rear, 3-Apr-2015.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v A $.
	$v X $.
	$d A x y $.
	$d X x y $.
	friinrab_0 $f wff ph $.
	friinrab_1 $f set x $.
	friinrab_2 $f set y $.
	friinrab_3 $f class A $.
	friinrab_4 $f class X $.
	riinrab $p |- ( A i^i |^|_ x e. X { y e. A | ph } ) = { y e. A | A. x e. X ph } $= friinrab_3 friinrab_1 friinrab_4 friinrab_0 friinrab_2 friinrab_3 crab ciin cin friinrab_0 friinrab_1 friinrab_4 wral friinrab_2 friinrab_3 crab wceq friinrab_4 c0 friinrab_4 c0 wceq friinrab_3 friinrab_1 friinrab_4 friinrab_0 friinrab_2 friinrab_3 crab ciin cin friinrab_3 friinrab_0 friinrab_1 friinrab_4 wral friinrab_2 friinrab_3 crab friinrab_1 friinrab_3 friinrab_0 friinrab_2 friinrab_3 crab friinrab_4 riin0 friinrab_4 c0 wceq friinrab_0 friinrab_1 friinrab_4 wral friinrab_2 friinrab_3 wral friinrab_3 friinrab_0 friinrab_1 friinrab_4 wral friinrab_2 friinrab_3 crab wceq friinrab_4 c0 wceq friinrab_0 friinrab_1 friinrab_4 wral friinrab_2 friinrab_3 friinrab_0 friinrab_1 friinrab_4 rzal ralrimivw friinrab_0 friinrab_1 friinrab_4 wral friinrab_2 friinrab_3 rabid2 sylibr eqtrd friinrab_4 c0 wne friinrab_3 friinrab_1 friinrab_4 friinrab_0 friinrab_2 friinrab_3 crab ciin cin friinrab_1 friinrab_4 friinrab_0 friinrab_2 friinrab_3 crab ciin friinrab_0 friinrab_1 friinrab_4 wral friinrab_2 friinrab_3 crab friinrab_0 friinrab_2 friinrab_3 crab friinrab_3 wss friinrab_1 friinrab_4 wral friinrab_4 c0 wne friinrab_3 friinrab_1 friinrab_4 friinrab_0 friinrab_2 friinrab_3 crab ciin cin friinrab_1 friinrab_4 friinrab_0 friinrab_2 friinrab_3 crab ciin wceq friinrab_0 friinrab_2 friinrab_3 crab friinrab_3 wss friinrab_1 friinrab_4 friinrab_0 friinrab_2 friinrab_3 ssrab2 rgenw friinrab_1 friinrab_3 friinrab_0 friinrab_2 friinrab_3 crab friinrab_4 riinn0 mpan friinrab_0 friinrab_1 friinrab_2 friinrab_4 friinrab_3 iinrab eqtrd pm2.61ine $.
$}
$( A singleton index picks out an instance of an indexed intersection's
       argument.  (Contributed by NM, 15-Jan-2012.)  (Proof shortened by Mario
       Carneiro, 17-Nov-2016.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$v V $.
	$d x y A $.
	$d y B $.
	$d x y C $.
	$d y V $.
	iiinxsng_0 $f set y $.
	fiinxsng_0 $f set x $.
	fiinxsng_1 $f class A $.
	fiinxsng_2 $f class B $.
	fiinxsng_3 $f class C $.
	fiinxsng_4 $f class V $.
	eiinxsng_0 $e |- ( x = A -> B = C ) $.
	iinxsng $p |- ( A e. V -> |^|_ x e. { A } B = C ) $= fiinxsng_1 fiinxsng_4 wcel fiinxsng_0 fiinxsng_1 csn fiinxsng_2 ciin iiinxsng_0 cv fiinxsng_2 wcel fiinxsng_0 fiinxsng_1 csn wral iiinxsng_0 cab fiinxsng_3 fiinxsng_0 iiinxsng_0 fiinxsng_1 csn fiinxsng_2 df-iin fiinxsng_1 fiinxsng_4 wcel iiinxsng_0 cv fiinxsng_2 wcel fiinxsng_0 fiinxsng_1 csn wral iiinxsng_0 fiinxsng_3 iiinxsng_0 cv fiinxsng_2 wcel iiinxsng_0 cv fiinxsng_3 wcel fiinxsng_0 fiinxsng_1 fiinxsng_4 fiinxsng_0 cv fiinxsng_1 wceq fiinxsng_2 fiinxsng_3 iiinxsng_0 cv eiinxsng_0 eleq2d ralsng abbi1dv syl5eq $.
$}
$( Indexed intersection with an unordered pair index.  (Contributed by NM,
       25-Jan-2012.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v E $.
	$v V $.
	$v W $.
	$d x y A $.
	$d x y B $.
	$d y C $.
	$d x y D $.
	$d x y E $.
	$d y V $.
	$d y W $.
	iiinxprg_0 $f set y $.
	fiinxprg_0 $f set x $.
	fiinxprg_1 $f class A $.
	fiinxprg_2 $f class B $.
	fiinxprg_3 $f class C $.
	fiinxprg_4 $f class D $.
	fiinxprg_5 $f class E $.
	fiinxprg_6 $f class V $.
	fiinxprg_7 $f class W $.
	eiinxprg_0 $e |- ( x = A -> C = D ) $.
	eiinxprg_1 $e |- ( x = B -> C = E ) $.
	iinxprg $p |- ( ( A e. V /\ B e. W ) -> |^|_ x e. { A , B } C = ( D i^i E ) ) $= fiinxprg_1 fiinxprg_6 wcel fiinxprg_2 fiinxprg_7 wcel wa iiinxprg_0 cv fiinxprg_3 wcel fiinxprg_0 fiinxprg_1 fiinxprg_2 cpr wral iiinxprg_0 cab iiinxprg_0 cv fiinxprg_4 wcel iiinxprg_0 cv fiinxprg_5 wcel wa iiinxprg_0 cab fiinxprg_0 fiinxprg_1 fiinxprg_2 cpr fiinxprg_3 ciin fiinxprg_4 fiinxprg_5 cin fiinxprg_1 fiinxprg_6 wcel fiinxprg_2 fiinxprg_7 wcel wa iiinxprg_0 cv fiinxprg_3 wcel fiinxprg_0 fiinxprg_1 fiinxprg_2 cpr wral iiinxprg_0 cv fiinxprg_4 wcel iiinxprg_0 cv fiinxprg_5 wcel wa iiinxprg_0 iiinxprg_0 cv fiinxprg_3 wcel iiinxprg_0 cv fiinxprg_4 wcel iiinxprg_0 cv fiinxprg_5 wcel fiinxprg_0 fiinxprg_1 fiinxprg_2 fiinxprg_6 fiinxprg_7 fiinxprg_0 cv fiinxprg_1 wceq fiinxprg_3 fiinxprg_4 iiinxprg_0 cv eiinxprg_0 eleq2d fiinxprg_0 cv fiinxprg_2 wceq fiinxprg_3 fiinxprg_5 iiinxprg_0 cv eiinxprg_1 eleq2d ralprg abbidv fiinxprg_0 iiinxprg_0 fiinxprg_1 fiinxprg_2 cpr fiinxprg_3 df-iin iiinxprg_0 fiinxprg_4 fiinxprg_5 df-in 3eqtr4g $.
$}
$( A singleton index picks out an instance of an indexed union's argument.
       (Contributed by Mario Carneiro, 25-Jun-2016.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$v V $.
	$d x y A $.
	$d y B $.
	$d x y C $.
	$d y V $.
	iiunxsng_0 $f set y $.
	fiunxsng_0 $f set x $.
	fiunxsng_1 $f class A $.
	fiunxsng_2 $f class B $.
	fiunxsng_3 $f class C $.
	fiunxsng_4 $f class V $.
	eiunxsng_0 $e |- ( x = A -> B = C ) $.
	iunxsng $p |- ( A e. V -> U_ x e. { A } B = C ) $= fiunxsng_1 fiunxsng_4 wcel iiunxsng_0 fiunxsng_0 fiunxsng_1 csn fiunxsng_2 ciun fiunxsng_3 iiunxsng_0 cv fiunxsng_0 fiunxsng_1 csn fiunxsng_2 ciun wcel iiunxsng_0 cv fiunxsng_2 wcel fiunxsng_0 fiunxsng_1 csn wrex fiunxsng_1 fiunxsng_4 wcel iiunxsng_0 cv fiunxsng_3 wcel fiunxsng_0 iiunxsng_0 cv fiunxsng_1 csn fiunxsng_2 eliun iiunxsng_0 cv fiunxsng_2 wcel iiunxsng_0 cv fiunxsng_3 wcel fiunxsng_0 fiunxsng_1 fiunxsng_4 fiunxsng_0 cv fiunxsng_1 wceq fiunxsng_2 fiunxsng_3 iiunxsng_0 cv eiunxsng_0 eleq2d rexsng syl5bb eqrdv $.
$}
$( A singleton index picks out an instance of an indexed union's argument.
       (Contributed by NM, 26-Mar-2004.)  (Proof shortened by Mario Carneiro,
       25-Jun-2016.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$d x A $.
	$d x C $.
	fiunxsn_0 $f set x $.
	fiunxsn_1 $f class A $.
	fiunxsn_2 $f class B $.
	fiunxsn_3 $f class C $.
	eiunxsn_0 $e |- A e. _V $.
	eiunxsn_1 $e |- ( x = A -> B = C ) $.
	iunxsn $p |- U_ x e. { A } B = C $= fiunxsn_1 cvv wcel fiunxsn_0 fiunxsn_1 csn fiunxsn_2 ciun fiunxsn_3 wceq eiunxsn_0 fiunxsn_0 fiunxsn_1 fiunxsn_2 fiunxsn_3 cvv eiunxsn_1 iunxsng ax-mp $.
$}
$( Separate a union in an indexed union.  (Contributed by NM,
       27-Dec-2004.)  (Proof shortened by Mario Carneiro, 17-Nov-2016.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$d x y $.
	$d y A $.
	$d y B $.
	$d y C $.
	iiunun_0 $f set y $.
	fiunun_0 $f set x $.
	fiunun_1 $f class A $.
	fiunun_2 $f class B $.
	fiunun_3 $f class C $.
	iunun $p |- U_ x e. A ( B u. C ) = ( U_ x e. A B u. U_ x e. A C ) $= iiunun_0 fiunun_0 fiunun_1 fiunun_2 fiunun_3 cun ciun fiunun_0 fiunun_1 fiunun_2 ciun fiunun_0 fiunun_1 fiunun_3 ciun cun iiunun_0 cv fiunun_2 fiunun_3 cun wcel fiunun_0 fiunun_1 wrex iiunun_0 cv fiunun_0 fiunun_1 fiunun_2 ciun wcel iiunun_0 cv fiunun_0 fiunun_1 fiunun_3 ciun wcel wo iiunun_0 cv fiunun_0 fiunun_1 fiunun_2 fiunun_3 cun ciun wcel iiunun_0 cv fiunun_0 fiunun_1 fiunun_2 ciun fiunun_0 fiunun_1 fiunun_3 ciun cun wcel iiunun_0 cv fiunun_2 wcel iiunun_0 cv fiunun_3 wcel wo fiunun_0 fiunun_1 wrex iiunun_0 cv fiunun_2 wcel fiunun_0 fiunun_1 wrex iiunun_0 cv fiunun_3 wcel fiunun_0 fiunun_1 wrex wo iiunun_0 cv fiunun_2 fiunun_3 cun wcel fiunun_0 fiunun_1 wrex iiunun_0 cv fiunun_0 fiunun_1 fiunun_2 ciun wcel iiunun_0 cv fiunun_0 fiunun_1 fiunun_3 ciun wcel wo iiunun_0 cv fiunun_2 wcel iiunun_0 cv fiunun_3 wcel fiunun_0 fiunun_1 r19.43 iiunun_0 cv fiunun_2 fiunun_3 cun wcel iiunun_0 cv fiunun_2 wcel iiunun_0 cv fiunun_3 wcel wo fiunun_0 fiunun_1 iiunun_0 cv fiunun_2 fiunun_3 elun rexbii iiunun_0 cv fiunun_0 fiunun_1 fiunun_2 ciun wcel iiunun_0 cv fiunun_2 wcel fiunun_0 fiunun_1 wrex iiunun_0 cv fiunun_0 fiunun_1 fiunun_3 ciun wcel iiunun_0 cv fiunun_3 wcel fiunun_0 fiunun_1 wrex fiunun_0 iiunun_0 cv fiunun_1 fiunun_2 eliun fiunun_0 iiunun_0 cv fiunun_1 fiunun_3 eliun orbi12i 3bitr4i fiunun_0 iiunun_0 cv fiunun_1 fiunun_2 fiunun_3 cun eliun iiunun_0 cv fiunun_0 fiunun_1 fiunun_2 ciun fiunun_0 fiunun_1 fiunun_3 ciun elun 3bitr4i eqriv $.
$}
$( Separate a union in the index of an indexed union.  (Contributed by NM,
       26-Mar-2004.)  (Proof shortened by Mario Carneiro, 17-Nov-2016.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$d x y $.
	$d y A $.
	$d y B $.
	$d y C $.
	iiunxun_0 $f set y $.
	fiunxun_0 $f set x $.
	fiunxun_1 $f class A $.
	fiunxun_2 $f class B $.
	fiunxun_3 $f class C $.
	iunxun $p |- U_ x e. ( A u. B ) C = ( U_ x e. A C u. U_ x e. B C ) $= iiunxun_0 fiunxun_0 fiunxun_1 fiunxun_2 cun fiunxun_3 ciun fiunxun_0 fiunxun_1 fiunxun_3 ciun fiunxun_0 fiunxun_2 fiunxun_3 ciun cun iiunxun_0 cv fiunxun_3 wcel fiunxun_0 fiunxun_1 fiunxun_2 cun wrex iiunxun_0 cv fiunxun_0 fiunxun_1 fiunxun_3 ciun wcel iiunxun_0 cv fiunxun_0 fiunxun_2 fiunxun_3 ciun wcel wo iiunxun_0 cv fiunxun_0 fiunxun_1 fiunxun_2 cun fiunxun_3 ciun wcel iiunxun_0 cv fiunxun_0 fiunxun_1 fiunxun_3 ciun fiunxun_0 fiunxun_2 fiunxun_3 ciun cun wcel iiunxun_0 cv fiunxun_3 wcel fiunxun_0 fiunxun_1 fiunxun_2 cun wrex iiunxun_0 cv fiunxun_3 wcel fiunxun_0 fiunxun_1 wrex iiunxun_0 cv fiunxun_3 wcel fiunxun_0 fiunxun_2 wrex wo iiunxun_0 cv fiunxun_0 fiunxun_1 fiunxun_3 ciun wcel iiunxun_0 cv fiunxun_0 fiunxun_2 fiunxun_3 ciun wcel wo iiunxun_0 cv fiunxun_3 wcel fiunxun_0 fiunxun_1 fiunxun_2 rexun iiunxun_0 cv fiunxun_0 fiunxun_1 fiunxun_3 ciun wcel iiunxun_0 cv fiunxun_3 wcel fiunxun_0 fiunxun_1 wrex iiunxun_0 cv fiunxun_0 fiunxun_2 fiunxun_3 ciun wcel iiunxun_0 cv fiunxun_3 wcel fiunxun_0 fiunxun_2 wrex fiunxun_0 iiunxun_0 cv fiunxun_1 fiunxun_3 eliun fiunxun_0 iiunxun_0 cv fiunxun_2 fiunxun_3 eliun orbi12i bitr4i fiunxun_0 iiunxun_0 cv fiunxun_1 fiunxun_2 cun fiunxun_3 eliun iiunxun_0 cv fiunxun_0 fiunxun_1 fiunxun_3 ciun fiunxun_0 fiunxun_2 fiunxun_3 ciun elun 3bitr4i eqriv $.
$}
$( Separate an indexed union in the index of an indexed union.
       (Contributed by Mario Carneiro, 5-Dec-2016.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v A $.
	$v B $.
	$v C $.
	$d x y z $.
	$d x z A $.
	$d z B $.
	$d y z C $.
	iiunxiun_0 $f set z $.
	fiunxiun_0 $f set x $.
	fiunxiun_1 $f set y $.
	fiunxiun_2 $f class A $.
	fiunxiun_3 $f class B $.
	fiunxiun_4 $f class C $.
	iunxiun $p |- U_ x e. U_ y e. A B C = U_ y e. A U_ x e. B C $= iiunxiun_0 fiunxiun_0 fiunxiun_1 fiunxiun_2 fiunxiun_3 ciun fiunxiun_4 ciun fiunxiun_1 fiunxiun_2 fiunxiun_0 fiunxiun_3 fiunxiun_4 ciun ciun iiunxiun_0 cv fiunxiun_4 wcel fiunxiun_0 fiunxiun_1 fiunxiun_2 fiunxiun_3 ciun wrex iiunxiun_0 cv fiunxiun_0 fiunxiun_3 fiunxiun_4 ciun wcel fiunxiun_1 fiunxiun_2 wrex iiunxiun_0 cv fiunxiun_0 fiunxiun_1 fiunxiun_2 fiunxiun_3 ciun fiunxiun_4 ciun wcel iiunxiun_0 cv fiunxiun_1 fiunxiun_2 fiunxiun_0 fiunxiun_3 fiunxiun_4 ciun ciun wcel fiunxiun_0 cv fiunxiun_1 fiunxiun_2 fiunxiun_3 ciun wcel iiunxiun_0 cv fiunxiun_4 wcel wa fiunxiun_0 wex fiunxiun_0 cv fiunxiun_3 wcel iiunxiun_0 cv fiunxiun_4 wcel wa fiunxiun_0 wex fiunxiun_1 fiunxiun_2 wrex iiunxiun_0 cv fiunxiun_4 wcel fiunxiun_0 fiunxiun_1 fiunxiun_2 fiunxiun_3 ciun wrex iiunxiun_0 cv fiunxiun_0 fiunxiun_3 fiunxiun_4 ciun wcel fiunxiun_1 fiunxiun_2 wrex fiunxiun_0 cv fiunxiun_1 fiunxiun_2 fiunxiun_3 ciun wcel iiunxiun_0 cv fiunxiun_4 wcel wa fiunxiun_0 wex fiunxiun_0 cv fiunxiun_3 wcel iiunxiun_0 cv fiunxiun_4 wcel wa fiunxiun_1 fiunxiun_2 wrex fiunxiun_0 wex fiunxiun_0 cv fiunxiun_3 wcel iiunxiun_0 cv fiunxiun_4 wcel wa fiunxiun_0 wex fiunxiun_1 fiunxiun_2 wrex fiunxiun_0 cv fiunxiun_1 fiunxiun_2 fiunxiun_3 ciun wcel iiunxiun_0 cv fiunxiun_4 wcel wa fiunxiun_0 cv fiunxiun_3 wcel iiunxiun_0 cv fiunxiun_4 wcel wa fiunxiun_1 fiunxiun_2 wrex fiunxiun_0 fiunxiun_0 cv fiunxiun_1 fiunxiun_2 fiunxiun_3 ciun wcel iiunxiun_0 cv fiunxiun_4 wcel wa fiunxiun_0 cv fiunxiun_3 wcel fiunxiun_1 fiunxiun_2 wrex iiunxiun_0 cv fiunxiun_4 wcel wa fiunxiun_0 cv fiunxiun_3 wcel iiunxiun_0 cv fiunxiun_4 wcel wa fiunxiun_1 fiunxiun_2 wrex fiunxiun_0 cv fiunxiun_1 fiunxiun_2 fiunxiun_3 ciun wcel fiunxiun_0 cv fiunxiun_3 wcel fiunxiun_1 fiunxiun_2 wrex iiunxiun_0 cv fiunxiun_4 wcel fiunxiun_1 fiunxiun_0 cv fiunxiun_2 fiunxiun_3 eliun anbi1i fiunxiun_0 cv fiunxiun_3 wcel iiunxiun_0 cv fiunxiun_4 wcel fiunxiun_1 fiunxiun_2 r19.41v bitr4i exbii fiunxiun_0 cv fiunxiun_3 wcel iiunxiun_0 cv fiunxiun_4 wcel wa fiunxiun_1 fiunxiun_0 fiunxiun_2 rexcom4 bitr4i iiunxiun_0 cv fiunxiun_4 wcel fiunxiun_0 fiunxiun_1 fiunxiun_2 fiunxiun_3 ciun df-rex iiunxiun_0 cv fiunxiun_0 fiunxiun_3 fiunxiun_4 ciun wcel fiunxiun_0 cv fiunxiun_3 wcel iiunxiun_0 cv fiunxiun_4 wcel wa fiunxiun_0 wex fiunxiun_1 fiunxiun_2 iiunxiun_0 cv fiunxiun_0 fiunxiun_3 fiunxiun_4 ciun wcel iiunxiun_0 cv fiunxiun_4 wcel fiunxiun_0 fiunxiun_3 wrex fiunxiun_0 cv fiunxiun_3 wcel iiunxiun_0 cv fiunxiun_4 wcel wa fiunxiun_0 wex fiunxiun_0 iiunxiun_0 cv fiunxiun_3 fiunxiun_4 eliun iiunxiun_0 cv fiunxiun_4 wcel fiunxiun_0 fiunxiun_3 df-rex bitri rexbii 3bitr4i fiunxiun_0 iiunxiun_0 cv fiunxiun_1 fiunxiun_2 fiunxiun_3 ciun fiunxiun_4 eliun fiunxiun_1 iiunxiun_0 cv fiunxiun_2 fiunxiun_0 fiunxiun_3 fiunxiun_4 ciun eliun 3bitr4i eqriv $.
$}
$( A relationship involving union and indexed intersection.  Exercise 23 of
       [Enderton] p. 33.  (Contributed by NM, 25-Nov-2003.)  (Proof shortened
       by Mario Carneiro, 17-Nov-2016.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$d x y A $.
	$d x y B $.
	iiinuni_0 $f set y $.
	fiinuni_0 $f set x $.
	fiinuni_1 $f class A $.
	fiinuni_2 $f class B $.
	iinuni $p |- ( A u. |^| B ) = |^|_ x e. B ( A u. x ) $= iiinuni_0 cv fiinuni_1 wcel iiinuni_0 cv fiinuni_2 cint wcel wo iiinuni_0 cab iiinuni_0 cv fiinuni_1 fiinuni_0 cv cun wcel fiinuni_0 fiinuni_2 wral iiinuni_0 cab fiinuni_1 fiinuni_2 cint cun fiinuni_0 fiinuni_2 fiinuni_1 fiinuni_0 cv cun ciin iiinuni_0 cv fiinuni_1 wcel iiinuni_0 cv fiinuni_2 cint wcel wo iiinuni_0 cv fiinuni_1 fiinuni_0 cv cun wcel fiinuni_0 fiinuni_2 wral iiinuni_0 iiinuni_0 cv fiinuni_1 wcel iiinuni_0 cv fiinuni_0 cv wcel wo fiinuni_0 fiinuni_2 wral iiinuni_0 cv fiinuni_1 wcel iiinuni_0 cv fiinuni_0 cv wcel fiinuni_0 fiinuni_2 wral wo iiinuni_0 cv fiinuni_1 fiinuni_0 cv cun wcel fiinuni_0 fiinuni_2 wral iiinuni_0 cv fiinuni_1 wcel iiinuni_0 cv fiinuni_2 cint wcel wo iiinuni_0 cv fiinuni_1 wcel iiinuni_0 cv fiinuni_0 cv wcel fiinuni_0 fiinuni_2 r19.32v iiinuni_0 cv fiinuni_1 fiinuni_0 cv cun wcel iiinuni_0 cv fiinuni_1 wcel iiinuni_0 cv fiinuni_0 cv wcel wo fiinuni_0 fiinuni_2 iiinuni_0 cv fiinuni_1 fiinuni_0 cv elun ralbii iiinuni_0 cv fiinuni_2 cint wcel iiinuni_0 cv fiinuni_0 cv wcel fiinuni_0 fiinuni_2 wral iiinuni_0 cv fiinuni_1 wcel fiinuni_0 iiinuni_0 cv fiinuni_2 iiinuni_0 vex elint2 orbi2i 3bitr4ri abbii iiinuni_0 fiinuni_1 fiinuni_2 cint df-un fiinuni_0 iiinuni_0 fiinuni_2 fiinuni_1 fiinuni_0 cv cun df-iin 3eqtr4i $.
$}
$( A relationship involving union and indexed union.  Exercise 25 of
       [Enderton] p. 33.  (Contributed by NM, 25-Nov-2003.)  (Proof shortened
       by Mario Carneiro, 17-Nov-2016.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$d x A $.
	$d x B $.
	fiununi_0 $f set x $.
	fiununi_1 $f class A $.
	fiununi_2 $f class B $.
	iununi $p |- ( ( B = (/) -> A = (/) ) <-> ( A u. U. B ) = U_ x e. B ( A u. x ) ) $= fiununi_2 c0 wceq fiununi_1 c0 wceq wi fiununi_1 fiununi_2 cuni cun fiununi_0 fiununi_2 fiununi_1 fiununi_0 cv cun ciun wceq fiununi_2 c0 wceq fiununi_1 c0 wceq wi fiununi_1 fiununi_0 fiununi_2 fiununi_0 cv ciun cun fiununi_0 fiununi_2 fiununi_1 ciun fiununi_0 fiununi_2 fiununi_0 cv ciun cun fiununi_1 fiununi_2 cuni cun fiununi_0 fiununi_2 fiununi_1 fiununi_0 cv cun ciun fiununi_2 c0 wceq fiununi_1 c0 wceq wi fiununi_1 fiununi_0 fiununi_2 fiununi_1 ciun fiununi_0 fiununi_2 fiununi_0 cv ciun fiununi_2 c0 wceq fiununi_1 c0 wceq wi fiununi_0 fiununi_2 fiununi_1 ciun fiununi_1 fiununi_2 c0 wceq fiununi_1 c0 wceq fiununi_0 fiununi_2 fiununi_1 ciun fiununi_1 wceq fiununi_2 c0 wceq wn fiununi_2 c0 wne fiununi_0 fiununi_2 fiununi_1 ciun fiununi_1 wceq fiununi_2 c0 df-ne fiununi_0 fiununi_2 fiununi_1 iunconst sylbir fiununi_1 c0 wceq fiununi_0 fiununi_2 c0 ciun c0 fiununi_0 fiununi_2 fiununi_1 ciun fiununi_1 fiununi_0 fiununi_2 iun0 fiununi_1 c0 wceq fiununi_0 fiununi_2 fiununi_1 c0 fiununi_1 c0 wceq id iuneq2d fiununi_1 c0 wceq id 3eqtr4a ja eqcomd uneq1d fiununi_2 cuni fiununi_0 fiununi_2 fiununi_0 cv ciun fiununi_1 fiununi_0 fiununi_2 uniiun uneq2i fiununi_0 fiununi_2 fiununi_1 fiununi_0 cv iunun 3eqtr4g fiununi_2 c0 wceq fiununi_1 fiununi_2 cuni cun fiununi_0 fiununi_2 fiununi_1 fiununi_0 cv cun ciun wceq fiununi_1 c0 wceq fiununi_2 c0 wceq fiununi_1 fiununi_2 cuni cun fiununi_1 fiununi_0 fiununi_2 fiununi_1 fiununi_0 cv cun ciun c0 fiununi_2 c0 wceq fiununi_1 fiununi_2 cuni cun fiununi_1 c0 cun fiununi_1 fiununi_2 c0 wceq fiununi_2 cuni c0 fiununi_1 fiununi_2 c0 wceq fiununi_2 cuni c0 cuni c0 fiununi_2 c0 unieq uni0 syl6eq uneq2d fiununi_1 un0 syl6eq fiununi_2 c0 wceq fiununi_0 fiununi_2 fiununi_1 fiununi_0 cv cun ciun fiununi_0 c0 fiununi_1 fiununi_0 cv cun ciun c0 fiununi_0 fiununi_2 c0 fiununi_1 fiununi_0 cv cun iuneq1 fiununi_0 fiununi_1 fiununi_0 cv cun 0iun syl6eq eqeq12d biimpcd impbii $.
$}
$( Subclass relationship for power class and union.  (Contributed by NM,
       18-Jul-2006.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$d x A $.
	$d x B $.
	isspwuni_0 $f set x $.
	fsspwuni_0 $f class A $.
	fsspwuni_1 $f class B $.
	sspwuni $p |- ( A C_ ~P B <-> U. A C_ B ) $= isspwuni_0 cv fsspwuni_1 cpw wcel isspwuni_0 fsspwuni_0 wral isspwuni_0 cv fsspwuni_1 wss isspwuni_0 fsspwuni_0 wral fsspwuni_0 fsspwuni_1 cpw wss fsspwuni_0 cuni fsspwuni_1 wss isspwuni_0 cv fsspwuni_1 cpw wcel isspwuni_0 cv fsspwuni_1 wss isspwuni_0 fsspwuni_0 isspwuni_0 cv fsspwuni_1 isspwuni_0 vex elpw ralbii isspwuni_0 fsspwuni_0 fsspwuni_1 cpw dfss3 isspwuni_0 fsspwuni_0 fsspwuni_1 unissb 3bitr4i $.
$}
$( Two ways to express a collection of subclasses.  (Contributed by NM,
       19-Jul-2006.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$d x A $.
	$d x B $.
	fpwssb_0 $f set x $.
	fpwssb_1 $f class A $.
	fpwssb_2 $f class B $.
	pwssb $p |- ( A C_ ~P B <-> A. x e. A x C_ B ) $= fpwssb_1 fpwssb_2 cpw wss fpwssb_1 cuni fpwssb_2 wss fpwssb_0 cv fpwssb_2 wss fpwssb_0 fpwssb_1 wral fpwssb_1 fpwssb_2 sspwuni fpwssb_0 fpwssb_1 fpwssb_2 unissb bitri $.
$}
$( Relationship for power class and union.  (Contributed by NM,
     18-Jul-2006.) $)
${
	$v A $.
	$v B $.
	felpwuni_0 $f class A $.
	felpwuni_1 $f class B $.
	elpwuni $p |- ( B e. A -> ( A C_ ~P B <-> U. A = B ) ) $= felpwuni_0 felpwuni_1 cpw wss felpwuni_0 cuni felpwuni_1 wss felpwuni_1 felpwuni_0 wcel felpwuni_0 cuni felpwuni_1 wceq felpwuni_0 felpwuni_1 sspwuni felpwuni_1 felpwuni_0 wcel felpwuni_0 cuni felpwuni_1 wss felpwuni_0 cuni felpwuni_1 wceq felpwuni_0 cuni felpwuni_1 wss felpwuni_1 felpwuni_0 wcel felpwuni_0 cuni felpwuni_1 wceq felpwuni_0 felpwuni_1 unissel expcom felpwuni_0 cuni felpwuni_1 eqimss impbid1 syl5bb $.
$}
$( The power class of an intersection in terms of indexed intersection.
       Exercise 24(a) of [Enderton] p. 33.  (Contributed by NM,
       29-Nov-2003.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$d x y A $.
	iiinpw_0 $f set y $.
	fiinpw_0 $f set x $.
	fiinpw_1 $f class A $.
	iinpw $p |- ~P |^| A = |^|_ x e. A ~P x $= iiinpw_0 fiinpw_1 cint cpw fiinpw_0 fiinpw_1 fiinpw_0 cv cpw ciin iiinpw_0 cv fiinpw_1 cint wss iiinpw_0 cv fiinpw_0 cv cpw wcel fiinpw_0 fiinpw_1 wral iiinpw_0 cv fiinpw_1 cint cpw wcel iiinpw_0 cv fiinpw_0 fiinpw_1 fiinpw_0 cv cpw ciin wcel iiinpw_0 cv fiinpw_1 cint wss iiinpw_0 cv fiinpw_0 cv wss fiinpw_0 fiinpw_1 wral iiinpw_0 cv fiinpw_0 cv cpw wcel fiinpw_0 fiinpw_1 wral fiinpw_0 iiinpw_0 cv fiinpw_1 ssint iiinpw_0 cv fiinpw_0 cv cpw wcel iiinpw_0 cv fiinpw_0 cv wss fiinpw_0 fiinpw_1 iiinpw_0 cv fiinpw_0 cv iiinpw_0 vex elpw ralbii bitr4i iiinpw_0 cv fiinpw_1 cint iiinpw_0 vex elpw iiinpw_0 cv cvv wcel iiinpw_0 cv fiinpw_0 fiinpw_1 fiinpw_0 cv cpw ciin wcel iiinpw_0 cv fiinpw_0 cv cpw wcel fiinpw_0 fiinpw_1 wral wb iiinpw_0 vex fiinpw_0 iiinpw_0 cv fiinpw_1 fiinpw_0 cv cpw cvv eliin ax-mp 3bitr4i eqriv $.
$}
$( Inclusion of an indexed union of a power class in the power class of the
       union of its index.  Part of Exercise 24(b) of [Enderton] p. 33.
       (Contributed by NM, 25-Nov-2003.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$d x y A $.
	iiunpwss_0 $f set y $.
	fiunpwss_0 $f set x $.
	fiunpwss_1 $f class A $.
	iunpwss $p |- U_ x e. A ~P x C_ ~P U. A $= iiunpwss_0 fiunpwss_0 fiunpwss_1 fiunpwss_0 cv cpw ciun fiunpwss_1 cuni cpw iiunpwss_0 cv fiunpwss_0 cv wss fiunpwss_0 fiunpwss_1 wrex iiunpwss_0 cv fiunpwss_0 fiunpwss_1 fiunpwss_0 cv ciun wss iiunpwss_0 cv fiunpwss_0 fiunpwss_1 fiunpwss_0 cv cpw ciun wcel iiunpwss_0 cv fiunpwss_1 cuni cpw wcel fiunpwss_0 fiunpwss_1 fiunpwss_0 cv iiunpwss_0 cv ssiun iiunpwss_0 cv fiunpwss_0 fiunpwss_1 fiunpwss_0 cv cpw ciun wcel iiunpwss_0 cv fiunpwss_0 cv cpw wcel fiunpwss_0 fiunpwss_1 wrex iiunpwss_0 cv fiunpwss_0 cv wss fiunpwss_0 fiunpwss_1 wrex fiunpwss_0 iiunpwss_0 cv fiunpwss_1 fiunpwss_0 cv cpw eliun iiunpwss_0 cv fiunpwss_0 cv cpw wcel iiunpwss_0 cv fiunpwss_0 cv wss fiunpwss_0 fiunpwss_1 iiunpwss_0 cv fiunpwss_0 cv iiunpwss_0 vex elpw rexbii bitri iiunpwss_0 cv fiunpwss_1 cuni cpw wcel iiunpwss_0 cv fiunpwss_1 cuni wss iiunpwss_0 cv fiunpwss_0 fiunpwss_1 fiunpwss_0 cv ciun wss iiunpwss_0 cv fiunpwss_1 cuni iiunpwss_0 vex elpw fiunpwss_1 cuni fiunpwss_0 fiunpwss_1 fiunpwss_0 cv ciun iiunpwss_0 cv fiunpwss_0 fiunpwss_1 uniiun sseq2i bitri 3imtr4i ssriv $.
$}
$( Relative intersection of a nonempty set.  (Contributed by Stefan O'Rear,
     3-Apr-2015.)  (Revised by Mario Carneiro, 5-Jun-2015.) $)
${
	$v A $.
	$v X $.
	frintn0_0 $f class A $.
	frintn0_1 $f class X $.
	rintn0 $p |- ( ( X C_ ~P A /\ X =/= (/) ) -> ( A i^i |^| X ) = |^| X ) $= frintn0_1 frintn0_0 cpw wss frintn0_1 c0 wne wa frintn0_0 frintn0_1 cint cin frintn0_1 cint frintn0_0 cin frintn0_1 cint frintn0_0 frintn0_1 cint incom frintn0_1 frintn0_0 cpw wss frintn0_1 c0 wne wa frintn0_1 cint frintn0_0 wss frintn0_1 cint frintn0_0 cin frintn0_1 cint wceq frintn0_1 frintn0_0 cpw wss frintn0_1 c0 wne wa frintn0_1 cint frintn0_0 cpw cuni frintn0_0 frintn0_1 frintn0_0 cpw intssuni2 frintn0_0 cpw frintn0_0 cpw wss frintn0_0 cpw cuni frintn0_0 wss frintn0_0 cpw ssid frintn0_0 cpw frintn0_0 sspwuni mpbi syl6ss frintn0_1 cint frintn0_0 df-ss sylib syl5eq $.
$}

