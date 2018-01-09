$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/Binary_relations.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                Ordered-pair class abstractions (class builders)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$c |->  $.
$( Maps-to symbol $)
$( Extend class notation to include ordered-pair class abstraction (class
     builder). $)
${
	fcopab_0 $f wff ph $.
	fcopab_1 $f set x $.
	fcopab_2 $f set y $.
	copab $a class { <. x , y >. | ph } $.
$}
$( Extend the definition of a class to include maps-to notation for defining
     a function via a rule. $)
${
	fcmpt_0 $f set x $.
	fcmpt_1 $f class A $.
	fcmpt_2 $f class B $.
	cmpt $a class ( x e. A |-> B ) $.
$}
$( Define the class abstraction of a collection of ordered pairs.
       Definition 3.3 of [Monk1] p. 34.  Usually ` x ` and ` y ` are distinct,
       although the definition doesn't strictly require it (see ~ dfid2 for a
       case where they are not distinct).  The brace notation is called "class
       abstraction" by Quine; it is also (more commonly) called a "class
       builder" in the literature.  An alternate definition using no
       existential quantifiers is shown by ~ dfopab2 .  For example,
` R = { <. x , y >. | ( x e. CC /\ y e. CC /\ ( x + 1 ) = y ) } -> 3 R 4 `
       ( ~ ex-opab ).  (Contributed by NM, 4-Jul-1994.) $)
${
	$d x z $.
	$d y z $.
	$d z ph $.
	fdf-opab_0 $f wff ph $.
	fdf-opab_1 $f set x $.
	fdf-opab_2 $f set y $.
	fdf-opab_3 $f set z $.
	df-opab $a |- { <. x , y >. | ph } = { z | E. x E. y ( z = <. x , y >. /\ ph ) } $.
$}
$( Define maps-to notation for defining a function via a rule.  Read as
       "the function defined by the map from ` x ` (in ` A ` ) to
       ` B ( x ) ` ."  The class expression ` B ` is the value of the function
       at ` x ` and normally contains the variable ` x ` .  An example is the
       square function for complex numbers, ` ( x e. CC |-> ( x ^ 2 ) ) ` .
       Similar to the definition of mapping in [ChoquetDD] p. 2.  (Contributed
       by NM, 17-Feb-2008.) $)
${
	$d x y $.
	$d y A $.
	$d y B $.
	fdf-mpt_0 $f set x $.
	fdf-mpt_1 $f set y $.
	fdf-mpt_2 $f class A $.
	fdf-mpt_3 $f class B $.
	df-mpt $a |- ( x e. A |-> B ) = { <. x , y >. | ( x e. A /\ y = B ) } $.
$}
$( The collection of ordered pairs in a class is a subclass of it.
       (Contributed by NM, 27-Dec-1996.)  (Proof shortened by Andrew Salmon,
       9-Jul-2011.) $)
${
	$d x z R $.
	$d y z R $.
	iopabss_0 $f set z $.
	fopabss_0 $f set x $.
	fopabss_1 $f set y $.
	fopabss_2 $f class R $.
	opabss $p |- { <. x , y >. | x R y } C_ R $= fopabss_0 sup_set_class fopabss_1 sup_set_class fopabss_2 wbr fopabss_0 fopabss_1 copab iopabss_0 sup_set_class fopabss_0 sup_set_class fopabss_1 sup_set_class cop wceq fopabss_0 sup_set_class fopabss_1 sup_set_class fopabss_2 wbr wa fopabss_1 wex fopabss_0 wex iopabss_0 cab fopabss_2 fopabss_0 sup_set_class fopabss_1 sup_set_class fopabss_2 wbr fopabss_0 fopabss_1 iopabss_0 df-opab iopabss_0 sup_set_class fopabss_0 sup_set_class fopabss_1 sup_set_class cop wceq fopabss_0 sup_set_class fopabss_1 sup_set_class fopabss_2 wbr wa fopabss_1 wex fopabss_0 wex iopabss_0 fopabss_2 iopabss_0 sup_set_class fopabss_0 sup_set_class fopabss_1 sup_set_class cop wceq fopabss_0 sup_set_class fopabss_1 sup_set_class fopabss_2 wbr wa iopabss_0 sup_set_class fopabss_2 wcel fopabss_0 fopabss_1 fopabss_0 sup_set_class fopabss_1 sup_set_class fopabss_2 wbr iopabss_0 sup_set_class fopabss_0 sup_set_class fopabss_1 sup_set_class cop wceq fopabss_0 sup_set_class fopabss_1 sup_set_class cop fopabss_2 wcel iopabss_0 sup_set_class fopabss_2 wcel fopabss_0 sup_set_class fopabss_1 sup_set_class fopabss_2 df-br iopabss_0 sup_set_class fopabss_0 sup_set_class fopabss_1 sup_set_class cop wceq iopabss_0 sup_set_class fopabss_2 wcel fopabss_0 sup_set_class fopabss_1 sup_set_class cop fopabss_2 wcel iopabss_0 sup_set_class fopabss_0 sup_set_class fopabss_1 sup_set_class cop fopabss_2 eleq1 biimpar sylan2b exlimivv abssi eqsstri $.
$}
$( Equivalent wff's yield equal ordered-pair class abstractions (deduction
       rule).  (Contributed by NM, 21-Feb-2004.)  (Proof shortened by Andrew
       Salmon, 9-Jul-2011.) $)
${
	$d x z $.
	$d y z $.
	$d z ph $.
	$d z ps $.
	$d z ch $.
	iopabbid_0 $f set z $.
	fopabbid_0 $f wff ph $.
	fopabbid_1 $f wff ps $.
	fopabbid_2 $f wff ch $.
	fopabbid_3 $f set x $.
	fopabbid_4 $f set y $.
	eopabbid_0 $e |- F/ x ph $.
	eopabbid_1 $e |- F/ y ph $.
	eopabbid_2 $e |- ( ph -> ( ps <-> ch ) ) $.
	opabbid $p |- ( ph -> { <. x , y >. | ps } = { <. x , y >. | ch } ) $= fopabbid_0 iopabbid_0 sup_set_class fopabbid_3 sup_set_class fopabbid_4 sup_set_class cop wceq fopabbid_1 wa fopabbid_4 wex fopabbid_3 wex iopabbid_0 cab iopabbid_0 sup_set_class fopabbid_3 sup_set_class fopabbid_4 sup_set_class cop wceq fopabbid_2 wa fopabbid_4 wex fopabbid_3 wex iopabbid_0 cab fopabbid_1 fopabbid_3 fopabbid_4 copab fopabbid_2 fopabbid_3 fopabbid_4 copab fopabbid_0 iopabbid_0 sup_set_class fopabbid_3 sup_set_class fopabbid_4 sup_set_class cop wceq fopabbid_1 wa fopabbid_4 wex fopabbid_3 wex iopabbid_0 sup_set_class fopabbid_3 sup_set_class fopabbid_4 sup_set_class cop wceq fopabbid_2 wa fopabbid_4 wex fopabbid_3 wex iopabbid_0 fopabbid_0 iopabbid_0 sup_set_class fopabbid_3 sup_set_class fopabbid_4 sup_set_class cop wceq fopabbid_1 wa fopabbid_4 wex iopabbid_0 sup_set_class fopabbid_3 sup_set_class fopabbid_4 sup_set_class cop wceq fopabbid_2 wa fopabbid_4 wex fopabbid_3 eopabbid_0 fopabbid_0 iopabbid_0 sup_set_class fopabbid_3 sup_set_class fopabbid_4 sup_set_class cop wceq fopabbid_1 wa iopabbid_0 sup_set_class fopabbid_3 sup_set_class fopabbid_4 sup_set_class cop wceq fopabbid_2 wa fopabbid_4 eopabbid_1 fopabbid_0 fopabbid_1 fopabbid_2 iopabbid_0 sup_set_class fopabbid_3 sup_set_class fopabbid_4 sup_set_class cop wceq eopabbid_2 anbi2d exbid exbid abbidv fopabbid_1 fopabbid_3 fopabbid_4 iopabbid_0 df-opab fopabbid_2 fopabbid_3 fopabbid_4 iopabbid_0 df-opab 3eqtr4g $.
$}
$( Equivalent wff's yield equal ordered-pair class abstractions (deduction
       rule).  (Contributed by NM, 15-May-1995.) $)
${
	$d x ph $.
	$d y ph $.
	fopabbidv_0 $f wff ph $.
	fopabbidv_1 $f wff ps $.
	fopabbidv_2 $f wff ch $.
	fopabbidv_3 $f set x $.
	fopabbidv_4 $f set y $.
	eopabbidv_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	opabbidv $p |- ( ph -> { <. x , y >. | ps } = { <. x , y >. | ch } ) $= fopabbidv_0 fopabbidv_1 fopabbidv_2 fopabbidv_3 fopabbidv_4 fopabbidv_0 fopabbidv_3 nfv fopabbidv_0 fopabbidv_4 nfv eopabbidv_0 opabbid $.
$}
$( Equivalent wff's yield equal class abstractions.  (Contributed by NM,
       15-May-1995.) $)
${
	$d x z $.
	$d y z $.
	$d z ph $.
	$d z ps $.
	iopabbii_0 $f set z $.
	fopabbii_0 $f wff ph $.
	fopabbii_1 $f wff ps $.
	fopabbii_2 $f set x $.
	fopabbii_3 $f set y $.
	eopabbii_0 $e |- ( ph <-> ps ) $.
	opabbii $p |- { <. x , y >. | ph } = { <. x , y >. | ps } $= iopabbii_0 sup_set_class iopabbii_0 sup_set_class wceq fopabbii_0 fopabbii_2 fopabbii_3 copab fopabbii_1 fopabbii_2 fopabbii_3 copab wceq iopabbii_0 sup_set_class eqid iopabbii_0 sup_set_class iopabbii_0 sup_set_class wceq fopabbii_0 fopabbii_1 fopabbii_2 fopabbii_3 fopabbii_0 fopabbii_1 wb iopabbii_0 sup_set_class iopabbii_0 sup_set_class wceq eopabbii_0 a1i opabbidv ax-mp $.
$}
$( Bound-variable hypothesis builder for class abstraction.  (Contributed
       by NM, 1-Sep-1999.)  (Unnecessary distinct variable restrictions were
       removed by Andrew Salmon, 11-Jul-2011.) $)
${
	$d x z w $.
	$d y z w $.
	$d ph w $.
	infopab_0 $f set w $.
	fnfopab_0 $f wff ph $.
	fnfopab_1 $f set x $.
	fnfopab_2 $f set y $.
	fnfopab_3 $f set z $.
	enfopab_0 $e |- F/ z ph $.
	nfopab $p |- F/_ z { <. x , y >. | ph } $= fnfopab_3 fnfopab_0 fnfopab_1 fnfopab_2 copab infopab_0 sup_set_class fnfopab_1 sup_set_class fnfopab_2 sup_set_class cop wceq fnfopab_0 wa fnfopab_2 wex fnfopab_1 wex infopab_0 cab fnfopab_0 fnfopab_1 fnfopab_2 infopab_0 df-opab infopab_0 sup_set_class fnfopab_1 sup_set_class fnfopab_2 sup_set_class cop wceq fnfopab_0 wa fnfopab_2 wex fnfopab_1 wex fnfopab_3 infopab_0 infopab_0 sup_set_class fnfopab_1 sup_set_class fnfopab_2 sup_set_class cop wceq fnfopab_0 wa fnfopab_2 wex fnfopab_3 fnfopab_1 infopab_0 sup_set_class fnfopab_1 sup_set_class fnfopab_2 sup_set_class cop wceq fnfopab_0 wa fnfopab_3 fnfopab_2 infopab_0 sup_set_class fnfopab_1 sup_set_class fnfopab_2 sup_set_class cop wceq fnfopab_0 fnfopab_3 infopab_0 sup_set_class fnfopab_1 sup_set_class fnfopab_2 sup_set_class cop wceq fnfopab_3 nfv enfopab_0 nfan nfex nfex nfab nfcxfr $.
$}
$( The first abstraction variable in an ordered-pair class abstraction
       (class builder) is effectively not free.  (Contributed by NM,
       16-May-1995.)  (Revised by Mario Carneiro, 14-Oct-2016.) $)
${
	$d x z $.
	$d y z $.
	$d z ph $.
	infopab1_0 $f set z $.
	fnfopab1_0 $f wff ph $.
	fnfopab1_1 $f set x $.
	fnfopab1_2 $f set y $.
	nfopab1 $p |- F/_ x { <. x , y >. | ph } $= fnfopab1_1 fnfopab1_0 fnfopab1_1 fnfopab1_2 copab infopab1_0 sup_set_class fnfopab1_1 sup_set_class fnfopab1_2 sup_set_class cop wceq fnfopab1_0 wa fnfopab1_2 wex fnfopab1_1 wex infopab1_0 cab fnfopab1_0 fnfopab1_1 fnfopab1_2 infopab1_0 df-opab infopab1_0 sup_set_class fnfopab1_1 sup_set_class fnfopab1_2 sup_set_class cop wceq fnfopab1_0 wa fnfopab1_2 wex fnfopab1_1 wex fnfopab1_1 infopab1_0 infopab1_0 sup_set_class fnfopab1_1 sup_set_class fnfopab1_2 sup_set_class cop wceq fnfopab1_0 wa fnfopab1_2 wex fnfopab1_1 nfe1 nfab nfcxfr $.
$}
$( The second abstraction variable in an ordered-pair class abstraction
       (class builder) is effectively not free.  (Contributed by NM,
       16-May-1995.)  (Revised by Mario Carneiro, 14-Oct-2016.) $)
${
	$d x z $.
	$d y z $.
	$d z ph $.
	infopab2_0 $f set z $.
	fnfopab2_0 $f wff ph $.
	fnfopab2_1 $f set x $.
	fnfopab2_2 $f set y $.
	nfopab2 $p |- F/_ y { <. x , y >. | ph } $= fnfopab2_2 fnfopab2_0 fnfopab2_1 fnfopab2_2 copab infopab2_0 sup_set_class fnfopab2_1 sup_set_class fnfopab2_2 sup_set_class cop wceq fnfopab2_0 wa fnfopab2_2 wex fnfopab2_1 wex infopab2_0 cab fnfopab2_0 fnfopab2_1 fnfopab2_2 infopab2_0 df-opab infopab2_0 sup_set_class fnfopab2_1 sup_set_class fnfopab2_2 sup_set_class cop wceq fnfopab2_0 wa fnfopab2_2 wex fnfopab2_1 wex fnfopab2_2 infopab2_0 infopab2_0 sup_set_class fnfopab2_1 sup_set_class fnfopab2_2 sup_set_class cop wceq fnfopab2_0 wa fnfopab2_2 wex fnfopab2_2 fnfopab2_1 infopab2_0 sup_set_class fnfopab2_1 sup_set_class fnfopab2_2 sup_set_class cop wceq fnfopab2_0 wa fnfopab2_2 nfe1 nfex nfab nfcxfr $.
$}
$( Rule used to change bound variables in an ordered-pair class
       abstraction, using implicit substitution.  (Contributed by NM,
       14-Sep-2003.) $)
${
	$d x y z w v $.
	$d v ph $.
	$d v ps $.
	icbvopab_0 $f set v $.
	fcbvopab_0 $f wff ph $.
	fcbvopab_1 $f wff ps $.
	fcbvopab_2 $f set x $.
	fcbvopab_3 $f set y $.
	fcbvopab_4 $f set z $.
	fcbvopab_5 $f set w $.
	ecbvopab_0 $e |- F/ z ph $.
	ecbvopab_1 $e |- F/ w ph $.
	ecbvopab_2 $e |- F/ x ps $.
	ecbvopab_3 $e |- F/ y ps $.
	ecbvopab_4 $e |- ( ( x = z /\ y = w ) -> ( ph <-> ps ) ) $.
	cbvopab $p |- { <. x , y >. | ph } = { <. z , w >. | ps } $= icbvopab_0 sup_set_class fcbvopab_2 sup_set_class fcbvopab_3 sup_set_class cop wceq fcbvopab_0 wa fcbvopab_3 wex fcbvopab_2 wex icbvopab_0 cab icbvopab_0 sup_set_class fcbvopab_4 sup_set_class fcbvopab_5 sup_set_class cop wceq fcbvopab_1 wa fcbvopab_5 wex fcbvopab_4 wex icbvopab_0 cab fcbvopab_0 fcbvopab_2 fcbvopab_3 copab fcbvopab_1 fcbvopab_4 fcbvopab_5 copab icbvopab_0 sup_set_class fcbvopab_2 sup_set_class fcbvopab_3 sup_set_class cop wceq fcbvopab_0 wa fcbvopab_3 wex fcbvopab_2 wex icbvopab_0 sup_set_class fcbvopab_4 sup_set_class fcbvopab_5 sup_set_class cop wceq fcbvopab_1 wa fcbvopab_5 wex fcbvopab_4 wex icbvopab_0 icbvopab_0 sup_set_class fcbvopab_2 sup_set_class fcbvopab_3 sup_set_class cop wceq fcbvopab_0 wa icbvopab_0 sup_set_class fcbvopab_4 sup_set_class fcbvopab_5 sup_set_class cop wceq fcbvopab_1 wa fcbvopab_2 fcbvopab_3 fcbvopab_4 fcbvopab_5 icbvopab_0 sup_set_class fcbvopab_2 sup_set_class fcbvopab_3 sup_set_class cop wceq fcbvopab_0 fcbvopab_4 icbvopab_0 sup_set_class fcbvopab_2 sup_set_class fcbvopab_3 sup_set_class cop wceq fcbvopab_4 nfv ecbvopab_0 nfan icbvopab_0 sup_set_class fcbvopab_2 sup_set_class fcbvopab_3 sup_set_class cop wceq fcbvopab_0 fcbvopab_5 icbvopab_0 sup_set_class fcbvopab_2 sup_set_class fcbvopab_3 sup_set_class cop wceq fcbvopab_5 nfv ecbvopab_1 nfan icbvopab_0 sup_set_class fcbvopab_4 sup_set_class fcbvopab_5 sup_set_class cop wceq fcbvopab_1 fcbvopab_2 icbvopab_0 sup_set_class fcbvopab_4 sup_set_class fcbvopab_5 sup_set_class cop wceq fcbvopab_2 nfv ecbvopab_2 nfan icbvopab_0 sup_set_class fcbvopab_4 sup_set_class fcbvopab_5 sup_set_class cop wceq fcbvopab_1 fcbvopab_3 icbvopab_0 sup_set_class fcbvopab_4 sup_set_class fcbvopab_5 sup_set_class cop wceq fcbvopab_3 nfv ecbvopab_3 nfan fcbvopab_2 sup_set_class fcbvopab_4 sup_set_class wceq fcbvopab_3 sup_set_class fcbvopab_5 sup_set_class wceq wa icbvopab_0 sup_set_class fcbvopab_2 sup_set_class fcbvopab_3 sup_set_class cop wceq icbvopab_0 sup_set_class fcbvopab_4 sup_set_class fcbvopab_5 sup_set_class cop wceq fcbvopab_0 fcbvopab_1 fcbvopab_2 sup_set_class fcbvopab_4 sup_set_class wceq fcbvopab_3 sup_set_class fcbvopab_5 sup_set_class wceq wa fcbvopab_2 sup_set_class fcbvopab_3 sup_set_class cop fcbvopab_4 sup_set_class fcbvopab_5 sup_set_class cop icbvopab_0 sup_set_class fcbvopab_2 sup_set_class fcbvopab_3 sup_set_class fcbvopab_4 sup_set_class fcbvopab_5 sup_set_class opeq12 eqeq2d ecbvopab_4 anbi12d cbvex2 abbii fcbvopab_0 fcbvopab_2 fcbvopab_3 icbvopab_0 df-opab fcbvopab_1 fcbvopab_4 fcbvopab_5 icbvopab_0 df-opab 3eqtr4i $.
$}
$( Rule used to change bound variables in an ordered-pair class
       abstraction, using implicit substitution.  (Contributed by NM,
       15-Oct-1996.) $)
${
	$d x y z w $.
	$d z w ph $.
	$d x y ps $.
	fcbvopabv_0 $f wff ph $.
	fcbvopabv_1 $f wff ps $.
	fcbvopabv_2 $f set x $.
	fcbvopabv_3 $f set y $.
	fcbvopabv_4 $f set z $.
	fcbvopabv_5 $f set w $.
	ecbvopabv_0 $e |- ( ( x = z /\ y = w ) -> ( ph <-> ps ) ) $.
	cbvopabv $p |- { <. x , y >. | ph } = { <. z , w >. | ps } $= fcbvopabv_0 fcbvopabv_1 fcbvopabv_2 fcbvopabv_3 fcbvopabv_4 fcbvopabv_5 fcbvopabv_0 fcbvopabv_4 nfv fcbvopabv_0 fcbvopabv_5 nfv fcbvopabv_1 fcbvopabv_2 nfv fcbvopabv_1 fcbvopabv_3 nfv ecbvopabv_0 cbvopab $.
$}
$( Change first bound variable in an ordered-pair class abstraction, using
       explicit substitution.  (Contributed by NM, 6-Oct-2004.)  (Revised by
       Mario Carneiro, 14-Oct-2016.) $)
${
	$d v w x y $.
	$d v w y z $.
	$d v w ph $.
	$d v w ps $.
	icbvopab1_0 $f set w $.
	icbvopab1_1 $f set v $.
	fcbvopab1_0 $f wff ph $.
	fcbvopab1_1 $f wff ps $.
	fcbvopab1_2 $f set x $.
	fcbvopab1_3 $f set y $.
	fcbvopab1_4 $f set z $.
	ecbvopab1_0 $e |- F/ z ph $.
	ecbvopab1_1 $e |- F/ x ps $.
	ecbvopab1_2 $e |- ( x = z -> ( ph <-> ps ) ) $.
	cbvopab1 $p |- { <. x , y >. | ph } = { <. z , y >. | ps } $= icbvopab1_0 sup_set_class fcbvopab1_2 sup_set_class fcbvopab1_3 sup_set_class cop wceq fcbvopab1_0 wa fcbvopab1_3 wex fcbvopab1_2 wex icbvopab1_0 cab icbvopab1_0 sup_set_class fcbvopab1_4 sup_set_class fcbvopab1_3 sup_set_class cop wceq fcbvopab1_1 wa fcbvopab1_3 wex fcbvopab1_4 wex icbvopab1_0 cab fcbvopab1_0 fcbvopab1_2 fcbvopab1_3 copab fcbvopab1_1 fcbvopab1_4 fcbvopab1_3 copab icbvopab1_0 sup_set_class fcbvopab1_2 sup_set_class fcbvopab1_3 sup_set_class cop wceq fcbvopab1_0 wa fcbvopab1_3 wex fcbvopab1_2 wex icbvopab1_0 sup_set_class fcbvopab1_4 sup_set_class fcbvopab1_3 sup_set_class cop wceq fcbvopab1_1 wa fcbvopab1_3 wex fcbvopab1_4 wex icbvopab1_0 icbvopab1_0 sup_set_class fcbvopab1_2 sup_set_class fcbvopab1_3 sup_set_class cop wceq fcbvopab1_0 wa fcbvopab1_3 wex fcbvopab1_2 wex icbvopab1_0 sup_set_class icbvopab1_1 sup_set_class fcbvopab1_3 sup_set_class cop wceq fcbvopab1_0 fcbvopab1_2 icbvopab1_1 wsb wa fcbvopab1_3 wex icbvopab1_1 wex icbvopab1_0 sup_set_class fcbvopab1_4 sup_set_class fcbvopab1_3 sup_set_class cop wceq fcbvopab1_1 wa fcbvopab1_3 wex fcbvopab1_4 wex icbvopab1_0 sup_set_class fcbvopab1_2 sup_set_class fcbvopab1_3 sup_set_class cop wceq fcbvopab1_0 wa fcbvopab1_3 wex icbvopab1_0 sup_set_class icbvopab1_1 sup_set_class fcbvopab1_3 sup_set_class cop wceq fcbvopab1_0 fcbvopab1_2 icbvopab1_1 wsb wa fcbvopab1_3 wex fcbvopab1_2 icbvopab1_1 icbvopab1_0 sup_set_class fcbvopab1_2 sup_set_class fcbvopab1_3 sup_set_class cop wceq fcbvopab1_0 wa fcbvopab1_3 wex icbvopab1_1 nfv icbvopab1_0 sup_set_class icbvopab1_1 sup_set_class fcbvopab1_3 sup_set_class cop wceq fcbvopab1_0 fcbvopab1_2 icbvopab1_1 wsb wa fcbvopab1_2 fcbvopab1_3 icbvopab1_0 sup_set_class icbvopab1_1 sup_set_class fcbvopab1_3 sup_set_class cop wceq fcbvopab1_0 fcbvopab1_2 icbvopab1_1 wsb fcbvopab1_2 icbvopab1_0 sup_set_class icbvopab1_1 sup_set_class fcbvopab1_3 sup_set_class cop wceq fcbvopab1_2 nfv fcbvopab1_0 fcbvopab1_2 icbvopab1_1 nfs1v nfan nfex fcbvopab1_2 sup_set_class icbvopab1_1 sup_set_class wceq icbvopab1_0 sup_set_class fcbvopab1_2 sup_set_class fcbvopab1_3 sup_set_class cop wceq fcbvopab1_0 wa icbvopab1_0 sup_set_class icbvopab1_1 sup_set_class fcbvopab1_3 sup_set_class cop wceq fcbvopab1_0 fcbvopab1_2 icbvopab1_1 wsb wa fcbvopab1_3 fcbvopab1_2 sup_set_class icbvopab1_1 sup_set_class wceq icbvopab1_0 sup_set_class fcbvopab1_2 sup_set_class fcbvopab1_3 sup_set_class cop wceq icbvopab1_0 sup_set_class icbvopab1_1 sup_set_class fcbvopab1_3 sup_set_class cop wceq fcbvopab1_0 fcbvopab1_0 fcbvopab1_2 icbvopab1_1 wsb fcbvopab1_2 sup_set_class icbvopab1_1 sup_set_class wceq fcbvopab1_2 sup_set_class fcbvopab1_3 sup_set_class cop icbvopab1_1 sup_set_class fcbvopab1_3 sup_set_class cop icbvopab1_0 sup_set_class fcbvopab1_2 sup_set_class icbvopab1_1 sup_set_class fcbvopab1_3 sup_set_class opeq1 eqeq2d fcbvopab1_0 fcbvopab1_2 icbvopab1_1 sbequ12 anbi12d exbidv cbvex icbvopab1_0 sup_set_class icbvopab1_1 sup_set_class fcbvopab1_3 sup_set_class cop wceq fcbvopab1_0 fcbvopab1_2 icbvopab1_1 wsb wa fcbvopab1_3 wex icbvopab1_0 sup_set_class fcbvopab1_4 sup_set_class fcbvopab1_3 sup_set_class cop wceq fcbvopab1_1 wa fcbvopab1_3 wex icbvopab1_1 fcbvopab1_4 icbvopab1_0 sup_set_class icbvopab1_1 sup_set_class fcbvopab1_3 sup_set_class cop wceq fcbvopab1_0 fcbvopab1_2 icbvopab1_1 wsb wa fcbvopab1_4 fcbvopab1_3 icbvopab1_0 sup_set_class icbvopab1_1 sup_set_class fcbvopab1_3 sup_set_class cop wceq fcbvopab1_0 fcbvopab1_2 icbvopab1_1 wsb fcbvopab1_4 icbvopab1_0 sup_set_class icbvopab1_1 sup_set_class fcbvopab1_3 sup_set_class cop wceq fcbvopab1_4 nfv fcbvopab1_0 fcbvopab1_2 icbvopab1_1 fcbvopab1_4 ecbvopab1_0 nfsb nfan nfex icbvopab1_0 sup_set_class fcbvopab1_4 sup_set_class fcbvopab1_3 sup_set_class cop wceq fcbvopab1_1 wa fcbvopab1_3 wex icbvopab1_1 nfv icbvopab1_1 sup_set_class fcbvopab1_4 sup_set_class wceq icbvopab1_0 sup_set_class icbvopab1_1 sup_set_class fcbvopab1_3 sup_set_class cop wceq fcbvopab1_0 fcbvopab1_2 icbvopab1_1 wsb wa icbvopab1_0 sup_set_class fcbvopab1_4 sup_set_class fcbvopab1_3 sup_set_class cop wceq fcbvopab1_1 wa fcbvopab1_3 icbvopab1_1 sup_set_class fcbvopab1_4 sup_set_class wceq icbvopab1_0 sup_set_class icbvopab1_1 sup_set_class fcbvopab1_3 sup_set_class cop wceq icbvopab1_0 sup_set_class fcbvopab1_4 sup_set_class fcbvopab1_3 sup_set_class cop wceq fcbvopab1_0 fcbvopab1_2 icbvopab1_1 wsb fcbvopab1_1 icbvopab1_1 sup_set_class fcbvopab1_4 sup_set_class wceq icbvopab1_1 sup_set_class fcbvopab1_3 sup_set_class cop fcbvopab1_4 sup_set_class fcbvopab1_3 sup_set_class cop icbvopab1_0 sup_set_class icbvopab1_1 sup_set_class fcbvopab1_4 sup_set_class fcbvopab1_3 sup_set_class opeq1 eqeq2d icbvopab1_1 sup_set_class fcbvopab1_4 sup_set_class wceq fcbvopab1_0 fcbvopab1_2 icbvopab1_1 wsb fcbvopab1_0 fcbvopab1_2 fcbvopab1_4 wsb fcbvopab1_1 fcbvopab1_0 icbvopab1_1 fcbvopab1_4 fcbvopab1_2 sbequ fcbvopab1_0 fcbvopab1_1 fcbvopab1_2 fcbvopab1_4 ecbvopab1_1 ecbvopab1_2 sbie syl6bb anbi12d exbidv cbvex bitri abbii fcbvopab1_0 fcbvopab1_2 fcbvopab1_3 icbvopab1_0 df-opab fcbvopab1_1 fcbvopab1_4 fcbvopab1_3 icbvopab1_0 df-opab 3eqtr4i $.
$}
$( Change second bound variable in an ordered-pair class abstraction, using
       explicit substitution.  (Contributed by NM, 22-Aug-2013.) $)
${
	$d w x y z $.
	$d w ph $.
	$d w ps $.
	icbvopab2_0 $f set w $.
	fcbvopab2_0 $f wff ph $.
	fcbvopab2_1 $f wff ps $.
	fcbvopab2_2 $f set x $.
	fcbvopab2_3 $f set y $.
	fcbvopab2_4 $f set z $.
	ecbvopab2_0 $e |- F/ z ph $.
	ecbvopab2_1 $e |- F/ y ps $.
	ecbvopab2_2 $e |- ( y = z -> ( ph <-> ps ) ) $.
	cbvopab2 $p |- { <. x , y >. | ph } = { <. x , z >. | ps } $= icbvopab2_0 sup_set_class fcbvopab2_2 sup_set_class fcbvopab2_3 sup_set_class cop wceq fcbvopab2_0 wa fcbvopab2_3 wex fcbvopab2_2 wex icbvopab2_0 cab icbvopab2_0 sup_set_class fcbvopab2_2 sup_set_class fcbvopab2_4 sup_set_class cop wceq fcbvopab2_1 wa fcbvopab2_4 wex fcbvopab2_2 wex icbvopab2_0 cab fcbvopab2_0 fcbvopab2_2 fcbvopab2_3 copab fcbvopab2_1 fcbvopab2_2 fcbvopab2_4 copab icbvopab2_0 sup_set_class fcbvopab2_2 sup_set_class fcbvopab2_3 sup_set_class cop wceq fcbvopab2_0 wa fcbvopab2_3 wex fcbvopab2_2 wex icbvopab2_0 sup_set_class fcbvopab2_2 sup_set_class fcbvopab2_4 sup_set_class cop wceq fcbvopab2_1 wa fcbvopab2_4 wex fcbvopab2_2 wex icbvopab2_0 icbvopab2_0 sup_set_class fcbvopab2_2 sup_set_class fcbvopab2_3 sup_set_class cop wceq fcbvopab2_0 wa fcbvopab2_3 wex icbvopab2_0 sup_set_class fcbvopab2_2 sup_set_class fcbvopab2_4 sup_set_class cop wceq fcbvopab2_1 wa fcbvopab2_4 wex fcbvopab2_2 icbvopab2_0 sup_set_class fcbvopab2_2 sup_set_class fcbvopab2_3 sup_set_class cop wceq fcbvopab2_0 wa icbvopab2_0 sup_set_class fcbvopab2_2 sup_set_class fcbvopab2_4 sup_set_class cop wceq fcbvopab2_1 wa fcbvopab2_3 fcbvopab2_4 icbvopab2_0 sup_set_class fcbvopab2_2 sup_set_class fcbvopab2_3 sup_set_class cop wceq fcbvopab2_0 fcbvopab2_4 icbvopab2_0 sup_set_class fcbvopab2_2 sup_set_class fcbvopab2_3 sup_set_class cop wceq fcbvopab2_4 nfv ecbvopab2_0 nfan icbvopab2_0 sup_set_class fcbvopab2_2 sup_set_class fcbvopab2_4 sup_set_class cop wceq fcbvopab2_1 fcbvopab2_3 icbvopab2_0 sup_set_class fcbvopab2_2 sup_set_class fcbvopab2_4 sup_set_class cop wceq fcbvopab2_3 nfv ecbvopab2_1 nfan fcbvopab2_3 sup_set_class fcbvopab2_4 sup_set_class wceq icbvopab2_0 sup_set_class fcbvopab2_2 sup_set_class fcbvopab2_3 sup_set_class cop wceq icbvopab2_0 sup_set_class fcbvopab2_2 sup_set_class fcbvopab2_4 sup_set_class cop wceq fcbvopab2_0 fcbvopab2_1 fcbvopab2_3 sup_set_class fcbvopab2_4 sup_set_class wceq fcbvopab2_2 sup_set_class fcbvopab2_3 sup_set_class cop fcbvopab2_2 sup_set_class fcbvopab2_4 sup_set_class cop icbvopab2_0 sup_set_class fcbvopab2_3 sup_set_class fcbvopab2_4 sup_set_class fcbvopab2_2 sup_set_class opeq2 eqeq2d ecbvopab2_2 anbi12d cbvex exbii abbii fcbvopab2_0 fcbvopab2_2 fcbvopab2_3 icbvopab2_0 df-opab fcbvopab2_1 fcbvopab2_2 fcbvopab2_4 icbvopab2_0 df-opab 3eqtr4i $.
$}
$( Change first bound variable in an ordered-pair class abstraction, using
       explicit substitution.  (Contributed by NM, 31-Jul-2003.) $)
${
	$d x y z w $.
	$d z w ph $.
	icbvopab1s_0 $f set w $.
	fcbvopab1s_0 $f wff ph $.
	fcbvopab1s_1 $f set x $.
	fcbvopab1s_2 $f set y $.
	fcbvopab1s_3 $f set z $.
	cbvopab1s $p |- { <. x , y >. | ph } = { <. z , y >. | [ z / x ] ph } $= icbvopab1s_0 sup_set_class fcbvopab1s_1 sup_set_class fcbvopab1s_2 sup_set_class cop wceq fcbvopab1s_0 wa fcbvopab1s_2 wex fcbvopab1s_1 wex icbvopab1s_0 cab icbvopab1s_0 sup_set_class fcbvopab1s_3 sup_set_class fcbvopab1s_2 sup_set_class cop wceq fcbvopab1s_0 fcbvopab1s_1 fcbvopab1s_3 wsb wa fcbvopab1s_2 wex fcbvopab1s_3 wex icbvopab1s_0 cab fcbvopab1s_0 fcbvopab1s_1 fcbvopab1s_2 copab fcbvopab1s_0 fcbvopab1s_1 fcbvopab1s_3 wsb fcbvopab1s_3 fcbvopab1s_2 copab icbvopab1s_0 sup_set_class fcbvopab1s_1 sup_set_class fcbvopab1s_2 sup_set_class cop wceq fcbvopab1s_0 wa fcbvopab1s_2 wex fcbvopab1s_1 wex icbvopab1s_0 sup_set_class fcbvopab1s_3 sup_set_class fcbvopab1s_2 sup_set_class cop wceq fcbvopab1s_0 fcbvopab1s_1 fcbvopab1s_3 wsb wa fcbvopab1s_2 wex fcbvopab1s_3 wex icbvopab1s_0 icbvopab1s_0 sup_set_class fcbvopab1s_1 sup_set_class fcbvopab1s_2 sup_set_class cop wceq fcbvopab1s_0 wa fcbvopab1s_2 wex icbvopab1s_0 sup_set_class fcbvopab1s_3 sup_set_class fcbvopab1s_2 sup_set_class cop wceq fcbvopab1s_0 fcbvopab1s_1 fcbvopab1s_3 wsb wa fcbvopab1s_2 wex fcbvopab1s_1 fcbvopab1s_3 icbvopab1s_0 sup_set_class fcbvopab1s_1 sup_set_class fcbvopab1s_2 sup_set_class cop wceq fcbvopab1s_0 wa fcbvopab1s_2 wex fcbvopab1s_3 nfv icbvopab1s_0 sup_set_class fcbvopab1s_3 sup_set_class fcbvopab1s_2 sup_set_class cop wceq fcbvopab1s_0 fcbvopab1s_1 fcbvopab1s_3 wsb wa fcbvopab1s_1 fcbvopab1s_2 icbvopab1s_0 sup_set_class fcbvopab1s_3 sup_set_class fcbvopab1s_2 sup_set_class cop wceq fcbvopab1s_0 fcbvopab1s_1 fcbvopab1s_3 wsb fcbvopab1s_1 icbvopab1s_0 sup_set_class fcbvopab1s_3 sup_set_class fcbvopab1s_2 sup_set_class cop wceq fcbvopab1s_1 nfv fcbvopab1s_0 fcbvopab1s_1 fcbvopab1s_3 nfs1v nfan nfex fcbvopab1s_1 sup_set_class fcbvopab1s_3 sup_set_class wceq icbvopab1s_0 sup_set_class fcbvopab1s_1 sup_set_class fcbvopab1s_2 sup_set_class cop wceq fcbvopab1s_0 wa icbvopab1s_0 sup_set_class fcbvopab1s_3 sup_set_class fcbvopab1s_2 sup_set_class cop wceq fcbvopab1s_0 fcbvopab1s_1 fcbvopab1s_3 wsb wa fcbvopab1s_2 fcbvopab1s_1 sup_set_class fcbvopab1s_3 sup_set_class wceq icbvopab1s_0 sup_set_class fcbvopab1s_1 sup_set_class fcbvopab1s_2 sup_set_class cop wceq icbvopab1s_0 sup_set_class fcbvopab1s_3 sup_set_class fcbvopab1s_2 sup_set_class cop wceq fcbvopab1s_0 fcbvopab1s_0 fcbvopab1s_1 fcbvopab1s_3 wsb fcbvopab1s_1 sup_set_class fcbvopab1s_3 sup_set_class wceq fcbvopab1s_1 sup_set_class fcbvopab1s_2 sup_set_class cop fcbvopab1s_3 sup_set_class fcbvopab1s_2 sup_set_class cop icbvopab1s_0 sup_set_class fcbvopab1s_1 sup_set_class fcbvopab1s_3 sup_set_class fcbvopab1s_2 sup_set_class opeq1 eqeq2d fcbvopab1s_0 fcbvopab1s_1 fcbvopab1s_3 sbequ12 anbi12d exbidv cbvex abbii fcbvopab1s_0 fcbvopab1s_1 fcbvopab1s_2 icbvopab1s_0 df-opab fcbvopab1s_0 fcbvopab1s_1 fcbvopab1s_3 wsb fcbvopab1s_3 fcbvopab1s_2 icbvopab1s_0 df-opab 3eqtr4i $.
$}
$( Rule used to change the first bound variable in an ordered pair
       abstraction, using implicit substitution.  (Contributed by NM,
       31-Jul-2003.)  (Proof shortened by Eric Schmidt, 4-Apr-2007.) $)
${
	$d x y $.
	$d y z $.
	$d z ph $.
	$d x ps $.
	fcbvopab1v_0 $f wff ph $.
	fcbvopab1v_1 $f wff ps $.
	fcbvopab1v_2 $f set x $.
	fcbvopab1v_3 $f set y $.
	fcbvopab1v_4 $f set z $.
	ecbvopab1v_0 $e |- ( x = z -> ( ph <-> ps ) ) $.
	cbvopab1v $p |- { <. x , y >. | ph } = { <. z , y >. | ps } $= fcbvopab1v_0 fcbvopab1v_1 fcbvopab1v_2 fcbvopab1v_3 fcbvopab1v_4 fcbvopab1v_0 fcbvopab1v_4 nfv fcbvopab1v_1 fcbvopab1v_2 nfv ecbvopab1v_0 cbvopab1 $.
$}
$( Rule used to change the second bound variable in an ordered pair
       abstraction, using implicit substitution.  (Contributed by NM,
       2-Sep-1999.) $)
${
	$d x y z w $.
	$d z w ph $.
	$d y w ps $.
	icbvopab2v_0 $f set w $.
	fcbvopab2v_0 $f wff ph $.
	fcbvopab2v_1 $f wff ps $.
	fcbvopab2v_2 $f set x $.
	fcbvopab2v_3 $f set y $.
	fcbvopab2v_4 $f set z $.
	ecbvopab2v_0 $e |- ( y = z -> ( ph <-> ps ) ) $.
	cbvopab2v $p |- { <. x , y >. | ph } = { <. x , z >. | ps } $= icbvopab2v_0 sup_set_class fcbvopab2v_2 sup_set_class fcbvopab2v_3 sup_set_class cop wceq fcbvopab2v_0 wa fcbvopab2v_3 wex fcbvopab2v_2 wex icbvopab2v_0 cab icbvopab2v_0 sup_set_class fcbvopab2v_2 sup_set_class fcbvopab2v_4 sup_set_class cop wceq fcbvopab2v_1 wa fcbvopab2v_4 wex fcbvopab2v_2 wex icbvopab2v_0 cab fcbvopab2v_0 fcbvopab2v_2 fcbvopab2v_3 copab fcbvopab2v_1 fcbvopab2v_2 fcbvopab2v_4 copab icbvopab2v_0 sup_set_class fcbvopab2v_2 sup_set_class fcbvopab2v_3 sup_set_class cop wceq fcbvopab2v_0 wa fcbvopab2v_3 wex fcbvopab2v_2 wex icbvopab2v_0 sup_set_class fcbvopab2v_2 sup_set_class fcbvopab2v_4 sup_set_class cop wceq fcbvopab2v_1 wa fcbvopab2v_4 wex fcbvopab2v_2 wex icbvopab2v_0 icbvopab2v_0 sup_set_class fcbvopab2v_2 sup_set_class fcbvopab2v_3 sup_set_class cop wceq fcbvopab2v_0 wa fcbvopab2v_3 wex icbvopab2v_0 sup_set_class fcbvopab2v_2 sup_set_class fcbvopab2v_4 sup_set_class cop wceq fcbvopab2v_1 wa fcbvopab2v_4 wex fcbvopab2v_2 icbvopab2v_0 sup_set_class fcbvopab2v_2 sup_set_class fcbvopab2v_3 sup_set_class cop wceq fcbvopab2v_0 wa icbvopab2v_0 sup_set_class fcbvopab2v_2 sup_set_class fcbvopab2v_4 sup_set_class cop wceq fcbvopab2v_1 wa fcbvopab2v_3 fcbvopab2v_4 fcbvopab2v_3 sup_set_class fcbvopab2v_4 sup_set_class wceq icbvopab2v_0 sup_set_class fcbvopab2v_2 sup_set_class fcbvopab2v_3 sup_set_class cop wceq icbvopab2v_0 sup_set_class fcbvopab2v_2 sup_set_class fcbvopab2v_4 sup_set_class cop wceq fcbvopab2v_0 fcbvopab2v_1 fcbvopab2v_3 sup_set_class fcbvopab2v_4 sup_set_class wceq fcbvopab2v_2 sup_set_class fcbvopab2v_3 sup_set_class cop fcbvopab2v_2 sup_set_class fcbvopab2v_4 sup_set_class cop icbvopab2v_0 sup_set_class fcbvopab2v_3 sup_set_class fcbvopab2v_4 sup_set_class fcbvopab2v_2 sup_set_class opeq2 eqeq2d ecbvopab2v_0 anbi12d cbvexv exbii abbii fcbvopab2v_0 fcbvopab2v_2 fcbvopab2v_3 icbvopab2v_0 df-opab fcbvopab2v_1 fcbvopab2v_2 fcbvopab2v_4 icbvopab2v_0 df-opab 3eqtr4i $.
$}
$( Move substitution into a class abstraction.  (Contributed by NM,
       6-Aug-2007.)  (Proof shortened by Mario Carneiro, 17-Nov-2016.) $)
${
	$d w y z A $.
	$d w ph $.
	$d w x y z $.
	icsbopabg_0 $f set w $.
	fcsbopabg_0 $f wff ph $.
	fcsbopabg_1 $f set x $.
	fcsbopabg_2 $f set y $.
	fcsbopabg_3 $f set z $.
	fcsbopabg_4 $f class A $.
	fcsbopabg_5 $f class V $.
	csbopabg $p |- ( A e. V -> [_ A / x ]_ { <. y , z >. | ph } = { <. y , z >. | [. A / x ]. ph } ) $= fcsbopabg_1 icsbopabg_0 sup_set_class fcsbopabg_0 fcsbopabg_2 fcsbopabg_3 copab csb fcsbopabg_0 fcsbopabg_1 icsbopabg_0 wsb fcsbopabg_2 fcsbopabg_3 copab wceq fcsbopabg_1 fcsbopabg_4 fcsbopabg_0 fcsbopabg_2 fcsbopabg_3 copab csb fcsbopabg_0 fcsbopabg_1 fcsbopabg_4 wsbc fcsbopabg_2 fcsbopabg_3 copab wceq icsbopabg_0 fcsbopabg_4 fcsbopabg_5 icsbopabg_0 sup_set_class fcsbopabg_4 wceq fcsbopabg_1 icsbopabg_0 sup_set_class fcsbopabg_0 fcsbopabg_2 fcsbopabg_3 copab csb fcsbopabg_1 fcsbopabg_4 fcsbopabg_0 fcsbopabg_2 fcsbopabg_3 copab csb fcsbopabg_0 fcsbopabg_1 icsbopabg_0 wsb fcsbopabg_2 fcsbopabg_3 copab fcsbopabg_0 fcsbopabg_1 fcsbopabg_4 wsbc fcsbopabg_2 fcsbopabg_3 copab fcsbopabg_1 icsbopabg_0 sup_set_class fcsbopabg_4 fcsbopabg_0 fcsbopabg_2 fcsbopabg_3 copab csbeq1 icsbopabg_0 sup_set_class fcsbopabg_4 wceq fcsbopabg_0 fcsbopabg_1 icsbopabg_0 wsb fcsbopabg_0 fcsbopabg_1 fcsbopabg_4 wsbc fcsbopabg_2 fcsbopabg_3 fcsbopabg_0 fcsbopabg_1 icsbopabg_0 fcsbopabg_4 dfsbcq2 opabbidv eqeq12d fcsbopabg_1 icsbopabg_0 sup_set_class fcsbopabg_0 fcsbopabg_2 fcsbopabg_3 copab fcsbopabg_0 fcsbopabg_1 icsbopabg_0 wsb fcsbopabg_2 fcsbopabg_3 copab icsbopabg_0 vex fcsbopabg_0 fcsbopabg_1 icsbopabg_0 wsb fcsbopabg_2 fcsbopabg_3 fcsbopabg_1 fcsbopabg_0 fcsbopabg_1 icsbopabg_0 nfs1v nfopab fcsbopabg_1 sup_set_class icsbopabg_0 sup_set_class wceq fcsbopabg_0 fcsbopabg_0 fcsbopabg_1 icsbopabg_0 wsb fcsbopabg_2 fcsbopabg_3 fcsbopabg_0 fcsbopabg_1 icsbopabg_0 sbequ12 opabbidv csbief vtoclg $.
$}
$( Union of two ordered pair class abstractions.  (Contributed by NM,
       30-Sep-2002.) $)
${
	$d x z $.
	$d y z $.
	$d ph z $.
	$d ps z $.
	iunopab_0 $f set z $.
	funopab_0 $f wff ph $.
	funopab_1 $f wff ps $.
	funopab_2 $f set x $.
	funopab_3 $f set y $.
	unopab $p |- ( { <. x , y >. | ph } u. { <. x , y >. | ps } ) = { <. x , y >. | ( ph \/ ps ) } $= iunopab_0 sup_set_class funopab_2 sup_set_class funopab_3 sup_set_class cop wceq funopab_0 wa funopab_3 wex funopab_2 wex iunopab_0 cab iunopab_0 sup_set_class funopab_2 sup_set_class funopab_3 sup_set_class cop wceq funopab_1 wa funopab_3 wex funopab_2 wex iunopab_0 cab cun iunopab_0 sup_set_class funopab_2 sup_set_class funopab_3 sup_set_class cop wceq funopab_0 funopab_1 wo wa funopab_3 wex funopab_2 wex iunopab_0 cab funopab_0 funopab_2 funopab_3 copab funopab_1 funopab_2 funopab_3 copab cun funopab_0 funopab_1 wo funopab_2 funopab_3 copab iunopab_0 sup_set_class funopab_2 sup_set_class funopab_3 sup_set_class cop wceq funopab_0 wa funopab_3 wex funopab_2 wex iunopab_0 cab iunopab_0 sup_set_class funopab_2 sup_set_class funopab_3 sup_set_class cop wceq funopab_1 wa funopab_3 wex funopab_2 wex iunopab_0 cab cun iunopab_0 sup_set_class funopab_2 sup_set_class funopab_3 sup_set_class cop wceq funopab_0 wa funopab_3 wex funopab_2 wex iunopab_0 sup_set_class funopab_2 sup_set_class funopab_3 sup_set_class cop wceq funopab_1 wa funopab_3 wex funopab_2 wex wo iunopab_0 cab iunopab_0 sup_set_class funopab_2 sup_set_class funopab_3 sup_set_class cop wceq funopab_0 funopab_1 wo wa funopab_3 wex funopab_2 wex iunopab_0 cab iunopab_0 sup_set_class funopab_2 sup_set_class funopab_3 sup_set_class cop wceq funopab_0 wa funopab_3 wex funopab_2 wex iunopab_0 sup_set_class funopab_2 sup_set_class funopab_3 sup_set_class cop wceq funopab_1 wa funopab_3 wex funopab_2 wex iunopab_0 unab iunopab_0 sup_set_class funopab_2 sup_set_class funopab_3 sup_set_class cop wceq funopab_0 wa funopab_3 wex funopab_2 wex iunopab_0 sup_set_class funopab_2 sup_set_class funopab_3 sup_set_class cop wceq funopab_1 wa funopab_3 wex funopab_2 wex wo iunopab_0 sup_set_class funopab_2 sup_set_class funopab_3 sup_set_class cop wceq funopab_0 funopab_1 wo wa funopab_3 wex funopab_2 wex iunopab_0 iunopab_0 sup_set_class funopab_2 sup_set_class funopab_3 sup_set_class cop wceq funopab_0 wa funopab_3 wex funopab_2 wex iunopab_0 sup_set_class funopab_2 sup_set_class funopab_3 sup_set_class cop wceq funopab_1 wa funopab_3 wex funopab_2 wex wo iunopab_0 sup_set_class funopab_2 sup_set_class funopab_3 sup_set_class cop wceq funopab_0 wa funopab_3 wex iunopab_0 sup_set_class funopab_2 sup_set_class funopab_3 sup_set_class cop wceq funopab_1 wa funopab_3 wex wo funopab_2 wex iunopab_0 sup_set_class funopab_2 sup_set_class funopab_3 sup_set_class cop wceq funopab_0 funopab_1 wo wa funopab_3 wex funopab_2 wex iunopab_0 sup_set_class funopab_2 sup_set_class funopab_3 sup_set_class cop wceq funopab_0 wa funopab_3 wex iunopab_0 sup_set_class funopab_2 sup_set_class funopab_3 sup_set_class cop wceq funopab_1 wa funopab_3 wex funopab_2 19.43 iunopab_0 sup_set_class funopab_2 sup_set_class funopab_3 sup_set_class cop wceq funopab_0 wa funopab_3 wex iunopab_0 sup_set_class funopab_2 sup_set_class funopab_3 sup_set_class cop wceq funopab_1 wa funopab_3 wex wo iunopab_0 sup_set_class funopab_2 sup_set_class funopab_3 sup_set_class cop wceq funopab_0 funopab_1 wo wa funopab_3 wex funopab_2 iunopab_0 sup_set_class funopab_2 sup_set_class funopab_3 sup_set_class cop wceq funopab_0 funopab_1 wo wa funopab_3 wex iunopab_0 sup_set_class funopab_2 sup_set_class funopab_3 sup_set_class cop wceq funopab_0 wa iunopab_0 sup_set_class funopab_2 sup_set_class funopab_3 sup_set_class cop wceq funopab_1 wa wo funopab_3 wex iunopab_0 sup_set_class funopab_2 sup_set_class funopab_3 sup_set_class cop wceq funopab_0 wa funopab_3 wex iunopab_0 sup_set_class funopab_2 sup_set_class funopab_3 sup_set_class cop wceq funopab_1 wa funopab_3 wex wo iunopab_0 sup_set_class funopab_2 sup_set_class funopab_3 sup_set_class cop wceq funopab_0 funopab_1 wo wa iunopab_0 sup_set_class funopab_2 sup_set_class funopab_3 sup_set_class cop wceq funopab_0 wa iunopab_0 sup_set_class funopab_2 sup_set_class funopab_3 sup_set_class cop wceq funopab_1 wa wo funopab_3 iunopab_0 sup_set_class funopab_2 sup_set_class funopab_3 sup_set_class cop wceq funopab_0 funopab_1 andi exbii iunopab_0 sup_set_class funopab_2 sup_set_class funopab_3 sup_set_class cop wceq funopab_0 wa iunopab_0 sup_set_class funopab_2 sup_set_class funopab_3 sup_set_class cop wceq funopab_1 wa funopab_3 19.43 bitr2i exbii bitr3i abbii eqtri funopab_0 funopab_2 funopab_3 copab iunopab_0 sup_set_class funopab_2 sup_set_class funopab_3 sup_set_class cop wceq funopab_0 wa funopab_3 wex funopab_2 wex iunopab_0 cab funopab_1 funopab_2 funopab_3 copab iunopab_0 sup_set_class funopab_2 sup_set_class funopab_3 sup_set_class cop wceq funopab_1 wa funopab_3 wex funopab_2 wex iunopab_0 cab funopab_0 funopab_2 funopab_3 iunopab_0 df-opab funopab_1 funopab_2 funopab_3 iunopab_0 df-opab uneq12i funopab_0 funopab_1 wo funopab_2 funopab_3 iunopab_0 df-opab 3eqtr4i $.
$}
$( An equality theorem for the maps to notation.  (Contributed by Mario
       Carneiro, 16-Dec-2013.) $)
${
	$d x y $.
	$d y A $.
	$d y B $.
	$d y C $.
	$d y D $.
	impteq12f_0 $f set y $.
	fmpteq12f_0 $f set x $.
	fmpteq12f_1 $f class A $.
	fmpteq12f_2 $f class B $.
	fmpteq12f_3 $f class C $.
	fmpteq12f_4 $f class D $.
	mpteq12f $p |- ( ( A. x A = C /\ A. x e. A B = D ) -> ( x e. A |-> B ) = ( x e. C |-> D ) ) $= fmpteq12f_1 fmpteq12f_3 wceq fmpteq12f_0 wal fmpteq12f_2 fmpteq12f_4 wceq fmpteq12f_0 fmpteq12f_1 wral wa fmpteq12f_0 sup_set_class fmpteq12f_1 wcel impteq12f_0 sup_set_class fmpteq12f_2 wceq wa fmpteq12f_0 impteq12f_0 copab fmpteq12f_0 sup_set_class fmpteq12f_3 wcel impteq12f_0 sup_set_class fmpteq12f_4 wceq wa fmpteq12f_0 impteq12f_0 copab fmpteq12f_0 fmpteq12f_1 fmpteq12f_2 cmpt fmpteq12f_0 fmpteq12f_3 fmpteq12f_4 cmpt fmpteq12f_1 fmpteq12f_3 wceq fmpteq12f_0 wal fmpteq12f_2 fmpteq12f_4 wceq fmpteq12f_0 fmpteq12f_1 wral wa fmpteq12f_0 sup_set_class fmpteq12f_1 wcel impteq12f_0 sup_set_class fmpteq12f_2 wceq wa fmpteq12f_0 sup_set_class fmpteq12f_3 wcel impteq12f_0 sup_set_class fmpteq12f_4 wceq wa fmpteq12f_0 impteq12f_0 fmpteq12f_1 fmpteq12f_3 wceq fmpteq12f_0 wal fmpteq12f_2 fmpteq12f_4 wceq fmpteq12f_0 fmpteq12f_1 wral fmpteq12f_0 fmpteq12f_1 fmpteq12f_3 wceq fmpteq12f_0 nfa1 fmpteq12f_2 fmpteq12f_4 wceq fmpteq12f_0 fmpteq12f_1 nfra1 nfan fmpteq12f_1 fmpteq12f_3 wceq fmpteq12f_0 wal fmpteq12f_2 fmpteq12f_4 wceq fmpteq12f_0 fmpteq12f_1 wral wa impteq12f_0 nfv fmpteq12f_2 fmpteq12f_4 wceq fmpteq12f_0 fmpteq12f_1 wral fmpteq12f_0 sup_set_class fmpteq12f_1 wcel impteq12f_0 sup_set_class fmpteq12f_2 wceq wa fmpteq12f_0 sup_set_class fmpteq12f_1 wcel impteq12f_0 sup_set_class fmpteq12f_4 wceq wa fmpteq12f_1 fmpteq12f_3 wceq fmpteq12f_0 wal fmpteq12f_0 sup_set_class fmpteq12f_3 wcel impteq12f_0 sup_set_class fmpteq12f_4 wceq wa fmpteq12f_2 fmpteq12f_4 wceq fmpteq12f_0 fmpteq12f_1 wral fmpteq12f_0 sup_set_class fmpteq12f_1 wcel impteq12f_0 sup_set_class fmpteq12f_2 wceq impteq12f_0 sup_set_class fmpteq12f_4 wceq fmpteq12f_2 fmpteq12f_4 wceq fmpteq12f_0 fmpteq12f_1 wral fmpteq12f_0 sup_set_class fmpteq12f_1 wcel wa fmpteq12f_2 fmpteq12f_4 impteq12f_0 sup_set_class fmpteq12f_2 fmpteq12f_4 wceq fmpteq12f_0 fmpteq12f_1 wral fmpteq12f_0 sup_set_class fmpteq12f_1 wcel fmpteq12f_2 fmpteq12f_4 wceq fmpteq12f_2 fmpteq12f_4 wceq fmpteq12f_0 fmpteq12f_1 rsp imp eqeq2d pm5.32da fmpteq12f_1 fmpteq12f_3 wceq fmpteq12f_0 wal fmpteq12f_0 sup_set_class fmpteq12f_1 wcel fmpteq12f_0 sup_set_class fmpteq12f_3 wcel impteq12f_0 sup_set_class fmpteq12f_4 wceq fmpteq12f_1 fmpteq12f_3 wceq fmpteq12f_0 wal fmpteq12f_1 fmpteq12f_3 fmpteq12f_0 sup_set_class fmpteq12f_1 fmpteq12f_3 wceq fmpteq12f_0 sp eleq2d anbi1d sylan9bbr opabbid fmpteq12f_0 impteq12f_0 fmpteq12f_1 fmpteq12f_2 df-mpt fmpteq12f_0 impteq12f_0 fmpteq12f_3 fmpteq12f_4 df-mpt 3eqtr4g $.
$}
$( An equality inference for the maps to notation.  (Contributed by Mario
         Carneiro, 26-Jan-2017.) $)
${
	$d x ph $.
	fmpteq12dva_0 $f wff ph $.
	fmpteq12dva_1 $f set x $.
	fmpteq12dva_2 $f class A $.
	fmpteq12dva_3 $f class B $.
	fmpteq12dva_4 $f class C $.
	fmpteq12dva_5 $f class D $.
	empteq12dva_0 $e |- ( ph -> A = C ) $.
	empteq12dva_1 $e |- ( ( ph /\ x e. A ) -> B = D ) $.
	mpteq12dva $p |- ( ph -> ( x e. A |-> B ) = ( x e. C |-> D ) ) $= fmpteq12dva_0 fmpteq12dva_2 fmpteq12dva_4 wceq fmpteq12dva_1 wal fmpteq12dva_3 fmpteq12dva_5 wceq fmpteq12dva_1 fmpteq12dva_2 wral fmpteq12dva_1 fmpteq12dva_2 fmpteq12dva_3 cmpt fmpteq12dva_1 fmpteq12dva_4 fmpteq12dva_5 cmpt wceq fmpteq12dva_0 fmpteq12dva_2 fmpteq12dva_4 wceq fmpteq12dva_1 empteq12dva_0 alrimiv fmpteq12dva_0 fmpteq12dva_3 fmpteq12dva_5 wceq fmpteq12dva_1 fmpteq12dva_2 empteq12dva_1 ralrimiva fmpteq12dva_1 fmpteq12dva_2 fmpteq12dva_3 fmpteq12dva_4 fmpteq12dva_5 mpteq12f syl2anc $.
$}
$( An equality inference for the maps to notation.  (Contributed by NM,
       24-Aug-2011.)  (Revised by Mario Carneiro, 16-Dec-2013.) $)
${
	$d x ph $.
	fmpteq12dv_0 $f wff ph $.
	fmpteq12dv_1 $f set x $.
	fmpteq12dv_2 $f class A $.
	fmpteq12dv_3 $f class B $.
	fmpteq12dv_4 $f class C $.
	fmpteq12dv_5 $f class D $.
	empteq12dv_0 $e |- ( ph -> A = C ) $.
	empteq12dv_1 $e |- ( ph -> B = D ) $.
	mpteq12dv $p |- ( ph -> ( x e. A |-> B ) = ( x e. C |-> D ) ) $= fmpteq12dv_0 fmpteq12dv_1 fmpteq12dv_2 fmpteq12dv_3 fmpteq12dv_4 fmpteq12dv_5 empteq12dv_0 fmpteq12dv_0 fmpteq12dv_3 fmpteq12dv_5 wceq fmpteq12dv_1 sup_set_class fmpteq12dv_2 wcel empteq12dv_1 adantr mpteq12dva $.
$}
$( An equality theorem for the maps to notation.  (Contributed by NM,
       16-Dec-2013.) $)
${
	$d x A $.
	$d x C $.
	fmpteq12_0 $f set x $.
	fmpteq12_1 $f class A $.
	fmpteq12_2 $f class B $.
	fmpteq12_3 $f class C $.
	fmpteq12_4 $f class D $.
	mpteq12 $p |- ( ( A = C /\ A. x e. A B = D ) -> ( x e. A |-> B ) = ( x e. C |-> D ) ) $= fmpteq12_1 fmpteq12_3 wceq fmpteq12_1 fmpteq12_3 wceq fmpteq12_0 wal fmpteq12_2 fmpteq12_4 wceq fmpteq12_0 fmpteq12_1 wral fmpteq12_0 fmpteq12_1 fmpteq12_2 cmpt fmpteq12_0 fmpteq12_3 fmpteq12_4 cmpt wceq fmpteq12_1 fmpteq12_3 wceq fmpteq12_0 ax-17 fmpteq12_0 fmpteq12_1 fmpteq12_2 fmpteq12_3 fmpteq12_4 mpteq12f sylan $.
$}
$( An equality theorem for the maps to notation.  (Contributed by Mario
       Carneiro, 16-Dec-2013.) $)
${
	$d x A $.
	$d x B $.
	fmpteq1_0 $f set x $.
	fmpteq1_1 $f class A $.
	fmpteq1_2 $f class B $.
	fmpteq1_3 $f class C $.
	mpteq1 $p |- ( A = B -> ( x e. A |-> C ) = ( x e. B |-> C ) ) $= fmpteq1_1 fmpteq1_2 wceq fmpteq1_3 fmpteq1_3 wceq fmpteq1_0 fmpteq1_1 wral fmpteq1_0 fmpteq1_1 fmpteq1_3 cmpt fmpteq1_0 fmpteq1_2 fmpteq1_3 cmpt wceq fmpteq1_3 fmpteq1_3 wceq fmpteq1_0 fmpteq1_1 fmpteq1_0 sup_set_class fmpteq1_1 wcel fmpteq1_3 eqidd rgen fmpteq1_0 fmpteq1_1 fmpteq1_3 fmpteq1_2 fmpteq1_3 mpteq12 mpan2 $.
$}
$( An equality theorem for the maps to notation.  (Contributed by Mario
       Carneiro, 11-Jun-2016.) $)
${
	$d x A $.
	$d x B $.
	fmpteq1d_0 $f wff ph $.
	fmpteq1d_1 $f set x $.
	fmpteq1d_2 $f class A $.
	fmpteq1d_3 $f class B $.
	fmpteq1d_4 $f class C $.
	empteq1d_0 $e |- ( ph -> A = B ) $.
	mpteq1d $p |- ( ph -> ( x e. A |-> C ) = ( x e. B |-> C ) ) $= fmpteq1d_0 fmpteq1d_2 fmpteq1d_3 wceq fmpteq1d_1 fmpteq1d_2 fmpteq1d_4 cmpt fmpteq1d_1 fmpteq1d_3 fmpteq1d_4 cmpt wceq empteq1d_0 fmpteq1d_1 fmpteq1d_2 fmpteq1d_3 fmpteq1d_4 mpteq1 syl $.
$}
$( An equality inference for the maps to notation.  (Contributed by Mario
       Carneiro, 16-Dec-2013.) $)
${
	fmpteq2ia_0 $f set x $.
	fmpteq2ia_1 $f class A $.
	fmpteq2ia_2 $f class B $.
	fmpteq2ia_3 $f class C $.
	empteq2ia_0 $e |- ( x e. A -> B = C ) $.
	mpteq2ia $p |- ( x e. A |-> B ) = ( x e. A |-> C ) $= fmpteq2ia_1 fmpteq2ia_1 wceq fmpteq2ia_0 wal fmpteq2ia_2 fmpteq2ia_3 wceq fmpteq2ia_0 fmpteq2ia_1 wral fmpteq2ia_0 fmpteq2ia_1 fmpteq2ia_2 cmpt fmpteq2ia_0 fmpteq2ia_1 fmpteq2ia_3 cmpt wceq fmpteq2ia_1 fmpteq2ia_1 wceq fmpteq2ia_0 fmpteq2ia_1 eqid ax-gen fmpteq2ia_2 fmpteq2ia_3 wceq fmpteq2ia_0 fmpteq2ia_1 empteq2ia_0 rgen fmpteq2ia_0 fmpteq2ia_1 fmpteq2ia_2 fmpteq2ia_1 fmpteq2ia_3 mpteq12f mp2an $.
$}
$( An equality inference for the maps to notation.  (Contributed by Mario
       Carneiro, 16-Dec-2013.) $)
${
	fmpteq2i_0 $f set x $.
	fmpteq2i_1 $f class A $.
	fmpteq2i_2 $f class B $.
	fmpteq2i_3 $f class C $.
	empteq2i_0 $e |- B = C $.
	mpteq2i $p |- ( x e. A |-> B ) = ( x e. A |-> C ) $= fmpteq2i_0 fmpteq2i_1 fmpteq2i_2 fmpteq2i_3 fmpteq2i_2 fmpteq2i_3 wceq fmpteq2i_0 sup_set_class fmpteq2i_1 wcel empteq2i_0 a1i mpteq2ia $.
$}
$( An equality inference for the maps to notation.  (Contributed by Scott
       Fenton, 27-Oct-2010.)  (Revised by Mario Carneiro, 16-Dec-2013.) $)
${
	fmpteq12i_0 $f set x $.
	fmpteq12i_1 $f class A $.
	fmpteq12i_2 $f class B $.
	fmpteq12i_3 $f class C $.
	fmpteq12i_4 $f class D $.
	empteq12i_0 $e |- A = C $.
	empteq12i_1 $e |- B = D $.
	mpteq12i $p |- ( x e. A |-> B ) = ( x e. C |-> D ) $= fmpteq12i_0 fmpteq12i_1 fmpteq12i_2 cmpt fmpteq12i_0 fmpteq12i_3 fmpteq12i_4 cmpt wceq wtru fmpteq12i_0 fmpteq12i_1 fmpteq12i_2 fmpteq12i_3 fmpteq12i_4 fmpteq12i_1 fmpteq12i_3 wceq wtru empteq12i_0 a1i fmpteq12i_2 fmpteq12i_4 wceq wtru empteq12i_1 a1i mpteq12dv trud $.
$}
$( Slightly more general equality inference for the maps to notation.
       (Contributed by FL, 14-Sep-2013.)  (Revised by Mario Carneiro,
       16-Dec-2013.) $)
${
	fmpteq2da_0 $f wff ph $.
	fmpteq2da_1 $f set x $.
	fmpteq2da_2 $f class A $.
	fmpteq2da_3 $f class B $.
	fmpteq2da_4 $f class C $.
	empteq2da_0 $e |- F/ x ph $.
	empteq2da_1 $e |- ( ( ph /\ x e. A ) -> B = C ) $.
	mpteq2da $p |- ( ph -> ( x e. A |-> B ) = ( x e. A |-> C ) ) $= fmpteq2da_0 fmpteq2da_2 fmpteq2da_2 wceq fmpteq2da_1 wal fmpteq2da_3 fmpteq2da_4 wceq fmpteq2da_1 fmpteq2da_2 wral fmpteq2da_1 fmpteq2da_2 fmpteq2da_3 cmpt fmpteq2da_1 fmpteq2da_2 fmpteq2da_4 cmpt wceq fmpteq2da_2 fmpteq2da_2 wceq fmpteq2da_1 fmpteq2da_2 eqid ax-gen fmpteq2da_0 fmpteq2da_3 fmpteq2da_4 wceq fmpteq2da_1 fmpteq2da_2 empteq2da_0 fmpteq2da_0 fmpteq2da_1 sup_set_class fmpteq2da_2 wcel fmpteq2da_3 fmpteq2da_4 wceq empteq2da_1 ex ralrimi fmpteq2da_1 fmpteq2da_2 fmpteq2da_3 fmpteq2da_2 fmpteq2da_4 mpteq12f sylancr $.
$}
$( Slightly more general equality inference for the maps to notation.
       (Contributed by Scott Fenton, 25-Apr-2012.) $)
${
	$d x ph $.
	fmpteq2dva_0 $f wff ph $.
	fmpteq2dva_1 $f set x $.
	fmpteq2dva_2 $f class A $.
	fmpteq2dva_3 $f class B $.
	fmpteq2dva_4 $f class C $.
	empteq2dva_0 $e |- ( ( ph /\ x e. A ) -> B = C ) $.
	mpteq2dva $p |- ( ph -> ( x e. A |-> B ) = ( x e. A |-> C ) ) $= fmpteq2dva_0 fmpteq2dva_1 fmpteq2dva_2 fmpteq2dva_3 fmpteq2dva_4 fmpteq2dva_0 fmpteq2dva_1 nfv empteq2dva_0 mpteq2da $.
$}
$( An equality inference for the maps to notation.  (Contributed by Mario
       Carneiro, 23-Aug-2014.) $)
${
	$d x ph $.
	fmpteq2dv_0 $f wff ph $.
	fmpteq2dv_1 $f set x $.
	fmpteq2dv_2 $f class A $.
	fmpteq2dv_3 $f class B $.
	fmpteq2dv_4 $f class C $.
	empteq2dv_0 $e |- ( ph -> B = C ) $.
	mpteq2dv $p |- ( ph -> ( x e. A |-> B ) = ( x e. A |-> C ) ) $= fmpteq2dv_0 fmpteq2dv_1 fmpteq2dv_2 fmpteq2dv_3 fmpteq2dv_4 fmpteq2dv_0 fmpteq2dv_3 fmpteq2dv_4 wceq fmpteq2dv_1 sup_set_class fmpteq2dv_2 wcel empteq2dv_0 adantr mpteq2dva $.
$}
$( Bound-variable hypothesis builder for the maps-to notation.
       (Contributed by NM, 20-Feb-2013.) $)
${
	$d z A $.
	$d z B $.
	$d x y z $.
	infmpt_0 $f set z $.
	fnfmpt_0 $f set x $.
	fnfmpt_1 $f set y $.
	fnfmpt_2 $f class A $.
	fnfmpt_3 $f class B $.
	enfmpt_0 $e |- F/_ x A $.
	enfmpt_1 $e |- F/_ x B $.
	nfmpt $p |- F/_ x ( y e. A |-> B ) $= fnfmpt_0 fnfmpt_1 fnfmpt_2 fnfmpt_3 cmpt fnfmpt_1 sup_set_class fnfmpt_2 wcel infmpt_0 sup_set_class fnfmpt_3 wceq wa fnfmpt_1 infmpt_0 copab fnfmpt_1 infmpt_0 fnfmpt_2 fnfmpt_3 df-mpt fnfmpt_1 sup_set_class fnfmpt_2 wcel infmpt_0 sup_set_class fnfmpt_3 wceq wa fnfmpt_1 infmpt_0 fnfmpt_0 fnfmpt_1 sup_set_class fnfmpt_2 wcel infmpt_0 sup_set_class fnfmpt_3 wceq fnfmpt_0 fnfmpt_0 fnfmpt_1 fnfmpt_2 enfmpt_0 nfcri fnfmpt_0 infmpt_0 sup_set_class fnfmpt_3 enfmpt_1 nfeq2 nfan nfopab nfcxfr $.
$}
$( Bound-variable hypothesis builder for the maps-to notation.
       (Contributed by FL, 17-Feb-2008.) $)
${
	$d A z $.
	$d B z $.
	$d x z $.
	infmpt1_0 $f set z $.
	fnfmpt1_0 $f set x $.
	fnfmpt1_1 $f class A $.
	fnfmpt1_2 $f class B $.
	nfmpt1 $p |- F/_ x ( x e. A |-> B ) $= fnfmpt1_0 fnfmpt1_0 fnfmpt1_1 fnfmpt1_2 cmpt fnfmpt1_0 sup_set_class fnfmpt1_1 wcel infmpt1_0 sup_set_class fnfmpt1_2 wceq wa fnfmpt1_0 infmpt1_0 copab fnfmpt1_0 infmpt1_0 fnfmpt1_1 fnfmpt1_2 df-mpt fnfmpt1_0 sup_set_class fnfmpt1_1 wcel infmpt1_0 sup_set_class fnfmpt1_2 wceq wa fnfmpt1_0 infmpt1_0 nfopab1 nfcxfr $.
$}
$( Rule to change the bound variable in a maps-to function, using implicit
       substitution.  This version has bound-variable hypotheses in place of
       distinct variable conditions.  (Contributed by NM, 11-Sep-2011.) $)
${
	$d w z x A $.
	$d w z y A $.
	$d w z B $.
	$d w z C $.
	icbvmpt_0 $f set z $.
	icbvmpt_1 $f set w $.
	fcbvmpt_0 $f set x $.
	fcbvmpt_1 $f set y $.
	fcbvmpt_2 $f class A $.
	fcbvmpt_3 $f class B $.
	fcbvmpt_4 $f class C $.
	ecbvmpt_0 $e |- F/_ y B $.
	ecbvmpt_1 $e |- F/_ x C $.
	ecbvmpt_2 $e |- ( x = y -> B = C ) $.
	cbvmpt $p |- ( x e. A |-> B ) = ( y e. A |-> C ) $= fcbvmpt_0 sup_set_class fcbvmpt_2 wcel icbvmpt_0 sup_set_class fcbvmpt_3 wceq wa fcbvmpt_0 icbvmpt_0 copab fcbvmpt_1 sup_set_class fcbvmpt_2 wcel icbvmpt_0 sup_set_class fcbvmpt_4 wceq wa fcbvmpt_1 icbvmpt_0 copab fcbvmpt_0 fcbvmpt_2 fcbvmpt_3 cmpt fcbvmpt_1 fcbvmpt_2 fcbvmpt_4 cmpt fcbvmpt_0 sup_set_class fcbvmpt_2 wcel icbvmpt_0 sup_set_class fcbvmpt_3 wceq wa fcbvmpt_0 icbvmpt_0 copab icbvmpt_1 sup_set_class fcbvmpt_2 wcel icbvmpt_0 sup_set_class fcbvmpt_3 wceq fcbvmpt_0 icbvmpt_1 wsb wa icbvmpt_1 icbvmpt_0 copab fcbvmpt_1 sup_set_class fcbvmpt_2 wcel icbvmpt_0 sup_set_class fcbvmpt_4 wceq wa fcbvmpt_1 icbvmpt_0 copab fcbvmpt_0 sup_set_class fcbvmpt_2 wcel icbvmpt_0 sup_set_class fcbvmpt_3 wceq wa icbvmpt_1 sup_set_class fcbvmpt_2 wcel icbvmpt_0 sup_set_class fcbvmpt_3 wceq fcbvmpt_0 icbvmpt_1 wsb wa fcbvmpt_0 icbvmpt_0 icbvmpt_1 fcbvmpt_0 sup_set_class fcbvmpt_2 wcel icbvmpt_0 sup_set_class fcbvmpt_3 wceq wa icbvmpt_1 nfv icbvmpt_1 sup_set_class fcbvmpt_2 wcel icbvmpt_0 sup_set_class fcbvmpt_3 wceq fcbvmpt_0 icbvmpt_1 wsb fcbvmpt_0 icbvmpt_1 sup_set_class fcbvmpt_2 wcel fcbvmpt_0 nfv icbvmpt_0 sup_set_class fcbvmpt_3 wceq fcbvmpt_0 icbvmpt_1 nfs1v nfan fcbvmpt_0 sup_set_class icbvmpt_1 sup_set_class wceq fcbvmpt_0 sup_set_class fcbvmpt_2 wcel icbvmpt_1 sup_set_class fcbvmpt_2 wcel icbvmpt_0 sup_set_class fcbvmpt_3 wceq icbvmpt_0 sup_set_class fcbvmpt_3 wceq fcbvmpt_0 icbvmpt_1 wsb fcbvmpt_0 sup_set_class icbvmpt_1 sup_set_class fcbvmpt_2 eleq1 icbvmpt_0 sup_set_class fcbvmpt_3 wceq fcbvmpt_0 icbvmpt_1 sbequ12 anbi12d cbvopab1 icbvmpt_1 sup_set_class fcbvmpt_2 wcel icbvmpt_0 sup_set_class fcbvmpt_3 wceq fcbvmpt_0 icbvmpt_1 wsb wa fcbvmpt_1 sup_set_class fcbvmpt_2 wcel icbvmpt_0 sup_set_class fcbvmpt_4 wceq wa icbvmpt_1 icbvmpt_0 fcbvmpt_1 icbvmpt_1 sup_set_class fcbvmpt_2 wcel icbvmpt_0 sup_set_class fcbvmpt_3 wceq fcbvmpt_0 icbvmpt_1 wsb fcbvmpt_1 icbvmpt_1 sup_set_class fcbvmpt_2 wcel fcbvmpt_1 nfv icbvmpt_0 sup_set_class fcbvmpt_3 wceq fcbvmpt_0 icbvmpt_1 fcbvmpt_1 fcbvmpt_1 icbvmpt_0 sup_set_class fcbvmpt_3 ecbvmpt_0 nfeq2 nfsb nfan fcbvmpt_1 sup_set_class fcbvmpt_2 wcel icbvmpt_0 sup_set_class fcbvmpt_4 wceq wa icbvmpt_1 nfv icbvmpt_1 sup_set_class fcbvmpt_1 sup_set_class wceq icbvmpt_1 sup_set_class fcbvmpt_2 wcel fcbvmpt_1 sup_set_class fcbvmpt_2 wcel icbvmpt_0 sup_set_class fcbvmpt_3 wceq fcbvmpt_0 icbvmpt_1 wsb icbvmpt_0 sup_set_class fcbvmpt_4 wceq icbvmpt_1 sup_set_class fcbvmpt_1 sup_set_class fcbvmpt_2 eleq1 icbvmpt_1 sup_set_class fcbvmpt_1 sup_set_class wceq icbvmpt_0 sup_set_class fcbvmpt_3 wceq fcbvmpt_0 icbvmpt_1 wsb icbvmpt_0 sup_set_class fcbvmpt_3 wceq fcbvmpt_0 fcbvmpt_1 wsb icbvmpt_0 sup_set_class fcbvmpt_4 wceq icbvmpt_0 sup_set_class fcbvmpt_3 wceq icbvmpt_1 fcbvmpt_1 fcbvmpt_0 sbequ icbvmpt_0 sup_set_class fcbvmpt_3 wceq icbvmpt_0 sup_set_class fcbvmpt_4 wceq fcbvmpt_0 fcbvmpt_1 fcbvmpt_0 icbvmpt_0 sup_set_class fcbvmpt_4 ecbvmpt_1 nfeq2 fcbvmpt_0 sup_set_class fcbvmpt_1 sup_set_class wceq fcbvmpt_3 fcbvmpt_4 icbvmpt_0 sup_set_class ecbvmpt_2 eqeq2d sbie syl6bb anbi12d cbvopab1 eqtri fcbvmpt_0 icbvmpt_0 fcbvmpt_2 fcbvmpt_3 df-mpt fcbvmpt_1 icbvmpt_0 fcbvmpt_2 fcbvmpt_4 df-mpt 3eqtr4i $.
$}
$( Rule to change the bound variable in a maps-to function, using implicit
       substitution.  (Contributed by Mario Carneiro, 19-Feb-2013.) $)
${
	$d A x $.
	$d A y $.
	$d B y $.
	$d C x $.
	fcbvmptv_0 $f set x $.
	fcbvmptv_1 $f set y $.
	fcbvmptv_2 $f class A $.
	fcbvmptv_3 $f class B $.
	fcbvmptv_4 $f class C $.
	ecbvmptv_0 $e |- ( x = y -> B = C ) $.
	cbvmptv $p |- ( x e. A |-> B ) = ( y e. A |-> C ) $= fcbvmptv_0 fcbvmptv_1 fcbvmptv_2 fcbvmptv_3 fcbvmptv_4 fcbvmptv_1 fcbvmptv_3 nfcv fcbvmptv_0 fcbvmptv_4 nfcv ecbvmptv_0 cbvmpt $.
$}
$( Function with universal domain in maps-to notation.  (Contributed by NM,
       16-Aug-2013.) $)
${
	$d x y $.
	$d y B $.
	fmptv_0 $f set x $.
	fmptv_1 $f set y $.
	fmptv_2 $f class B $.
	mptv $p |- ( x e. _V |-> B ) = { <. x , y >. | y = B } $= fmptv_0 cvv fmptv_2 cmpt fmptv_0 sup_set_class cvv wcel fmptv_1 sup_set_class fmptv_2 wceq wa fmptv_0 fmptv_1 copab fmptv_1 sup_set_class fmptv_2 wceq fmptv_0 fmptv_1 copab fmptv_0 fmptv_1 cvv fmptv_2 df-mpt fmptv_1 sup_set_class fmptv_2 wceq fmptv_0 sup_set_class cvv wcel fmptv_1 sup_set_class fmptv_2 wceq wa fmptv_0 fmptv_1 fmptv_0 sup_set_class cvv wcel fmptv_1 sup_set_class fmptv_2 wceq fmptv_0 vex biantrur opabbii eqtr4i $.
$}

