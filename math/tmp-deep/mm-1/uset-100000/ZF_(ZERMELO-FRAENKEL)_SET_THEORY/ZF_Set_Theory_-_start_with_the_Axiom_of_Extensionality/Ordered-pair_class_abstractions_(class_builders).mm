$[ turnstile_special_source.mm $]

$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/Binary_relations.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                Ordered-pair class abstractions (class builders)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$c |-> $.

$(Maps-to symbol $)

$(Extend class notation to include ordered-pair class abstraction (class
     builder). $)

${
	$v ph x y  $.
	f0_copab $f wff ph $.
	f1_copab $f set x $.
	f2_copab $f set y $.
	a_copab $a class { <. x , y >. | ph } $.
$}

$(Extend the definition of a class to include maps-to notation for defining
     a function via a rule. $)

${
	$v x A B  $.
	f0_cmpt $f set x $.
	f1_cmpt $f class A $.
	f2_cmpt $f class B $.
	a_cmpt $a class ( x e. A |-> B ) $.
$}

$(Define the class abstraction of a collection of ordered pairs.
       Definition 3.3 of [Monk1] p. 34.  Usually ` x ` and ` y ` are distinct,
       although the definition doesn't strictly require it (see ~ dfid2 for a
       case where they are not distinct).  The brace notation is called "class
       abstraction" by Quine; it is also (more commonly) called a "class
       builder" in the literature.  An alternate definition using no
       existential quantifiers is shown by ~ dfopab2 .  For example,
` R = { <. x , y >. | ( x e. CC /\ y e. CC /\ ( x + 1 ) = y ) } -> 3 R 4 `
       ( ~ ex-opab ).  (Contributed by NM, 4-Jul-1994.) $)

${
	$v ph x y z  $.
	$d x z  $.
	$d y z  $.
	$d z ph  $.
	f0_df-opab $f wff ph $.
	f1_df-opab $f set x $.
	f2_df-opab $f set y $.
	f3_df-opab $f set z $.
	a_df-opab $a |- { <. x , y >. | ph } = { z | E. x E. y ( z = <. x , y >. /\ ph ) } $.
$}

$(Define maps-to notation for defining a function via a rule.  Read as
       "the function defined by the map from ` x ` (in ` A ` ) to
       ` B ( x ) ` ."  The class expression ` B ` is the value of the function
       at ` x ` and normally contains the variable ` x ` .  An example is the
       square function for complex numbers, ` ( x e. CC |-> ( x ^ 2 ) ) ` .
       Similar to the definition of mapping in [ChoquetDD] p. 2.  (Contributed
       by NM, 17-Feb-2008.) $)

${
	$v x y A B  $.
	$d x y  $.
	$d y A  $.
	$d y B  $.
	f0_df-mpt $f set x $.
	f1_df-mpt $f set y $.
	f2_df-mpt $f class A $.
	f3_df-mpt $f class B $.
	a_df-mpt $a |- ( x e. A |-> B ) = { <. x , y >. | ( x e. A /\ y = B ) } $.
$}

$(The collection of ordered pairs in a class is a subclass of it.
       (Contributed by NM, 27-Dec-1996.)  (Proof shortened by Andrew Salmon,
       9-Jul-2011.) $)

${
	$v x y R  $.
	$d x z R  $.
	$d y z R  $.
	f0_opabss $f set x $.
	f1_opabss $f set y $.
	f2_opabss $f class R $.
	i0_opabss $f set z $.
	p_opabss $p |- { <. x , y >. | x R y } C_ R $= f0_opabss a_sup_set_class f1_opabss a_sup_set_class f2_opabss a_wbr f0_opabss f1_opabss i0_opabss a_df-opab f0_opabss a_sup_set_class f1_opabss a_sup_set_class f2_opabss a_df-br i0_opabss a_sup_set_class f0_opabss a_sup_set_class f1_opabss a_sup_set_class a_cop f2_opabss p_eleq1 i0_opabss a_sup_set_class f0_opabss a_sup_set_class f1_opabss a_sup_set_class a_cop a_wceq i0_opabss a_sup_set_class f2_opabss a_wcel f0_opabss a_sup_set_class f1_opabss a_sup_set_class a_cop f2_opabss a_wcel p_biimpar f0_opabss a_sup_set_class f1_opabss a_sup_set_class f2_opabss a_wbr i0_opabss a_sup_set_class f0_opabss a_sup_set_class f1_opabss a_sup_set_class a_cop a_wceq f0_opabss a_sup_set_class f1_opabss a_sup_set_class a_cop f2_opabss a_wcel i0_opabss a_sup_set_class f2_opabss a_wcel p_sylan2b i0_opabss a_sup_set_class f0_opabss a_sup_set_class f1_opabss a_sup_set_class a_cop a_wceq f0_opabss a_sup_set_class f1_opabss a_sup_set_class f2_opabss a_wbr a_wa i0_opabss a_sup_set_class f2_opabss a_wcel f0_opabss f1_opabss p_exlimivv i0_opabss a_sup_set_class f0_opabss a_sup_set_class f1_opabss a_sup_set_class a_cop a_wceq f0_opabss a_sup_set_class f1_opabss a_sup_set_class f2_opabss a_wbr a_wa f1_opabss a_wex f0_opabss a_wex i0_opabss f2_opabss p_abssi f0_opabss a_sup_set_class f1_opabss a_sup_set_class f2_opabss a_wbr f0_opabss f1_opabss a_copab i0_opabss a_sup_set_class f0_opabss a_sup_set_class f1_opabss a_sup_set_class a_cop a_wceq f0_opabss a_sup_set_class f1_opabss a_sup_set_class f2_opabss a_wbr a_wa f1_opabss a_wex f0_opabss a_wex i0_opabss a_cab f2_opabss p_eqsstri $.
$}

$(Equivalent wff's yield equal ordered-pair class abstractions (deduction
       rule).  (Contributed by NM, 21-Feb-2004.)  (Proof shortened by Andrew
       Salmon, 9-Jul-2011.) $)

${
	$v ph ps ch x y  $.
	$d x z  $.
	$d y z  $.
	$d z ph  $.
	$d z ps  $.
	$d z ch  $.
	f0_opabbid $f wff ph $.
	f1_opabbid $f wff ps $.
	f2_opabbid $f wff ch $.
	f3_opabbid $f set x $.
	f4_opabbid $f set y $.
	i0_opabbid $f set z $.
	e0_opabbid $e |- F/ x ph $.
	e1_opabbid $e |- F/ y ph $.
	e2_opabbid $e |- ( ph -> ( ps <-> ch ) ) $.
	p_opabbid $p |- ( ph -> { <. x , y >. | ps } = { <. x , y >. | ch } ) $= e0_opabbid e1_opabbid e2_opabbid f0_opabbid f1_opabbid f2_opabbid i0_opabbid a_sup_set_class f3_opabbid a_sup_set_class f4_opabbid a_sup_set_class a_cop a_wceq p_anbi2d f0_opabbid i0_opabbid a_sup_set_class f3_opabbid a_sup_set_class f4_opabbid a_sup_set_class a_cop a_wceq f1_opabbid a_wa i0_opabbid a_sup_set_class f3_opabbid a_sup_set_class f4_opabbid a_sup_set_class a_cop a_wceq f2_opabbid a_wa f4_opabbid p_exbid f0_opabbid i0_opabbid a_sup_set_class f3_opabbid a_sup_set_class f4_opabbid a_sup_set_class a_cop a_wceq f1_opabbid a_wa f4_opabbid a_wex i0_opabbid a_sup_set_class f3_opabbid a_sup_set_class f4_opabbid a_sup_set_class a_cop a_wceq f2_opabbid a_wa f4_opabbid a_wex f3_opabbid p_exbid f0_opabbid i0_opabbid a_sup_set_class f3_opabbid a_sup_set_class f4_opabbid a_sup_set_class a_cop a_wceq f1_opabbid a_wa f4_opabbid a_wex f3_opabbid a_wex i0_opabbid a_sup_set_class f3_opabbid a_sup_set_class f4_opabbid a_sup_set_class a_cop a_wceq f2_opabbid a_wa f4_opabbid a_wex f3_opabbid a_wex i0_opabbid p_abbidv f1_opabbid f3_opabbid f4_opabbid i0_opabbid a_df-opab f2_opabbid f3_opabbid f4_opabbid i0_opabbid a_df-opab f0_opabbid i0_opabbid a_sup_set_class f3_opabbid a_sup_set_class f4_opabbid a_sup_set_class a_cop a_wceq f1_opabbid a_wa f4_opabbid a_wex f3_opabbid a_wex i0_opabbid a_cab i0_opabbid a_sup_set_class f3_opabbid a_sup_set_class f4_opabbid a_sup_set_class a_cop a_wceq f2_opabbid a_wa f4_opabbid a_wex f3_opabbid a_wex i0_opabbid a_cab f1_opabbid f3_opabbid f4_opabbid a_copab f2_opabbid f3_opabbid f4_opabbid a_copab p_3eqtr4g $.
$}

$(Equivalent wff's yield equal ordered-pair class abstractions (deduction
       rule).  (Contributed by NM, 15-May-1995.) $)

${
	$v ph ps ch x y  $.
	$d x ph  $.
	$d y ph  $.
	$d ps  $.
	$d ch  $.
	f0_opabbidv $f wff ph $.
	f1_opabbidv $f wff ps $.
	f2_opabbidv $f wff ch $.
	f3_opabbidv $f set x $.
	f4_opabbidv $f set y $.
	e0_opabbidv $e |- ( ph -> ( ps <-> ch ) ) $.
	p_opabbidv $p |- ( ph -> { <. x , y >. | ps } = { <. x , y >. | ch } ) $= f0_opabbidv f3_opabbidv p_nfv f0_opabbidv f4_opabbidv p_nfv e0_opabbidv f0_opabbidv f1_opabbidv f2_opabbidv f3_opabbidv f4_opabbidv p_opabbid $.
$}

$(Equivalent wff's yield equal class abstractions.  (Contributed by NM,
       15-May-1995.) $)

${
	$v ph ps x y  $.
	$d x z  $.
	$d y z  $.
	$d z ph  $.
	$d z ps  $.
	f0_opabbii $f wff ph $.
	f1_opabbii $f wff ps $.
	f2_opabbii $f set x $.
	f3_opabbii $f set y $.
	i0_opabbii $f set z $.
	e0_opabbii $e |- ( ph <-> ps ) $.
	p_opabbii $p |- { <. x , y >. | ph } = { <. x , y >. | ps } $= i0_opabbii a_sup_set_class p_eqid e0_opabbii f0_opabbii f1_opabbii a_wb i0_opabbii a_sup_set_class i0_opabbii a_sup_set_class a_wceq p_a1i i0_opabbii a_sup_set_class i0_opabbii a_sup_set_class a_wceq f0_opabbii f1_opabbii f2_opabbii f3_opabbii p_opabbidv i0_opabbii a_sup_set_class i0_opabbii a_sup_set_class a_wceq f0_opabbii f2_opabbii f3_opabbii a_copab f1_opabbii f2_opabbii f3_opabbii a_copab a_wceq a_ax-mp $.
$}

$(Bound-variable hypothesis builder for class abstraction.  (Contributed
       by NM, 1-Sep-1999.)  (Unnecessary distinct variable restrictions were
       removed by Andrew Salmon, 11-Jul-2011.) $)

${
	$v ph x y z  $.
	$d x z w  $.
	$d y z w  $.
	$d ph w  $.
	f0_nfopab $f wff ph $.
	f1_nfopab $f set x $.
	f2_nfopab $f set y $.
	f3_nfopab $f set z $.
	i0_nfopab $f set w $.
	e0_nfopab $e |- F/ z ph $.
	p_nfopab $p |- F/_ z { <. x , y >. | ph } $= f0_nfopab f1_nfopab f2_nfopab i0_nfopab a_df-opab i0_nfopab a_sup_set_class f1_nfopab a_sup_set_class f2_nfopab a_sup_set_class a_cop a_wceq f3_nfopab p_nfv e0_nfopab i0_nfopab a_sup_set_class f1_nfopab a_sup_set_class f2_nfopab a_sup_set_class a_cop a_wceq f0_nfopab f3_nfopab p_nfan i0_nfopab a_sup_set_class f1_nfopab a_sup_set_class f2_nfopab a_sup_set_class a_cop a_wceq f0_nfopab a_wa f3_nfopab f2_nfopab p_nfex i0_nfopab a_sup_set_class f1_nfopab a_sup_set_class f2_nfopab a_sup_set_class a_cop a_wceq f0_nfopab a_wa f2_nfopab a_wex f3_nfopab f1_nfopab p_nfex i0_nfopab a_sup_set_class f1_nfopab a_sup_set_class f2_nfopab a_sup_set_class a_cop a_wceq f0_nfopab a_wa f2_nfopab a_wex f1_nfopab a_wex f3_nfopab i0_nfopab p_nfab f3_nfopab f0_nfopab f1_nfopab f2_nfopab a_copab i0_nfopab a_sup_set_class f1_nfopab a_sup_set_class f2_nfopab a_sup_set_class a_cop a_wceq f0_nfopab a_wa f2_nfopab a_wex f1_nfopab a_wex i0_nfopab a_cab p_nfcxfr $.
$}

$(The first abstraction variable in an ordered-pair class abstraction
       (class builder) is effectively not free.  (Contributed by NM,
       16-May-1995.)  (Revised by Mario Carneiro, 14-Oct-2016.) $)

${
	$v ph x y  $.
	$d x z  $.
	$d y z  $.
	$d z ph  $.
	f0_nfopab1 $f wff ph $.
	f1_nfopab1 $f set x $.
	f2_nfopab1 $f set y $.
	i0_nfopab1 $f set z $.
	p_nfopab1 $p |- F/_ x { <. x , y >. | ph } $= f0_nfopab1 f1_nfopab1 f2_nfopab1 i0_nfopab1 a_df-opab i0_nfopab1 a_sup_set_class f1_nfopab1 a_sup_set_class f2_nfopab1 a_sup_set_class a_cop a_wceq f0_nfopab1 a_wa f2_nfopab1 a_wex f1_nfopab1 p_nfe1 i0_nfopab1 a_sup_set_class f1_nfopab1 a_sup_set_class f2_nfopab1 a_sup_set_class a_cop a_wceq f0_nfopab1 a_wa f2_nfopab1 a_wex f1_nfopab1 a_wex f1_nfopab1 i0_nfopab1 p_nfab f1_nfopab1 f0_nfopab1 f1_nfopab1 f2_nfopab1 a_copab i0_nfopab1 a_sup_set_class f1_nfopab1 a_sup_set_class f2_nfopab1 a_sup_set_class a_cop a_wceq f0_nfopab1 a_wa f2_nfopab1 a_wex f1_nfopab1 a_wex i0_nfopab1 a_cab p_nfcxfr $.
$}

$(The second abstraction variable in an ordered-pair class abstraction
       (class builder) is effectively not free.  (Contributed by NM,
       16-May-1995.)  (Revised by Mario Carneiro, 14-Oct-2016.) $)

${
	$v ph x y  $.
	$d x z  $.
	$d y z  $.
	$d z ph  $.
	f0_nfopab2 $f wff ph $.
	f1_nfopab2 $f set x $.
	f2_nfopab2 $f set y $.
	i0_nfopab2 $f set z $.
	p_nfopab2 $p |- F/_ y { <. x , y >. | ph } $= f0_nfopab2 f1_nfopab2 f2_nfopab2 i0_nfopab2 a_df-opab i0_nfopab2 a_sup_set_class f1_nfopab2 a_sup_set_class f2_nfopab2 a_sup_set_class a_cop a_wceq f0_nfopab2 a_wa f2_nfopab2 p_nfe1 i0_nfopab2 a_sup_set_class f1_nfopab2 a_sup_set_class f2_nfopab2 a_sup_set_class a_cop a_wceq f0_nfopab2 a_wa f2_nfopab2 a_wex f2_nfopab2 f1_nfopab2 p_nfex i0_nfopab2 a_sup_set_class f1_nfopab2 a_sup_set_class f2_nfopab2 a_sup_set_class a_cop a_wceq f0_nfopab2 a_wa f2_nfopab2 a_wex f1_nfopab2 a_wex f2_nfopab2 i0_nfopab2 p_nfab f2_nfopab2 f0_nfopab2 f1_nfopab2 f2_nfopab2 a_copab i0_nfopab2 a_sup_set_class f1_nfopab2 a_sup_set_class f2_nfopab2 a_sup_set_class a_cop a_wceq f0_nfopab2 a_wa f2_nfopab2 a_wex f1_nfopab2 a_wex i0_nfopab2 a_cab p_nfcxfr $.
$}

$(Rule used to change bound variables in an ordered-pair class
       abstraction, using implicit substitution.  (Contributed by NM,
       14-Sep-2003.) $)

${
	$v ph ps x y z w  $.
	$d x y z w v  $.
	$d v ph  $.
	$d v ps  $.
	f0_cbvopab $f wff ph $.
	f1_cbvopab $f wff ps $.
	f2_cbvopab $f set x $.
	f3_cbvopab $f set y $.
	f4_cbvopab $f set z $.
	f5_cbvopab $f set w $.
	i0_cbvopab $f set v $.
	e0_cbvopab $e |- F/ z ph $.
	e1_cbvopab $e |- F/ w ph $.
	e2_cbvopab $e |- F/ x ps $.
	e3_cbvopab $e |- F/ y ps $.
	e4_cbvopab $e |- ( ( x = z /\ y = w ) -> ( ph <-> ps ) ) $.
	p_cbvopab $p |- { <. x , y >. | ph } = { <. z , w >. | ps } $= i0_cbvopab a_sup_set_class f2_cbvopab a_sup_set_class f3_cbvopab a_sup_set_class a_cop a_wceq f4_cbvopab p_nfv e0_cbvopab i0_cbvopab a_sup_set_class f2_cbvopab a_sup_set_class f3_cbvopab a_sup_set_class a_cop a_wceq f0_cbvopab f4_cbvopab p_nfan i0_cbvopab a_sup_set_class f2_cbvopab a_sup_set_class f3_cbvopab a_sup_set_class a_cop a_wceq f5_cbvopab p_nfv e1_cbvopab i0_cbvopab a_sup_set_class f2_cbvopab a_sup_set_class f3_cbvopab a_sup_set_class a_cop a_wceq f0_cbvopab f5_cbvopab p_nfan i0_cbvopab a_sup_set_class f4_cbvopab a_sup_set_class f5_cbvopab a_sup_set_class a_cop a_wceq f2_cbvopab p_nfv e2_cbvopab i0_cbvopab a_sup_set_class f4_cbvopab a_sup_set_class f5_cbvopab a_sup_set_class a_cop a_wceq f1_cbvopab f2_cbvopab p_nfan i0_cbvopab a_sup_set_class f4_cbvopab a_sup_set_class f5_cbvopab a_sup_set_class a_cop a_wceq f3_cbvopab p_nfv e3_cbvopab i0_cbvopab a_sup_set_class f4_cbvopab a_sup_set_class f5_cbvopab a_sup_set_class a_cop a_wceq f1_cbvopab f3_cbvopab p_nfan f2_cbvopab a_sup_set_class f3_cbvopab a_sup_set_class f4_cbvopab a_sup_set_class f5_cbvopab a_sup_set_class p_opeq12 f2_cbvopab a_sup_set_class f4_cbvopab a_sup_set_class a_wceq f3_cbvopab a_sup_set_class f5_cbvopab a_sup_set_class a_wceq a_wa f2_cbvopab a_sup_set_class f3_cbvopab a_sup_set_class a_cop f4_cbvopab a_sup_set_class f5_cbvopab a_sup_set_class a_cop i0_cbvopab a_sup_set_class p_eqeq2d e4_cbvopab f2_cbvopab a_sup_set_class f4_cbvopab a_sup_set_class a_wceq f3_cbvopab a_sup_set_class f5_cbvopab a_sup_set_class a_wceq a_wa i0_cbvopab a_sup_set_class f2_cbvopab a_sup_set_class f3_cbvopab a_sup_set_class a_cop a_wceq i0_cbvopab a_sup_set_class f4_cbvopab a_sup_set_class f5_cbvopab a_sup_set_class a_cop a_wceq f0_cbvopab f1_cbvopab p_anbi12d i0_cbvopab a_sup_set_class f2_cbvopab a_sup_set_class f3_cbvopab a_sup_set_class a_cop a_wceq f0_cbvopab a_wa i0_cbvopab a_sup_set_class f4_cbvopab a_sup_set_class f5_cbvopab a_sup_set_class a_cop a_wceq f1_cbvopab a_wa f2_cbvopab f3_cbvopab f4_cbvopab f5_cbvopab p_cbvex2 i0_cbvopab a_sup_set_class f2_cbvopab a_sup_set_class f3_cbvopab a_sup_set_class a_cop a_wceq f0_cbvopab a_wa f3_cbvopab a_wex f2_cbvopab a_wex i0_cbvopab a_sup_set_class f4_cbvopab a_sup_set_class f5_cbvopab a_sup_set_class a_cop a_wceq f1_cbvopab a_wa f5_cbvopab a_wex f4_cbvopab a_wex i0_cbvopab p_abbii f0_cbvopab f2_cbvopab f3_cbvopab i0_cbvopab a_df-opab f1_cbvopab f4_cbvopab f5_cbvopab i0_cbvopab a_df-opab i0_cbvopab a_sup_set_class f2_cbvopab a_sup_set_class f3_cbvopab a_sup_set_class a_cop a_wceq f0_cbvopab a_wa f3_cbvopab a_wex f2_cbvopab a_wex i0_cbvopab a_cab i0_cbvopab a_sup_set_class f4_cbvopab a_sup_set_class f5_cbvopab a_sup_set_class a_cop a_wceq f1_cbvopab a_wa f5_cbvopab a_wex f4_cbvopab a_wex i0_cbvopab a_cab f0_cbvopab f2_cbvopab f3_cbvopab a_copab f1_cbvopab f4_cbvopab f5_cbvopab a_copab p_3eqtr4i $.
$}

$(Rule used to change bound variables in an ordered-pair class
       abstraction, using implicit substitution.  (Contributed by NM,
       15-Oct-1996.) $)

${
	$v ph ps x y z w  $.
	$d x y z w  $.
	$d z w ph  $.
	$d x y ps  $.
	f0_cbvopabv $f wff ph $.
	f1_cbvopabv $f wff ps $.
	f2_cbvopabv $f set x $.
	f3_cbvopabv $f set y $.
	f4_cbvopabv $f set z $.
	f5_cbvopabv $f set w $.
	e0_cbvopabv $e |- ( ( x = z /\ y = w ) -> ( ph <-> ps ) ) $.
	p_cbvopabv $p |- { <. x , y >. | ph } = { <. z , w >. | ps } $= f0_cbvopabv f4_cbvopabv p_nfv f0_cbvopabv f5_cbvopabv p_nfv f1_cbvopabv f2_cbvopabv p_nfv f1_cbvopabv f3_cbvopabv p_nfv e0_cbvopabv f0_cbvopabv f1_cbvopabv f2_cbvopabv f3_cbvopabv f4_cbvopabv f5_cbvopabv p_cbvopab $.
$}

$(Change first bound variable in an ordered-pair class abstraction, using
       explicit substitution.  (Contributed by NM, 6-Oct-2004.)  (Revised by
       Mario Carneiro, 14-Oct-2016.) $)

${
	$v ph ps x y z  $.
	$d v w x y  $.
	$d v w y z  $.
	$d v w ph  $.
	$d v w ps  $.
	f0_cbvopab1 $f wff ph $.
	f1_cbvopab1 $f wff ps $.
	f2_cbvopab1 $f set x $.
	f3_cbvopab1 $f set y $.
	f4_cbvopab1 $f set z $.
	i0_cbvopab1 $f set w $.
	i1_cbvopab1 $f set v $.
	e0_cbvopab1 $e |- F/ z ph $.
	e1_cbvopab1 $e |- F/ x ps $.
	e2_cbvopab1 $e |- ( x = z -> ( ph <-> ps ) ) $.
	p_cbvopab1 $p |- { <. x , y >. | ph } = { <. z , y >. | ps } $= i0_cbvopab1 a_sup_set_class f2_cbvopab1 a_sup_set_class f3_cbvopab1 a_sup_set_class a_cop a_wceq f0_cbvopab1 a_wa f3_cbvopab1 a_wex i1_cbvopab1 p_nfv i0_cbvopab1 a_sup_set_class i1_cbvopab1 a_sup_set_class f3_cbvopab1 a_sup_set_class a_cop a_wceq f2_cbvopab1 p_nfv f0_cbvopab1 f2_cbvopab1 i1_cbvopab1 p_nfs1v i0_cbvopab1 a_sup_set_class i1_cbvopab1 a_sup_set_class f3_cbvopab1 a_sup_set_class a_cop a_wceq f0_cbvopab1 f2_cbvopab1 i1_cbvopab1 a_wsb f2_cbvopab1 p_nfan i0_cbvopab1 a_sup_set_class i1_cbvopab1 a_sup_set_class f3_cbvopab1 a_sup_set_class a_cop a_wceq f0_cbvopab1 f2_cbvopab1 i1_cbvopab1 a_wsb a_wa f2_cbvopab1 f3_cbvopab1 p_nfex f2_cbvopab1 a_sup_set_class i1_cbvopab1 a_sup_set_class f3_cbvopab1 a_sup_set_class p_opeq1 f2_cbvopab1 a_sup_set_class i1_cbvopab1 a_sup_set_class a_wceq f2_cbvopab1 a_sup_set_class f3_cbvopab1 a_sup_set_class a_cop i1_cbvopab1 a_sup_set_class f3_cbvopab1 a_sup_set_class a_cop i0_cbvopab1 a_sup_set_class p_eqeq2d f0_cbvopab1 f2_cbvopab1 i1_cbvopab1 p_sbequ12 f2_cbvopab1 a_sup_set_class i1_cbvopab1 a_sup_set_class a_wceq i0_cbvopab1 a_sup_set_class f2_cbvopab1 a_sup_set_class f3_cbvopab1 a_sup_set_class a_cop a_wceq i0_cbvopab1 a_sup_set_class i1_cbvopab1 a_sup_set_class f3_cbvopab1 a_sup_set_class a_cop a_wceq f0_cbvopab1 f0_cbvopab1 f2_cbvopab1 i1_cbvopab1 a_wsb p_anbi12d f2_cbvopab1 a_sup_set_class i1_cbvopab1 a_sup_set_class a_wceq i0_cbvopab1 a_sup_set_class f2_cbvopab1 a_sup_set_class f3_cbvopab1 a_sup_set_class a_cop a_wceq f0_cbvopab1 a_wa i0_cbvopab1 a_sup_set_class i1_cbvopab1 a_sup_set_class f3_cbvopab1 a_sup_set_class a_cop a_wceq f0_cbvopab1 f2_cbvopab1 i1_cbvopab1 a_wsb a_wa f3_cbvopab1 p_exbidv i0_cbvopab1 a_sup_set_class f2_cbvopab1 a_sup_set_class f3_cbvopab1 a_sup_set_class a_cop a_wceq f0_cbvopab1 a_wa f3_cbvopab1 a_wex i0_cbvopab1 a_sup_set_class i1_cbvopab1 a_sup_set_class f3_cbvopab1 a_sup_set_class a_cop a_wceq f0_cbvopab1 f2_cbvopab1 i1_cbvopab1 a_wsb a_wa f3_cbvopab1 a_wex f2_cbvopab1 i1_cbvopab1 p_cbvex i0_cbvopab1 a_sup_set_class i1_cbvopab1 a_sup_set_class f3_cbvopab1 a_sup_set_class a_cop a_wceq f4_cbvopab1 p_nfv e0_cbvopab1 f0_cbvopab1 f2_cbvopab1 i1_cbvopab1 f4_cbvopab1 p_nfsb i0_cbvopab1 a_sup_set_class i1_cbvopab1 a_sup_set_class f3_cbvopab1 a_sup_set_class a_cop a_wceq f0_cbvopab1 f2_cbvopab1 i1_cbvopab1 a_wsb f4_cbvopab1 p_nfan i0_cbvopab1 a_sup_set_class i1_cbvopab1 a_sup_set_class f3_cbvopab1 a_sup_set_class a_cop a_wceq f0_cbvopab1 f2_cbvopab1 i1_cbvopab1 a_wsb a_wa f4_cbvopab1 f3_cbvopab1 p_nfex i0_cbvopab1 a_sup_set_class f4_cbvopab1 a_sup_set_class f3_cbvopab1 a_sup_set_class a_cop a_wceq f1_cbvopab1 a_wa f3_cbvopab1 a_wex i1_cbvopab1 p_nfv i1_cbvopab1 a_sup_set_class f4_cbvopab1 a_sup_set_class f3_cbvopab1 a_sup_set_class p_opeq1 i1_cbvopab1 a_sup_set_class f4_cbvopab1 a_sup_set_class a_wceq i1_cbvopab1 a_sup_set_class f3_cbvopab1 a_sup_set_class a_cop f4_cbvopab1 a_sup_set_class f3_cbvopab1 a_sup_set_class a_cop i0_cbvopab1 a_sup_set_class p_eqeq2d f0_cbvopab1 i1_cbvopab1 f4_cbvopab1 f2_cbvopab1 p_sbequ e1_cbvopab1 e2_cbvopab1 f0_cbvopab1 f1_cbvopab1 f2_cbvopab1 f4_cbvopab1 p_sbie i1_cbvopab1 a_sup_set_class f4_cbvopab1 a_sup_set_class a_wceq f0_cbvopab1 f2_cbvopab1 i1_cbvopab1 a_wsb f0_cbvopab1 f2_cbvopab1 f4_cbvopab1 a_wsb f1_cbvopab1 p_syl6bb i1_cbvopab1 a_sup_set_class f4_cbvopab1 a_sup_set_class a_wceq i0_cbvopab1 a_sup_set_class i1_cbvopab1 a_sup_set_class f3_cbvopab1 a_sup_set_class a_cop a_wceq i0_cbvopab1 a_sup_set_class f4_cbvopab1 a_sup_set_class f3_cbvopab1 a_sup_set_class a_cop a_wceq f0_cbvopab1 f2_cbvopab1 i1_cbvopab1 a_wsb f1_cbvopab1 p_anbi12d i1_cbvopab1 a_sup_set_class f4_cbvopab1 a_sup_set_class a_wceq i0_cbvopab1 a_sup_set_class i1_cbvopab1 a_sup_set_class f3_cbvopab1 a_sup_set_class a_cop a_wceq f0_cbvopab1 f2_cbvopab1 i1_cbvopab1 a_wsb a_wa i0_cbvopab1 a_sup_set_class f4_cbvopab1 a_sup_set_class f3_cbvopab1 a_sup_set_class a_cop a_wceq f1_cbvopab1 a_wa f3_cbvopab1 p_exbidv i0_cbvopab1 a_sup_set_class i1_cbvopab1 a_sup_set_class f3_cbvopab1 a_sup_set_class a_cop a_wceq f0_cbvopab1 f2_cbvopab1 i1_cbvopab1 a_wsb a_wa f3_cbvopab1 a_wex i0_cbvopab1 a_sup_set_class f4_cbvopab1 a_sup_set_class f3_cbvopab1 a_sup_set_class a_cop a_wceq f1_cbvopab1 a_wa f3_cbvopab1 a_wex i1_cbvopab1 f4_cbvopab1 p_cbvex i0_cbvopab1 a_sup_set_class f2_cbvopab1 a_sup_set_class f3_cbvopab1 a_sup_set_class a_cop a_wceq f0_cbvopab1 a_wa f3_cbvopab1 a_wex f2_cbvopab1 a_wex i0_cbvopab1 a_sup_set_class i1_cbvopab1 a_sup_set_class f3_cbvopab1 a_sup_set_class a_cop a_wceq f0_cbvopab1 f2_cbvopab1 i1_cbvopab1 a_wsb a_wa f3_cbvopab1 a_wex i1_cbvopab1 a_wex i0_cbvopab1 a_sup_set_class f4_cbvopab1 a_sup_set_class f3_cbvopab1 a_sup_set_class a_cop a_wceq f1_cbvopab1 a_wa f3_cbvopab1 a_wex f4_cbvopab1 a_wex p_bitri i0_cbvopab1 a_sup_set_class f2_cbvopab1 a_sup_set_class f3_cbvopab1 a_sup_set_class a_cop a_wceq f0_cbvopab1 a_wa f3_cbvopab1 a_wex f2_cbvopab1 a_wex i0_cbvopab1 a_sup_set_class f4_cbvopab1 a_sup_set_class f3_cbvopab1 a_sup_set_class a_cop a_wceq f1_cbvopab1 a_wa f3_cbvopab1 a_wex f4_cbvopab1 a_wex i0_cbvopab1 p_abbii f0_cbvopab1 f2_cbvopab1 f3_cbvopab1 i0_cbvopab1 a_df-opab f1_cbvopab1 f4_cbvopab1 f3_cbvopab1 i0_cbvopab1 a_df-opab i0_cbvopab1 a_sup_set_class f2_cbvopab1 a_sup_set_class f3_cbvopab1 a_sup_set_class a_cop a_wceq f0_cbvopab1 a_wa f3_cbvopab1 a_wex f2_cbvopab1 a_wex i0_cbvopab1 a_cab i0_cbvopab1 a_sup_set_class f4_cbvopab1 a_sup_set_class f3_cbvopab1 a_sup_set_class a_cop a_wceq f1_cbvopab1 a_wa f3_cbvopab1 a_wex f4_cbvopab1 a_wex i0_cbvopab1 a_cab f0_cbvopab1 f2_cbvopab1 f3_cbvopab1 a_copab f1_cbvopab1 f4_cbvopab1 f3_cbvopab1 a_copab p_3eqtr4i $.
$}

$(Change second bound variable in an ordered-pair class abstraction, using
       explicit substitution.  (Contributed by NM, 22-Aug-2013.) $)

${
	$v ph ps x y z  $.
	$d w x y z  $.
	$d w ph  $.
	$d w ps  $.
	f0_cbvopab2 $f wff ph $.
	f1_cbvopab2 $f wff ps $.
	f2_cbvopab2 $f set x $.
	f3_cbvopab2 $f set y $.
	f4_cbvopab2 $f set z $.
	i0_cbvopab2 $f set w $.
	e0_cbvopab2 $e |- F/ z ph $.
	e1_cbvopab2 $e |- F/ y ps $.
	e2_cbvopab2 $e |- ( y = z -> ( ph <-> ps ) ) $.
	p_cbvopab2 $p |- { <. x , y >. | ph } = { <. x , z >. | ps } $= i0_cbvopab2 a_sup_set_class f2_cbvopab2 a_sup_set_class f3_cbvopab2 a_sup_set_class a_cop a_wceq f4_cbvopab2 p_nfv e0_cbvopab2 i0_cbvopab2 a_sup_set_class f2_cbvopab2 a_sup_set_class f3_cbvopab2 a_sup_set_class a_cop a_wceq f0_cbvopab2 f4_cbvopab2 p_nfan i0_cbvopab2 a_sup_set_class f2_cbvopab2 a_sup_set_class f4_cbvopab2 a_sup_set_class a_cop a_wceq f3_cbvopab2 p_nfv e1_cbvopab2 i0_cbvopab2 a_sup_set_class f2_cbvopab2 a_sup_set_class f4_cbvopab2 a_sup_set_class a_cop a_wceq f1_cbvopab2 f3_cbvopab2 p_nfan f3_cbvopab2 a_sup_set_class f4_cbvopab2 a_sup_set_class f2_cbvopab2 a_sup_set_class p_opeq2 f3_cbvopab2 a_sup_set_class f4_cbvopab2 a_sup_set_class a_wceq f2_cbvopab2 a_sup_set_class f3_cbvopab2 a_sup_set_class a_cop f2_cbvopab2 a_sup_set_class f4_cbvopab2 a_sup_set_class a_cop i0_cbvopab2 a_sup_set_class p_eqeq2d e2_cbvopab2 f3_cbvopab2 a_sup_set_class f4_cbvopab2 a_sup_set_class a_wceq i0_cbvopab2 a_sup_set_class f2_cbvopab2 a_sup_set_class f3_cbvopab2 a_sup_set_class a_cop a_wceq i0_cbvopab2 a_sup_set_class f2_cbvopab2 a_sup_set_class f4_cbvopab2 a_sup_set_class a_cop a_wceq f0_cbvopab2 f1_cbvopab2 p_anbi12d i0_cbvopab2 a_sup_set_class f2_cbvopab2 a_sup_set_class f3_cbvopab2 a_sup_set_class a_cop a_wceq f0_cbvopab2 a_wa i0_cbvopab2 a_sup_set_class f2_cbvopab2 a_sup_set_class f4_cbvopab2 a_sup_set_class a_cop a_wceq f1_cbvopab2 a_wa f3_cbvopab2 f4_cbvopab2 p_cbvex i0_cbvopab2 a_sup_set_class f2_cbvopab2 a_sup_set_class f3_cbvopab2 a_sup_set_class a_cop a_wceq f0_cbvopab2 a_wa f3_cbvopab2 a_wex i0_cbvopab2 a_sup_set_class f2_cbvopab2 a_sup_set_class f4_cbvopab2 a_sup_set_class a_cop a_wceq f1_cbvopab2 a_wa f4_cbvopab2 a_wex f2_cbvopab2 p_exbii i0_cbvopab2 a_sup_set_class f2_cbvopab2 a_sup_set_class f3_cbvopab2 a_sup_set_class a_cop a_wceq f0_cbvopab2 a_wa f3_cbvopab2 a_wex f2_cbvopab2 a_wex i0_cbvopab2 a_sup_set_class f2_cbvopab2 a_sup_set_class f4_cbvopab2 a_sup_set_class a_cop a_wceq f1_cbvopab2 a_wa f4_cbvopab2 a_wex f2_cbvopab2 a_wex i0_cbvopab2 p_abbii f0_cbvopab2 f2_cbvopab2 f3_cbvopab2 i0_cbvopab2 a_df-opab f1_cbvopab2 f2_cbvopab2 f4_cbvopab2 i0_cbvopab2 a_df-opab i0_cbvopab2 a_sup_set_class f2_cbvopab2 a_sup_set_class f3_cbvopab2 a_sup_set_class a_cop a_wceq f0_cbvopab2 a_wa f3_cbvopab2 a_wex f2_cbvopab2 a_wex i0_cbvopab2 a_cab i0_cbvopab2 a_sup_set_class f2_cbvopab2 a_sup_set_class f4_cbvopab2 a_sup_set_class a_cop a_wceq f1_cbvopab2 a_wa f4_cbvopab2 a_wex f2_cbvopab2 a_wex i0_cbvopab2 a_cab f0_cbvopab2 f2_cbvopab2 f3_cbvopab2 a_copab f1_cbvopab2 f2_cbvopab2 f4_cbvopab2 a_copab p_3eqtr4i $.
$}

$(Change first bound variable in an ordered-pair class abstraction, using
       explicit substitution.  (Contributed by NM, 31-Jul-2003.) $)

${
	$v ph x y z  $.
	$d x y z w  $.
	$d z w ph  $.
	f0_cbvopab1s $f wff ph $.
	f1_cbvopab1s $f set x $.
	f2_cbvopab1s $f set y $.
	f3_cbvopab1s $f set z $.
	i0_cbvopab1s $f set w $.
	p_cbvopab1s $p |- { <. x , y >. | ph } = { <. z , y >. | [ z / x ] ph } $= i0_cbvopab1s a_sup_set_class f1_cbvopab1s a_sup_set_class f2_cbvopab1s a_sup_set_class a_cop a_wceq f0_cbvopab1s a_wa f2_cbvopab1s a_wex f3_cbvopab1s p_nfv i0_cbvopab1s a_sup_set_class f3_cbvopab1s a_sup_set_class f2_cbvopab1s a_sup_set_class a_cop a_wceq f1_cbvopab1s p_nfv f0_cbvopab1s f1_cbvopab1s f3_cbvopab1s p_nfs1v i0_cbvopab1s a_sup_set_class f3_cbvopab1s a_sup_set_class f2_cbvopab1s a_sup_set_class a_cop a_wceq f0_cbvopab1s f1_cbvopab1s f3_cbvopab1s a_wsb f1_cbvopab1s p_nfan i0_cbvopab1s a_sup_set_class f3_cbvopab1s a_sup_set_class f2_cbvopab1s a_sup_set_class a_cop a_wceq f0_cbvopab1s f1_cbvopab1s f3_cbvopab1s a_wsb a_wa f1_cbvopab1s f2_cbvopab1s p_nfex f1_cbvopab1s a_sup_set_class f3_cbvopab1s a_sup_set_class f2_cbvopab1s a_sup_set_class p_opeq1 f1_cbvopab1s a_sup_set_class f3_cbvopab1s a_sup_set_class a_wceq f1_cbvopab1s a_sup_set_class f2_cbvopab1s a_sup_set_class a_cop f3_cbvopab1s a_sup_set_class f2_cbvopab1s a_sup_set_class a_cop i0_cbvopab1s a_sup_set_class p_eqeq2d f0_cbvopab1s f1_cbvopab1s f3_cbvopab1s p_sbequ12 f1_cbvopab1s a_sup_set_class f3_cbvopab1s a_sup_set_class a_wceq i0_cbvopab1s a_sup_set_class f1_cbvopab1s a_sup_set_class f2_cbvopab1s a_sup_set_class a_cop a_wceq i0_cbvopab1s a_sup_set_class f3_cbvopab1s a_sup_set_class f2_cbvopab1s a_sup_set_class a_cop a_wceq f0_cbvopab1s f0_cbvopab1s f1_cbvopab1s f3_cbvopab1s a_wsb p_anbi12d f1_cbvopab1s a_sup_set_class f3_cbvopab1s a_sup_set_class a_wceq i0_cbvopab1s a_sup_set_class f1_cbvopab1s a_sup_set_class f2_cbvopab1s a_sup_set_class a_cop a_wceq f0_cbvopab1s a_wa i0_cbvopab1s a_sup_set_class f3_cbvopab1s a_sup_set_class f2_cbvopab1s a_sup_set_class a_cop a_wceq f0_cbvopab1s f1_cbvopab1s f3_cbvopab1s a_wsb a_wa f2_cbvopab1s p_exbidv i0_cbvopab1s a_sup_set_class f1_cbvopab1s a_sup_set_class f2_cbvopab1s a_sup_set_class a_cop a_wceq f0_cbvopab1s a_wa f2_cbvopab1s a_wex i0_cbvopab1s a_sup_set_class f3_cbvopab1s a_sup_set_class f2_cbvopab1s a_sup_set_class a_cop a_wceq f0_cbvopab1s f1_cbvopab1s f3_cbvopab1s a_wsb a_wa f2_cbvopab1s a_wex f1_cbvopab1s f3_cbvopab1s p_cbvex i0_cbvopab1s a_sup_set_class f1_cbvopab1s a_sup_set_class f2_cbvopab1s a_sup_set_class a_cop a_wceq f0_cbvopab1s a_wa f2_cbvopab1s a_wex f1_cbvopab1s a_wex i0_cbvopab1s a_sup_set_class f3_cbvopab1s a_sup_set_class f2_cbvopab1s a_sup_set_class a_cop a_wceq f0_cbvopab1s f1_cbvopab1s f3_cbvopab1s a_wsb a_wa f2_cbvopab1s a_wex f3_cbvopab1s a_wex i0_cbvopab1s p_abbii f0_cbvopab1s f1_cbvopab1s f2_cbvopab1s i0_cbvopab1s a_df-opab f0_cbvopab1s f1_cbvopab1s f3_cbvopab1s a_wsb f3_cbvopab1s f2_cbvopab1s i0_cbvopab1s a_df-opab i0_cbvopab1s a_sup_set_class f1_cbvopab1s a_sup_set_class f2_cbvopab1s a_sup_set_class a_cop a_wceq f0_cbvopab1s a_wa f2_cbvopab1s a_wex f1_cbvopab1s a_wex i0_cbvopab1s a_cab i0_cbvopab1s a_sup_set_class f3_cbvopab1s a_sup_set_class f2_cbvopab1s a_sup_set_class a_cop a_wceq f0_cbvopab1s f1_cbvopab1s f3_cbvopab1s a_wsb a_wa f2_cbvopab1s a_wex f3_cbvopab1s a_wex i0_cbvopab1s a_cab f0_cbvopab1s f1_cbvopab1s f2_cbvopab1s a_copab f0_cbvopab1s f1_cbvopab1s f3_cbvopab1s a_wsb f3_cbvopab1s f2_cbvopab1s a_copab p_3eqtr4i $.
$}

$(Rule used to change the first bound variable in an ordered pair
       abstraction, using implicit substitution.  (Contributed by NM,
       31-Jul-2003.)  (Proof shortened by Eric Schmidt, 4-Apr-2007.) $)

${
	$v ph ps x y z  $.
	$d x y  $.
	$d y z  $.
	$d z ph  $.
	$d x ps  $.
	f0_cbvopab1v $f wff ph $.
	f1_cbvopab1v $f wff ps $.
	f2_cbvopab1v $f set x $.
	f3_cbvopab1v $f set y $.
	f4_cbvopab1v $f set z $.
	e0_cbvopab1v $e |- ( x = z -> ( ph <-> ps ) ) $.
	p_cbvopab1v $p |- { <. x , y >. | ph } = { <. z , y >. | ps } $= f0_cbvopab1v f4_cbvopab1v p_nfv f1_cbvopab1v f2_cbvopab1v p_nfv e0_cbvopab1v f0_cbvopab1v f1_cbvopab1v f2_cbvopab1v f3_cbvopab1v f4_cbvopab1v p_cbvopab1 $.
$}

$(Rule used to change the second bound variable in an ordered pair
       abstraction, using implicit substitution.  (Contributed by NM,
       2-Sep-1999.) $)

${
	$v ph ps x y z  $.
	$d x y z w  $.
	$d z w ph  $.
	$d y w ps  $.
	f0_cbvopab2v $f wff ph $.
	f1_cbvopab2v $f wff ps $.
	f2_cbvopab2v $f set x $.
	f3_cbvopab2v $f set y $.
	f4_cbvopab2v $f set z $.
	i0_cbvopab2v $f set w $.
	e0_cbvopab2v $e |- ( y = z -> ( ph <-> ps ) ) $.
	p_cbvopab2v $p |- { <. x , y >. | ph } = { <. x , z >. | ps } $= f3_cbvopab2v a_sup_set_class f4_cbvopab2v a_sup_set_class f2_cbvopab2v a_sup_set_class p_opeq2 f3_cbvopab2v a_sup_set_class f4_cbvopab2v a_sup_set_class a_wceq f2_cbvopab2v a_sup_set_class f3_cbvopab2v a_sup_set_class a_cop f2_cbvopab2v a_sup_set_class f4_cbvopab2v a_sup_set_class a_cop i0_cbvopab2v a_sup_set_class p_eqeq2d e0_cbvopab2v f3_cbvopab2v a_sup_set_class f4_cbvopab2v a_sup_set_class a_wceq i0_cbvopab2v a_sup_set_class f2_cbvopab2v a_sup_set_class f3_cbvopab2v a_sup_set_class a_cop a_wceq i0_cbvopab2v a_sup_set_class f2_cbvopab2v a_sup_set_class f4_cbvopab2v a_sup_set_class a_cop a_wceq f0_cbvopab2v f1_cbvopab2v p_anbi12d i0_cbvopab2v a_sup_set_class f2_cbvopab2v a_sup_set_class f3_cbvopab2v a_sup_set_class a_cop a_wceq f0_cbvopab2v a_wa i0_cbvopab2v a_sup_set_class f2_cbvopab2v a_sup_set_class f4_cbvopab2v a_sup_set_class a_cop a_wceq f1_cbvopab2v a_wa f3_cbvopab2v f4_cbvopab2v p_cbvexv i0_cbvopab2v a_sup_set_class f2_cbvopab2v a_sup_set_class f3_cbvopab2v a_sup_set_class a_cop a_wceq f0_cbvopab2v a_wa f3_cbvopab2v a_wex i0_cbvopab2v a_sup_set_class f2_cbvopab2v a_sup_set_class f4_cbvopab2v a_sup_set_class a_cop a_wceq f1_cbvopab2v a_wa f4_cbvopab2v a_wex f2_cbvopab2v p_exbii i0_cbvopab2v a_sup_set_class f2_cbvopab2v a_sup_set_class f3_cbvopab2v a_sup_set_class a_cop a_wceq f0_cbvopab2v a_wa f3_cbvopab2v a_wex f2_cbvopab2v a_wex i0_cbvopab2v a_sup_set_class f2_cbvopab2v a_sup_set_class f4_cbvopab2v a_sup_set_class a_cop a_wceq f1_cbvopab2v a_wa f4_cbvopab2v a_wex f2_cbvopab2v a_wex i0_cbvopab2v p_abbii f0_cbvopab2v f2_cbvopab2v f3_cbvopab2v i0_cbvopab2v a_df-opab f1_cbvopab2v f2_cbvopab2v f4_cbvopab2v i0_cbvopab2v a_df-opab i0_cbvopab2v a_sup_set_class f2_cbvopab2v a_sup_set_class f3_cbvopab2v a_sup_set_class a_cop a_wceq f0_cbvopab2v a_wa f3_cbvopab2v a_wex f2_cbvopab2v a_wex i0_cbvopab2v a_cab i0_cbvopab2v a_sup_set_class f2_cbvopab2v a_sup_set_class f4_cbvopab2v a_sup_set_class a_cop a_wceq f1_cbvopab2v a_wa f4_cbvopab2v a_wex f2_cbvopab2v a_wex i0_cbvopab2v a_cab f0_cbvopab2v f2_cbvopab2v f3_cbvopab2v a_copab f1_cbvopab2v f2_cbvopab2v f4_cbvopab2v a_copab p_3eqtr4i $.
$}

$(Move substitution into a class abstraction.  (Contributed by NM,
       6-Aug-2007.)  (Proof shortened by Mario Carneiro, 17-Nov-2016.) $)

${
	$v ph x y z A V  $.
	$d w y z A  $.
	$d w ph  $.
	$d w x y z  $.
	f0_csbopabg $f wff ph $.
	f1_csbopabg $f set x $.
	f2_csbopabg $f set y $.
	f3_csbopabg $f set z $.
	f4_csbopabg $f class A $.
	f5_csbopabg $f class V $.
	i0_csbopabg $f set w $.
	p_csbopabg $p |- ( A e. V -> [_ A / x ]_ { <. y , z >. | ph } = { <. y , z >. | [. A / x ]. ph } ) $= f1_csbopabg i0_csbopabg a_sup_set_class f4_csbopabg f0_csbopabg f2_csbopabg f3_csbopabg a_copab p_csbeq1 f0_csbopabg f1_csbopabg i0_csbopabg f4_csbopabg p_dfsbcq2 i0_csbopabg a_sup_set_class f4_csbopabg a_wceq f0_csbopabg f1_csbopabg i0_csbopabg a_wsb f0_csbopabg f1_csbopabg f4_csbopabg a_wsbc f2_csbopabg f3_csbopabg p_opabbidv i0_csbopabg a_sup_set_class f4_csbopabg a_wceq f1_csbopabg i0_csbopabg a_sup_set_class f0_csbopabg f2_csbopabg f3_csbopabg a_copab a_csb f1_csbopabg f4_csbopabg f0_csbopabg f2_csbopabg f3_csbopabg a_copab a_csb f0_csbopabg f1_csbopabg i0_csbopabg a_wsb f2_csbopabg f3_csbopabg a_copab f0_csbopabg f1_csbopabg f4_csbopabg a_wsbc f2_csbopabg f3_csbopabg a_copab p_eqeq12d i0_csbopabg p_vex f0_csbopabg f1_csbopabg i0_csbopabg p_nfs1v f0_csbopabg f1_csbopabg i0_csbopabg a_wsb f2_csbopabg f3_csbopabg f1_csbopabg p_nfopab f0_csbopabg f1_csbopabg i0_csbopabg p_sbequ12 f1_csbopabg a_sup_set_class i0_csbopabg a_sup_set_class a_wceq f0_csbopabg f0_csbopabg f1_csbopabg i0_csbopabg a_wsb f2_csbopabg f3_csbopabg p_opabbidv f1_csbopabg i0_csbopabg a_sup_set_class f0_csbopabg f2_csbopabg f3_csbopabg a_copab f0_csbopabg f1_csbopabg i0_csbopabg a_wsb f2_csbopabg f3_csbopabg a_copab p_csbief f1_csbopabg i0_csbopabg a_sup_set_class f0_csbopabg f2_csbopabg f3_csbopabg a_copab a_csb f0_csbopabg f1_csbopabg i0_csbopabg a_wsb f2_csbopabg f3_csbopabg a_copab a_wceq f1_csbopabg f4_csbopabg f0_csbopabg f2_csbopabg f3_csbopabg a_copab a_csb f0_csbopabg f1_csbopabg f4_csbopabg a_wsbc f2_csbopabg f3_csbopabg a_copab a_wceq i0_csbopabg f4_csbopabg f5_csbopabg p_vtoclg $.
$}

$(Union of two ordered pair class abstractions.  (Contributed by NM,
       30-Sep-2002.) $)

${
	$v ph ps x y  $.
	$d x z  $.
	$d y z  $.
	$d ph z  $.
	$d ps z  $.
	f0_unopab $f wff ph $.
	f1_unopab $f wff ps $.
	f2_unopab $f set x $.
	f3_unopab $f set y $.
	i0_unopab $f set z $.
	p_unopab $p |- ( { <. x , y >. | ph } u. { <. x , y >. | ps } ) = { <. x , y >. | ( ph \/ ps ) } $= i0_unopab a_sup_set_class f2_unopab a_sup_set_class f3_unopab a_sup_set_class a_cop a_wceq f0_unopab a_wa f3_unopab a_wex f2_unopab a_wex i0_unopab a_sup_set_class f2_unopab a_sup_set_class f3_unopab a_sup_set_class a_cop a_wceq f1_unopab a_wa f3_unopab a_wex f2_unopab a_wex i0_unopab p_unab i0_unopab a_sup_set_class f2_unopab a_sup_set_class f3_unopab a_sup_set_class a_cop a_wceq f0_unopab a_wa f3_unopab a_wex i0_unopab a_sup_set_class f2_unopab a_sup_set_class f3_unopab a_sup_set_class a_cop a_wceq f1_unopab a_wa f3_unopab a_wex f2_unopab p_19.43 i0_unopab a_sup_set_class f2_unopab a_sup_set_class f3_unopab a_sup_set_class a_cop a_wceq f0_unopab f1_unopab p_andi i0_unopab a_sup_set_class f2_unopab a_sup_set_class f3_unopab a_sup_set_class a_cop a_wceq f0_unopab f1_unopab a_wo a_wa i0_unopab a_sup_set_class f2_unopab a_sup_set_class f3_unopab a_sup_set_class a_cop a_wceq f0_unopab a_wa i0_unopab a_sup_set_class f2_unopab a_sup_set_class f3_unopab a_sup_set_class a_cop a_wceq f1_unopab a_wa a_wo f3_unopab p_exbii i0_unopab a_sup_set_class f2_unopab a_sup_set_class f3_unopab a_sup_set_class a_cop a_wceq f0_unopab a_wa i0_unopab a_sup_set_class f2_unopab a_sup_set_class f3_unopab a_sup_set_class a_cop a_wceq f1_unopab a_wa f3_unopab p_19.43 i0_unopab a_sup_set_class f2_unopab a_sup_set_class f3_unopab a_sup_set_class a_cop a_wceq f0_unopab f1_unopab a_wo a_wa f3_unopab a_wex i0_unopab a_sup_set_class f2_unopab a_sup_set_class f3_unopab a_sup_set_class a_cop a_wceq f0_unopab a_wa i0_unopab a_sup_set_class f2_unopab a_sup_set_class f3_unopab a_sup_set_class a_cop a_wceq f1_unopab a_wa a_wo f3_unopab a_wex i0_unopab a_sup_set_class f2_unopab a_sup_set_class f3_unopab a_sup_set_class a_cop a_wceq f0_unopab a_wa f3_unopab a_wex i0_unopab a_sup_set_class f2_unopab a_sup_set_class f3_unopab a_sup_set_class a_cop a_wceq f1_unopab a_wa f3_unopab a_wex a_wo p_bitr2i i0_unopab a_sup_set_class f2_unopab a_sup_set_class f3_unopab a_sup_set_class a_cop a_wceq f0_unopab a_wa f3_unopab a_wex i0_unopab a_sup_set_class f2_unopab a_sup_set_class f3_unopab a_sup_set_class a_cop a_wceq f1_unopab a_wa f3_unopab a_wex a_wo i0_unopab a_sup_set_class f2_unopab a_sup_set_class f3_unopab a_sup_set_class a_cop a_wceq f0_unopab f1_unopab a_wo a_wa f3_unopab a_wex f2_unopab p_exbii i0_unopab a_sup_set_class f2_unopab a_sup_set_class f3_unopab a_sup_set_class a_cop a_wceq f0_unopab a_wa f3_unopab a_wex f2_unopab a_wex i0_unopab a_sup_set_class f2_unopab a_sup_set_class f3_unopab a_sup_set_class a_cop a_wceq f1_unopab a_wa f3_unopab a_wex f2_unopab a_wex a_wo i0_unopab a_sup_set_class f2_unopab a_sup_set_class f3_unopab a_sup_set_class a_cop a_wceq f0_unopab a_wa f3_unopab a_wex i0_unopab a_sup_set_class f2_unopab a_sup_set_class f3_unopab a_sup_set_class a_cop a_wceq f1_unopab a_wa f3_unopab a_wex a_wo f2_unopab a_wex i0_unopab a_sup_set_class f2_unopab a_sup_set_class f3_unopab a_sup_set_class a_cop a_wceq f0_unopab f1_unopab a_wo a_wa f3_unopab a_wex f2_unopab a_wex p_bitr3i i0_unopab a_sup_set_class f2_unopab a_sup_set_class f3_unopab a_sup_set_class a_cop a_wceq f0_unopab a_wa f3_unopab a_wex f2_unopab a_wex i0_unopab a_sup_set_class f2_unopab a_sup_set_class f3_unopab a_sup_set_class a_cop a_wceq f1_unopab a_wa f3_unopab a_wex f2_unopab a_wex a_wo i0_unopab a_sup_set_class f2_unopab a_sup_set_class f3_unopab a_sup_set_class a_cop a_wceq f0_unopab f1_unopab a_wo a_wa f3_unopab a_wex f2_unopab a_wex i0_unopab p_abbii i0_unopab a_sup_set_class f2_unopab a_sup_set_class f3_unopab a_sup_set_class a_cop a_wceq f0_unopab a_wa f3_unopab a_wex f2_unopab a_wex i0_unopab a_cab i0_unopab a_sup_set_class f2_unopab a_sup_set_class f3_unopab a_sup_set_class a_cop a_wceq f1_unopab a_wa f3_unopab a_wex f2_unopab a_wex i0_unopab a_cab a_cun i0_unopab a_sup_set_class f2_unopab a_sup_set_class f3_unopab a_sup_set_class a_cop a_wceq f0_unopab a_wa f3_unopab a_wex f2_unopab a_wex i0_unopab a_sup_set_class f2_unopab a_sup_set_class f3_unopab a_sup_set_class a_cop a_wceq f1_unopab a_wa f3_unopab a_wex f2_unopab a_wex a_wo i0_unopab a_cab i0_unopab a_sup_set_class f2_unopab a_sup_set_class f3_unopab a_sup_set_class a_cop a_wceq f0_unopab f1_unopab a_wo a_wa f3_unopab a_wex f2_unopab a_wex i0_unopab a_cab p_eqtri f0_unopab f2_unopab f3_unopab i0_unopab a_df-opab f1_unopab f2_unopab f3_unopab i0_unopab a_df-opab f0_unopab f2_unopab f3_unopab a_copab i0_unopab a_sup_set_class f2_unopab a_sup_set_class f3_unopab a_sup_set_class a_cop a_wceq f0_unopab a_wa f3_unopab a_wex f2_unopab a_wex i0_unopab a_cab f1_unopab f2_unopab f3_unopab a_copab i0_unopab a_sup_set_class f2_unopab a_sup_set_class f3_unopab a_sup_set_class a_cop a_wceq f1_unopab a_wa f3_unopab a_wex f2_unopab a_wex i0_unopab a_cab p_uneq12i f0_unopab f1_unopab a_wo f2_unopab f3_unopab i0_unopab a_df-opab i0_unopab a_sup_set_class f2_unopab a_sup_set_class f3_unopab a_sup_set_class a_cop a_wceq f0_unopab a_wa f3_unopab a_wex f2_unopab a_wex i0_unopab a_cab i0_unopab a_sup_set_class f2_unopab a_sup_set_class f3_unopab a_sup_set_class a_cop a_wceq f1_unopab a_wa f3_unopab a_wex f2_unopab a_wex i0_unopab a_cab a_cun i0_unopab a_sup_set_class f2_unopab a_sup_set_class f3_unopab a_sup_set_class a_cop a_wceq f0_unopab f1_unopab a_wo a_wa f3_unopab a_wex f2_unopab a_wex i0_unopab a_cab f0_unopab f2_unopab f3_unopab a_copab f1_unopab f2_unopab f3_unopab a_copab a_cun f0_unopab f1_unopab a_wo f2_unopab f3_unopab a_copab p_3eqtr4i $.
$}

$(An equality theorem for the maps to notation.  (Contributed by Mario
       Carneiro, 16-Dec-2013.) $)

${
	$v x A B C D  $.
	$d x y  $.
	$d y A  $.
	$d y B  $.
	$d y C  $.
	$d y D  $.
	f0_mpteq12f $f set x $.
	f1_mpteq12f $f class A $.
	f2_mpteq12f $f class B $.
	f3_mpteq12f $f class C $.
	f4_mpteq12f $f class D $.
	i0_mpteq12f $f set y $.
	p_mpteq12f $p |- ( ( A. x A = C /\ A. x e. A B = D ) -> ( x e. A |-> B ) = ( x e. C |-> D ) ) $= f1_mpteq12f f3_mpteq12f a_wceq f0_mpteq12f p_nfa1 f2_mpteq12f f4_mpteq12f a_wceq f0_mpteq12f f1_mpteq12f p_nfra1 f1_mpteq12f f3_mpteq12f a_wceq f0_mpteq12f a_wal f2_mpteq12f f4_mpteq12f a_wceq f0_mpteq12f f1_mpteq12f a_wral f0_mpteq12f p_nfan f1_mpteq12f f3_mpteq12f a_wceq f0_mpteq12f a_wal f2_mpteq12f f4_mpteq12f a_wceq f0_mpteq12f f1_mpteq12f a_wral a_wa i0_mpteq12f p_nfv f2_mpteq12f f4_mpteq12f a_wceq f0_mpteq12f f1_mpteq12f p_rsp f2_mpteq12f f4_mpteq12f a_wceq f0_mpteq12f f1_mpteq12f a_wral f0_mpteq12f a_sup_set_class f1_mpteq12f a_wcel f2_mpteq12f f4_mpteq12f a_wceq p_imp f2_mpteq12f f4_mpteq12f a_wceq f0_mpteq12f f1_mpteq12f a_wral f0_mpteq12f a_sup_set_class f1_mpteq12f a_wcel a_wa f2_mpteq12f f4_mpteq12f i0_mpteq12f a_sup_set_class p_eqeq2d f2_mpteq12f f4_mpteq12f a_wceq f0_mpteq12f f1_mpteq12f a_wral f0_mpteq12f a_sup_set_class f1_mpteq12f a_wcel i0_mpteq12f a_sup_set_class f2_mpteq12f a_wceq i0_mpteq12f a_sup_set_class f4_mpteq12f a_wceq p_pm5.32da f1_mpteq12f f3_mpteq12f a_wceq f0_mpteq12f p_sp f1_mpteq12f f3_mpteq12f a_wceq f0_mpteq12f a_wal f1_mpteq12f f3_mpteq12f f0_mpteq12f a_sup_set_class p_eleq2d f1_mpteq12f f3_mpteq12f a_wceq f0_mpteq12f a_wal f0_mpteq12f a_sup_set_class f1_mpteq12f a_wcel f0_mpteq12f a_sup_set_class f3_mpteq12f a_wcel i0_mpteq12f a_sup_set_class f4_mpteq12f a_wceq p_anbi1d f2_mpteq12f f4_mpteq12f a_wceq f0_mpteq12f f1_mpteq12f a_wral f0_mpteq12f a_sup_set_class f1_mpteq12f a_wcel i0_mpteq12f a_sup_set_class f2_mpteq12f a_wceq a_wa f0_mpteq12f a_sup_set_class f1_mpteq12f a_wcel i0_mpteq12f a_sup_set_class f4_mpteq12f a_wceq a_wa f1_mpteq12f f3_mpteq12f a_wceq f0_mpteq12f a_wal f0_mpteq12f a_sup_set_class f3_mpteq12f a_wcel i0_mpteq12f a_sup_set_class f4_mpteq12f a_wceq a_wa p_sylan9bbr f1_mpteq12f f3_mpteq12f a_wceq f0_mpteq12f a_wal f2_mpteq12f f4_mpteq12f a_wceq f0_mpteq12f f1_mpteq12f a_wral a_wa f0_mpteq12f a_sup_set_class f1_mpteq12f a_wcel i0_mpteq12f a_sup_set_class f2_mpteq12f a_wceq a_wa f0_mpteq12f a_sup_set_class f3_mpteq12f a_wcel i0_mpteq12f a_sup_set_class f4_mpteq12f a_wceq a_wa f0_mpteq12f i0_mpteq12f p_opabbid f0_mpteq12f i0_mpteq12f f1_mpteq12f f2_mpteq12f a_df-mpt f0_mpteq12f i0_mpteq12f f3_mpteq12f f4_mpteq12f a_df-mpt f1_mpteq12f f3_mpteq12f a_wceq f0_mpteq12f a_wal f2_mpteq12f f4_mpteq12f a_wceq f0_mpteq12f f1_mpteq12f a_wral a_wa f0_mpteq12f a_sup_set_class f1_mpteq12f a_wcel i0_mpteq12f a_sup_set_class f2_mpteq12f a_wceq a_wa f0_mpteq12f i0_mpteq12f a_copab f0_mpteq12f a_sup_set_class f3_mpteq12f a_wcel i0_mpteq12f a_sup_set_class f4_mpteq12f a_wceq a_wa f0_mpteq12f i0_mpteq12f a_copab f0_mpteq12f f1_mpteq12f f2_mpteq12f a_cmpt f0_mpteq12f f3_mpteq12f f4_mpteq12f a_cmpt p_3eqtr4g $.
$}

$(An equality inference for the maps to notation.  (Contributed by Mario
         Carneiro, 26-Jan-2017.) $)

${
	$v ph x A B C D  $.
	$d x ph  $.
	$d A  $.
	$d B  $.
	$d C  $.
	$d D  $.
	f0_mpteq12dva $f wff ph $.
	f1_mpteq12dva $f set x $.
	f2_mpteq12dva $f class A $.
	f3_mpteq12dva $f class B $.
	f4_mpteq12dva $f class C $.
	f5_mpteq12dva $f class D $.
	e0_mpteq12dva $e |- ( ph -> A = C ) $.
	e1_mpteq12dva $e |- ( ( ph /\ x e. A ) -> B = D ) $.
	p_mpteq12dva $p |- ( ph -> ( x e. A |-> B ) = ( x e. C |-> D ) ) $= e0_mpteq12dva f0_mpteq12dva f2_mpteq12dva f4_mpteq12dva a_wceq f1_mpteq12dva p_alrimiv e1_mpteq12dva f0_mpteq12dva f3_mpteq12dva f5_mpteq12dva a_wceq f1_mpteq12dva f2_mpteq12dva p_ralrimiva f1_mpteq12dva f2_mpteq12dva f3_mpteq12dva f4_mpteq12dva f5_mpteq12dva p_mpteq12f f0_mpteq12dva f2_mpteq12dva f4_mpteq12dva a_wceq f1_mpteq12dva a_wal f3_mpteq12dva f5_mpteq12dva a_wceq f1_mpteq12dva f2_mpteq12dva a_wral f1_mpteq12dva f2_mpteq12dva f3_mpteq12dva a_cmpt f1_mpteq12dva f4_mpteq12dva f5_mpteq12dva a_cmpt a_wceq p_syl2anc $.
$}

$(An equality inference for the maps to notation.  (Contributed by NM,
       24-Aug-2011.)  (Revised by Mario Carneiro, 16-Dec-2013.) $)

${
	$v ph x A B C D  $.
	$d x ph  $.
	$d A  $.
	$d B  $.
	$d C  $.
	$d D  $.
	f0_mpteq12dv $f wff ph $.
	f1_mpteq12dv $f set x $.
	f2_mpteq12dv $f class A $.
	f3_mpteq12dv $f class B $.
	f4_mpteq12dv $f class C $.
	f5_mpteq12dv $f class D $.
	e0_mpteq12dv $e |- ( ph -> A = C ) $.
	e1_mpteq12dv $e |- ( ph -> B = D ) $.
	p_mpteq12dv $p |- ( ph -> ( x e. A |-> B ) = ( x e. C |-> D ) ) $= e0_mpteq12dv e1_mpteq12dv f0_mpteq12dv f3_mpteq12dv f5_mpteq12dv a_wceq f1_mpteq12dv a_sup_set_class f2_mpteq12dv a_wcel p_adantr f0_mpteq12dv f1_mpteq12dv f2_mpteq12dv f3_mpteq12dv f4_mpteq12dv f5_mpteq12dv p_mpteq12dva $.
$}

$(An equality theorem for the maps to notation.  (Contributed by NM,
       16-Dec-2013.) $)

${
	$v x A B C D  $.
	$d x A  $.
	$d x C  $.
	f0_mpteq12 $f set x $.
	f1_mpteq12 $f class A $.
	f2_mpteq12 $f class B $.
	f3_mpteq12 $f class C $.
	f4_mpteq12 $f class D $.
	p_mpteq12 $p |- ( ( A = C /\ A. x e. A B = D ) -> ( x e. A |-> B ) = ( x e. C |-> D ) ) $= f1_mpteq12 f3_mpteq12 a_wceq f0_mpteq12 a_ax-17 f0_mpteq12 f1_mpteq12 f2_mpteq12 f3_mpteq12 f4_mpteq12 p_mpteq12f f1_mpteq12 f3_mpteq12 a_wceq f1_mpteq12 f3_mpteq12 a_wceq f0_mpteq12 a_wal f2_mpteq12 f4_mpteq12 a_wceq f0_mpteq12 f1_mpteq12 a_wral f0_mpteq12 f1_mpteq12 f2_mpteq12 a_cmpt f0_mpteq12 f3_mpteq12 f4_mpteq12 a_cmpt a_wceq p_sylan $.
$}

$(An equality theorem for the maps to notation.  (Contributed by Mario
       Carneiro, 16-Dec-2013.) $)

${
	$v x A B C  $.
	$d x A  $.
	$d x B  $.
	f0_mpteq1 $f set x $.
	f1_mpteq1 $f class A $.
	f2_mpteq1 $f class B $.
	f3_mpteq1 $f class C $.
	p_mpteq1 $p |- ( A = B -> ( x e. A |-> C ) = ( x e. B |-> C ) ) $= f0_mpteq1 a_sup_set_class f1_mpteq1 a_wcel f3_mpteq1 p_eqidd f3_mpteq1 f3_mpteq1 a_wceq f0_mpteq1 f1_mpteq1 p_rgen f0_mpteq1 f1_mpteq1 f3_mpteq1 f2_mpteq1 f3_mpteq1 p_mpteq12 f1_mpteq1 f2_mpteq1 a_wceq f3_mpteq1 f3_mpteq1 a_wceq f0_mpteq1 f1_mpteq1 a_wral f0_mpteq1 f1_mpteq1 f3_mpteq1 a_cmpt f0_mpteq1 f2_mpteq1 f3_mpteq1 a_cmpt a_wceq p_mpan2 $.
$}

$(An equality theorem for the maps to notation.  (Contributed by Mario
       Carneiro, 11-Jun-2016.) $)

${
	$v ph x A B C  $.
	$d x A  $.
	$d x B  $.
	f0_mpteq1d $f wff ph $.
	f1_mpteq1d $f set x $.
	f2_mpteq1d $f class A $.
	f3_mpteq1d $f class B $.
	f4_mpteq1d $f class C $.
	e0_mpteq1d $e |- ( ph -> A = B ) $.
	p_mpteq1d $p |- ( ph -> ( x e. A |-> C ) = ( x e. B |-> C ) ) $= e0_mpteq1d f1_mpteq1d f2_mpteq1d f3_mpteq1d f4_mpteq1d p_mpteq1 f0_mpteq1d f2_mpteq1d f3_mpteq1d a_wceq f1_mpteq1d f2_mpteq1d f4_mpteq1d a_cmpt f1_mpteq1d f3_mpteq1d f4_mpteq1d a_cmpt a_wceq p_syl $.
$}

$(An equality inference for the maps to notation.  (Contributed by Mario
       Carneiro, 16-Dec-2013.) $)

${
	$v x A B C  $.
	f0_mpteq2ia $f set x $.
	f1_mpteq2ia $f class A $.
	f2_mpteq2ia $f class B $.
	f3_mpteq2ia $f class C $.
	e0_mpteq2ia $e |- ( x e. A -> B = C ) $.
	p_mpteq2ia $p |- ( x e. A |-> B ) = ( x e. A |-> C ) $= f1_mpteq2ia p_eqid f1_mpteq2ia f1_mpteq2ia a_wceq f0_mpteq2ia a_ax-gen e0_mpteq2ia f2_mpteq2ia f3_mpteq2ia a_wceq f0_mpteq2ia f1_mpteq2ia p_rgen f0_mpteq2ia f1_mpteq2ia f2_mpteq2ia f1_mpteq2ia f3_mpteq2ia p_mpteq12f f1_mpteq2ia f1_mpteq2ia a_wceq f0_mpteq2ia a_wal f2_mpteq2ia f3_mpteq2ia a_wceq f0_mpteq2ia f1_mpteq2ia a_wral f0_mpteq2ia f1_mpteq2ia f2_mpteq2ia a_cmpt f0_mpteq2ia f1_mpteq2ia f3_mpteq2ia a_cmpt a_wceq p_mp2an $.
$}

$(An equality inference for the maps to notation.  (Contributed by Mario
       Carneiro, 16-Dec-2013.) $)

${
	$v x A B C  $.
	f0_mpteq2i $f set x $.
	f1_mpteq2i $f class A $.
	f2_mpteq2i $f class B $.
	f3_mpteq2i $f class C $.
	e0_mpteq2i $e |- B = C $.
	p_mpteq2i $p |- ( x e. A |-> B ) = ( x e. A |-> C ) $= e0_mpteq2i f2_mpteq2i f3_mpteq2i a_wceq f0_mpteq2i a_sup_set_class f1_mpteq2i a_wcel p_a1i f0_mpteq2i f1_mpteq2i f2_mpteq2i f3_mpteq2i p_mpteq2ia $.
$}

$(An equality inference for the maps to notation.  (Contributed by Scott
       Fenton, 27-Oct-2010.)  (Revised by Mario Carneiro, 16-Dec-2013.) $)

${
	$v x A B C D  $.
	f0_mpteq12i $f set x $.
	f1_mpteq12i $f class A $.
	f2_mpteq12i $f class B $.
	f3_mpteq12i $f class C $.
	f4_mpteq12i $f class D $.
	e0_mpteq12i $e |- A = C $.
	e1_mpteq12i $e |- B = D $.
	p_mpteq12i $p |- ( x e. A |-> B ) = ( x e. C |-> D ) $= e0_mpteq12i f1_mpteq12i f3_mpteq12i a_wceq a_wtru p_a1i e1_mpteq12i f2_mpteq12i f4_mpteq12i a_wceq a_wtru p_a1i a_wtru f0_mpteq12i f1_mpteq12i f2_mpteq12i f3_mpteq12i f4_mpteq12i p_mpteq12dv f0_mpteq12i f1_mpteq12i f2_mpteq12i a_cmpt f0_mpteq12i f3_mpteq12i f4_mpteq12i a_cmpt a_wceq p_trud $.
$}

$(Slightly more general equality inference for the maps to notation.
       (Contributed by FL, 14-Sep-2013.)  (Revised by Mario Carneiro,
       16-Dec-2013.) $)

${
	$v ph x A B C  $.
	f0_mpteq2da $f wff ph $.
	f1_mpteq2da $f set x $.
	f2_mpteq2da $f class A $.
	f3_mpteq2da $f class B $.
	f4_mpteq2da $f class C $.
	e0_mpteq2da $e |- F/ x ph $.
	e1_mpteq2da $e |- ( ( ph /\ x e. A ) -> B = C ) $.
	p_mpteq2da $p |- ( ph -> ( x e. A |-> B ) = ( x e. A |-> C ) ) $= f2_mpteq2da p_eqid f2_mpteq2da f2_mpteq2da a_wceq f1_mpteq2da a_ax-gen e0_mpteq2da e1_mpteq2da f0_mpteq2da f1_mpteq2da a_sup_set_class f2_mpteq2da a_wcel f3_mpteq2da f4_mpteq2da a_wceq p_ex f0_mpteq2da f3_mpteq2da f4_mpteq2da a_wceq f1_mpteq2da f2_mpteq2da p_ralrimi f1_mpteq2da f2_mpteq2da f3_mpteq2da f2_mpteq2da f4_mpteq2da p_mpteq12f f0_mpteq2da f2_mpteq2da f2_mpteq2da a_wceq f1_mpteq2da a_wal f3_mpteq2da f4_mpteq2da a_wceq f1_mpteq2da f2_mpteq2da a_wral f1_mpteq2da f2_mpteq2da f3_mpteq2da a_cmpt f1_mpteq2da f2_mpteq2da f4_mpteq2da a_cmpt a_wceq p_sylancr $.
$}

$(Slightly more general equality inference for the maps to notation.
       (Contributed by Scott Fenton, 25-Apr-2012.) $)

${
	$v ph x A B C  $.
	$d x ph  $.
	f0_mpteq2dva $f wff ph $.
	f1_mpteq2dva $f set x $.
	f2_mpteq2dva $f class A $.
	f3_mpteq2dva $f class B $.
	f4_mpteq2dva $f class C $.
	e0_mpteq2dva $e |- ( ( ph /\ x e. A ) -> B = C ) $.
	p_mpteq2dva $p |- ( ph -> ( x e. A |-> B ) = ( x e. A |-> C ) ) $= f0_mpteq2dva f1_mpteq2dva p_nfv e0_mpteq2dva f0_mpteq2dva f1_mpteq2dva f2_mpteq2dva f3_mpteq2dva f4_mpteq2dva p_mpteq2da $.
$}

$(An equality inference for the maps to notation.  (Contributed by Mario
       Carneiro, 23-Aug-2014.) $)

${
	$v ph x A B C  $.
	$d x ph  $.
	f0_mpteq2dv $f wff ph $.
	f1_mpteq2dv $f set x $.
	f2_mpteq2dv $f class A $.
	f3_mpteq2dv $f class B $.
	f4_mpteq2dv $f class C $.
	e0_mpteq2dv $e |- ( ph -> B = C ) $.
	p_mpteq2dv $p |- ( ph -> ( x e. A |-> B ) = ( x e. A |-> C ) ) $= e0_mpteq2dv f0_mpteq2dv f3_mpteq2dv f4_mpteq2dv a_wceq f1_mpteq2dv a_sup_set_class f2_mpteq2dv a_wcel p_adantr f0_mpteq2dv f1_mpteq2dv f2_mpteq2dv f3_mpteq2dv f4_mpteq2dv p_mpteq2dva $.
$}

$(Bound-variable hypothesis builder for the maps-to notation.
       (Contributed by NM, 20-Feb-2013.) $)

${
	$v x y A B  $.
	$d z A  $.
	$d z B  $.
	$d x y z  $.
	f0_nfmpt $f set x $.
	f1_nfmpt $f set y $.
	f2_nfmpt $f class A $.
	f3_nfmpt $f class B $.
	i0_nfmpt $f set z $.
	e0_nfmpt $e |- F/_ x A $.
	e1_nfmpt $e |- F/_ x B $.
	p_nfmpt $p |- F/_ x ( y e. A |-> B ) $= f1_nfmpt i0_nfmpt f2_nfmpt f3_nfmpt a_df-mpt e0_nfmpt f0_nfmpt f1_nfmpt f2_nfmpt p_nfcri e1_nfmpt f0_nfmpt i0_nfmpt a_sup_set_class f3_nfmpt p_nfeq2 f1_nfmpt a_sup_set_class f2_nfmpt a_wcel i0_nfmpt a_sup_set_class f3_nfmpt a_wceq f0_nfmpt p_nfan f1_nfmpt a_sup_set_class f2_nfmpt a_wcel i0_nfmpt a_sup_set_class f3_nfmpt a_wceq a_wa f1_nfmpt i0_nfmpt f0_nfmpt p_nfopab f0_nfmpt f1_nfmpt f2_nfmpt f3_nfmpt a_cmpt f1_nfmpt a_sup_set_class f2_nfmpt a_wcel i0_nfmpt a_sup_set_class f3_nfmpt a_wceq a_wa f1_nfmpt i0_nfmpt a_copab p_nfcxfr $.
$}

$(Bound-variable hypothesis builder for the maps-to notation.
       (Contributed by FL, 17-Feb-2008.) $)

${
	$v x A B  $.
	$d A z  $.
	$d B z  $.
	$d x  $.
	$d x z  $.
	f0_nfmpt1 $f set x $.
	f1_nfmpt1 $f class A $.
	f2_nfmpt1 $f class B $.
	i0_nfmpt1 $f set z $.
	p_nfmpt1 $p |- F/_ x ( x e. A |-> B ) $= f0_nfmpt1 i0_nfmpt1 f1_nfmpt1 f2_nfmpt1 a_df-mpt f0_nfmpt1 a_sup_set_class f1_nfmpt1 a_wcel i0_nfmpt1 a_sup_set_class f2_nfmpt1 a_wceq a_wa f0_nfmpt1 i0_nfmpt1 p_nfopab1 f0_nfmpt1 f0_nfmpt1 f1_nfmpt1 f2_nfmpt1 a_cmpt f0_nfmpt1 a_sup_set_class f1_nfmpt1 a_wcel i0_nfmpt1 a_sup_set_class f2_nfmpt1 a_wceq a_wa f0_nfmpt1 i0_nfmpt1 a_copab p_nfcxfr $.
$}

$(Rule to change the bound variable in a maps-to function, using implicit
       substitution.  This version has bound-variable hypotheses in place of
       distinct variable conditions.  (Contributed by NM, 11-Sep-2011.) $)

${
	$v x y A B C  $.
	$d w z x A  $.
	$d w z y A  $.
	$d w z B  $.
	$d w z C  $.
	f0_cbvmpt $f set x $.
	f1_cbvmpt $f set y $.
	f2_cbvmpt $f class A $.
	f3_cbvmpt $f class B $.
	f4_cbvmpt $f class C $.
	i0_cbvmpt $f set z $.
	i1_cbvmpt $f set w $.
	e0_cbvmpt $e |- F/_ y B $.
	e1_cbvmpt $e |- F/_ x C $.
	e2_cbvmpt $e |- ( x = y -> B = C ) $.
	p_cbvmpt $p |- ( x e. A |-> B ) = ( y e. A |-> C ) $= f0_cbvmpt a_sup_set_class f2_cbvmpt a_wcel i0_cbvmpt a_sup_set_class f3_cbvmpt a_wceq a_wa i1_cbvmpt p_nfv i1_cbvmpt a_sup_set_class f2_cbvmpt a_wcel f0_cbvmpt p_nfv i0_cbvmpt a_sup_set_class f3_cbvmpt a_wceq f0_cbvmpt i1_cbvmpt p_nfs1v i1_cbvmpt a_sup_set_class f2_cbvmpt a_wcel i0_cbvmpt a_sup_set_class f3_cbvmpt a_wceq f0_cbvmpt i1_cbvmpt a_wsb f0_cbvmpt p_nfan f0_cbvmpt a_sup_set_class i1_cbvmpt a_sup_set_class f2_cbvmpt p_eleq1 i0_cbvmpt a_sup_set_class f3_cbvmpt a_wceq f0_cbvmpt i1_cbvmpt p_sbequ12 f0_cbvmpt a_sup_set_class i1_cbvmpt a_sup_set_class a_wceq f0_cbvmpt a_sup_set_class f2_cbvmpt a_wcel i1_cbvmpt a_sup_set_class f2_cbvmpt a_wcel i0_cbvmpt a_sup_set_class f3_cbvmpt a_wceq i0_cbvmpt a_sup_set_class f3_cbvmpt a_wceq f0_cbvmpt i1_cbvmpt a_wsb p_anbi12d f0_cbvmpt a_sup_set_class f2_cbvmpt a_wcel i0_cbvmpt a_sup_set_class f3_cbvmpt a_wceq a_wa i1_cbvmpt a_sup_set_class f2_cbvmpt a_wcel i0_cbvmpt a_sup_set_class f3_cbvmpt a_wceq f0_cbvmpt i1_cbvmpt a_wsb a_wa f0_cbvmpt i0_cbvmpt i1_cbvmpt p_cbvopab1 i1_cbvmpt a_sup_set_class f2_cbvmpt a_wcel f1_cbvmpt p_nfv e0_cbvmpt f1_cbvmpt i0_cbvmpt a_sup_set_class f3_cbvmpt p_nfeq2 i0_cbvmpt a_sup_set_class f3_cbvmpt a_wceq f0_cbvmpt i1_cbvmpt f1_cbvmpt p_nfsb i1_cbvmpt a_sup_set_class f2_cbvmpt a_wcel i0_cbvmpt a_sup_set_class f3_cbvmpt a_wceq f0_cbvmpt i1_cbvmpt a_wsb f1_cbvmpt p_nfan f1_cbvmpt a_sup_set_class f2_cbvmpt a_wcel i0_cbvmpt a_sup_set_class f4_cbvmpt a_wceq a_wa i1_cbvmpt p_nfv i1_cbvmpt a_sup_set_class f1_cbvmpt a_sup_set_class f2_cbvmpt p_eleq1 i0_cbvmpt a_sup_set_class f3_cbvmpt a_wceq i1_cbvmpt f1_cbvmpt f0_cbvmpt p_sbequ e1_cbvmpt f0_cbvmpt i0_cbvmpt a_sup_set_class f4_cbvmpt p_nfeq2 e2_cbvmpt f0_cbvmpt a_sup_set_class f1_cbvmpt a_sup_set_class a_wceq f3_cbvmpt f4_cbvmpt i0_cbvmpt a_sup_set_class p_eqeq2d i0_cbvmpt a_sup_set_class f3_cbvmpt a_wceq i0_cbvmpt a_sup_set_class f4_cbvmpt a_wceq f0_cbvmpt f1_cbvmpt p_sbie i1_cbvmpt a_sup_set_class f1_cbvmpt a_sup_set_class a_wceq i0_cbvmpt a_sup_set_class f3_cbvmpt a_wceq f0_cbvmpt i1_cbvmpt a_wsb i0_cbvmpt a_sup_set_class f3_cbvmpt a_wceq f0_cbvmpt f1_cbvmpt a_wsb i0_cbvmpt a_sup_set_class f4_cbvmpt a_wceq p_syl6bb i1_cbvmpt a_sup_set_class f1_cbvmpt a_sup_set_class a_wceq i1_cbvmpt a_sup_set_class f2_cbvmpt a_wcel f1_cbvmpt a_sup_set_class f2_cbvmpt a_wcel i0_cbvmpt a_sup_set_class f3_cbvmpt a_wceq f0_cbvmpt i1_cbvmpt a_wsb i0_cbvmpt a_sup_set_class f4_cbvmpt a_wceq p_anbi12d i1_cbvmpt a_sup_set_class f2_cbvmpt a_wcel i0_cbvmpt a_sup_set_class f3_cbvmpt a_wceq f0_cbvmpt i1_cbvmpt a_wsb a_wa f1_cbvmpt a_sup_set_class f2_cbvmpt a_wcel i0_cbvmpt a_sup_set_class f4_cbvmpt a_wceq a_wa i1_cbvmpt i0_cbvmpt f1_cbvmpt p_cbvopab1 f0_cbvmpt a_sup_set_class f2_cbvmpt a_wcel i0_cbvmpt a_sup_set_class f3_cbvmpt a_wceq a_wa f0_cbvmpt i0_cbvmpt a_copab i1_cbvmpt a_sup_set_class f2_cbvmpt a_wcel i0_cbvmpt a_sup_set_class f3_cbvmpt a_wceq f0_cbvmpt i1_cbvmpt a_wsb a_wa i1_cbvmpt i0_cbvmpt a_copab f1_cbvmpt a_sup_set_class f2_cbvmpt a_wcel i0_cbvmpt a_sup_set_class f4_cbvmpt a_wceq a_wa f1_cbvmpt i0_cbvmpt a_copab p_eqtri f0_cbvmpt i0_cbvmpt f2_cbvmpt f3_cbvmpt a_df-mpt f1_cbvmpt i0_cbvmpt f2_cbvmpt f4_cbvmpt a_df-mpt f0_cbvmpt a_sup_set_class f2_cbvmpt a_wcel i0_cbvmpt a_sup_set_class f3_cbvmpt a_wceq a_wa f0_cbvmpt i0_cbvmpt a_copab f1_cbvmpt a_sup_set_class f2_cbvmpt a_wcel i0_cbvmpt a_sup_set_class f4_cbvmpt a_wceq a_wa f1_cbvmpt i0_cbvmpt a_copab f0_cbvmpt f2_cbvmpt f3_cbvmpt a_cmpt f1_cbvmpt f2_cbvmpt f4_cbvmpt a_cmpt p_3eqtr4i $.
$}

$(Rule to change the bound variable in a maps-to function, using implicit
       substitution.  (Contributed by Mario Carneiro, 19-Feb-2013.) $)

${
	$v x y A B C  $.
	$d A x  $.
	$d A y  $.
	$d B y  $.
	$d C x  $.
	f0_cbvmptv $f set x $.
	f1_cbvmptv $f set y $.
	f2_cbvmptv $f class A $.
	f3_cbvmptv $f class B $.
	f4_cbvmptv $f class C $.
	e0_cbvmptv $e |- ( x = y -> B = C ) $.
	p_cbvmptv $p |- ( x e. A |-> B ) = ( y e. A |-> C ) $= f1_cbvmptv f3_cbvmptv p_nfcv f0_cbvmptv f4_cbvmptv p_nfcv e0_cbvmptv f0_cbvmptv f1_cbvmptv f2_cbvmptv f3_cbvmptv f4_cbvmptv p_cbvmpt $.
$}

$(Function with universal domain in maps-to notation.  (Contributed by NM,
       16-Aug-2013.) $)

${
	$v x y B  $.
	$d x y  $.
	$d y B  $.
	f0_mptv $f set x $.
	f1_mptv $f set y $.
	f2_mptv $f class B $.
	p_mptv $p |- ( x e. _V |-> B ) = { <. x , y >. | y = B } $= f0_mptv f1_mptv a_cvv f2_mptv a_df-mpt f0_mptv p_vex f0_mptv a_sup_set_class a_cvv a_wcel f1_mptv a_sup_set_class f2_mptv a_wceq p_biantrur f1_mptv a_sup_set_class f2_mptv a_wceq f0_mptv a_sup_set_class a_cvv a_wcel f1_mptv a_sup_set_class f2_mptv a_wceq a_wa f0_mptv f1_mptv p_opabbii f0_mptv a_cvv f2_mptv a_cmpt f0_mptv a_sup_set_class a_cvv a_wcel f1_mptv a_sup_set_class f2_mptv a_wceq a_wa f0_mptv f1_mptv a_copab f1_mptv a_sup_set_class f2_mptv a_wceq f0_mptv f1_mptv a_copab p_eqtr4i $.
$}


