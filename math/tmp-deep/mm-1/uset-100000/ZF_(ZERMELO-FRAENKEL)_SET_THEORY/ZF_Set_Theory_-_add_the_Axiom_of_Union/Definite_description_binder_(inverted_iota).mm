$[ turnstile_special_source.mm $]

$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Union/Relations.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Definite description binder (inverted iota)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$c iota $.

$(Extend class notation with Russell's definition description binder
     (inverted iota). $)

${
	$v ph x  $.
	f0_cio $f wff ph $.
	f1_cio $f set x $.
	a_cio $a class ( iota x ph ) $.
$}

$(Soundness justification theorem for ~ df-iota .  (Contributed by Andrew
       Salmon, 29-Jun-2011.) $)

${
	$v ph x y z  $.
	$d w x z  $.
	$d ph w z  $.
	$d ph w y  $.
	$d x y  $.
	f0_iotajust $f wff ph $.
	f1_iotajust $f set x $.
	f2_iotajust $f set y $.
	f3_iotajust $f set z $.
	i0_iotajust $f set w $.
	p_iotajust $p |- U. { y | { x | ph } = { y } } = U. { z | { x | ph } = { z } } $= f2_iotajust a_sup_set_class i0_iotajust a_sup_set_class p_sneq f2_iotajust a_sup_set_class i0_iotajust a_sup_set_class a_wceq f2_iotajust a_sup_set_class a_csn i0_iotajust a_sup_set_class a_csn f0_iotajust f1_iotajust a_cab p_eqeq2d f0_iotajust f1_iotajust a_cab f2_iotajust a_sup_set_class a_csn a_wceq f0_iotajust f1_iotajust a_cab i0_iotajust a_sup_set_class a_csn a_wceq f2_iotajust i0_iotajust p_cbvabv i0_iotajust a_sup_set_class f3_iotajust a_sup_set_class p_sneq i0_iotajust a_sup_set_class f3_iotajust a_sup_set_class a_wceq i0_iotajust a_sup_set_class a_csn f3_iotajust a_sup_set_class a_csn f0_iotajust f1_iotajust a_cab p_eqeq2d f0_iotajust f1_iotajust a_cab i0_iotajust a_sup_set_class a_csn a_wceq f0_iotajust f1_iotajust a_cab f3_iotajust a_sup_set_class a_csn a_wceq i0_iotajust f3_iotajust p_cbvabv f0_iotajust f1_iotajust a_cab f2_iotajust a_sup_set_class a_csn a_wceq f2_iotajust a_cab f0_iotajust f1_iotajust a_cab i0_iotajust a_sup_set_class a_csn a_wceq i0_iotajust a_cab f0_iotajust f1_iotajust a_cab f3_iotajust a_sup_set_class a_csn a_wceq f3_iotajust a_cab p_eqtri f0_iotajust f1_iotajust a_cab f2_iotajust a_sup_set_class a_csn a_wceq f2_iotajust a_cab f0_iotajust f1_iotajust a_cab f3_iotajust a_sup_set_class a_csn a_wceq f3_iotajust a_cab p_unieqi $.
$}

$(Define Russell's definition description binder, which can be read as
       "the unique ` x ` such that ` ph ` ," where ` ph ` ordinarily contains
       ` x ` as a free variable.  Our definition is meaningful only when there
       is exactly one ` x ` such that ` ph ` is true (see ~ iotaval );
       otherwise, it evaluates to the empty set (see ~ iotanul ).  Russell used
       the inverted iota symbol ` iota ` to represent the binder.

       Sometimes proofs need to expand an iota-based definition.  That is,
       given "X = the x for which ... x ... x ..." holds, the proof needs to
       get to "...  X ...  X ...".  A general strategy to do this is to use
       ~ riotacl2 (or ~ iotacl for unbounded iota), as demonstrated in the
       proof of ~ supub .  This can be easier than applying ~ riotasbc or a
       version that applies an explicit substitution, because substituting an
       iota into its own property always has a bound variable clash which must
       be first renamed or else guarded with NF.

       (Contributed by Andrew Salmon, 30-Jun-2011.) $)

${
	$v ph x y  $.
	$d y x  $.
	$d y ph  $.
	f0_df-iota $f wff ph $.
	f1_df-iota $f set x $.
	f2_df-iota $f set y $.
	a_df-iota $a |- ( iota x ph ) = U. { y | { x | ph } = { y } } $.
$}

$(Alternate definition for descriptions.  Definition 8.18 in [Quine]
       p. 56.  (Contributed by Andrew Salmon, 30-Jun-2011.) $)

${
	$v ph x y  $.
	$d y x  $.
	$d y ph  $.
	f0_dfiota2 $f wff ph $.
	f1_dfiota2 $f set x $.
	f2_dfiota2 $f set y $.
	p_dfiota2 $p |- ( iota x ph ) = U. { y | A. x ( ph <-> x = y ) } $= f0_dfiota2 f1_dfiota2 f2_dfiota2 a_df-iota f1_dfiota2 f2_dfiota2 a_sup_set_class a_df-sn f2_dfiota2 a_sup_set_class a_csn f1_dfiota2 a_sup_set_class f2_dfiota2 a_sup_set_class a_wceq f1_dfiota2 a_cab f0_dfiota2 f1_dfiota2 a_cab p_eqeq2i f0_dfiota2 f1_dfiota2 a_sup_set_class f2_dfiota2 a_sup_set_class a_wceq f1_dfiota2 p_abbi f0_dfiota2 f1_dfiota2 a_cab f2_dfiota2 a_sup_set_class a_csn a_wceq f0_dfiota2 f1_dfiota2 a_cab f1_dfiota2 a_sup_set_class f2_dfiota2 a_sup_set_class a_wceq f1_dfiota2 a_cab a_wceq f0_dfiota2 f1_dfiota2 a_sup_set_class f2_dfiota2 a_sup_set_class a_wceq a_wb f1_dfiota2 a_wal p_bitr4i f0_dfiota2 f1_dfiota2 a_cab f2_dfiota2 a_sup_set_class a_csn a_wceq f0_dfiota2 f1_dfiota2 a_sup_set_class f2_dfiota2 a_sup_set_class a_wceq a_wb f1_dfiota2 a_wal f2_dfiota2 p_abbii f0_dfiota2 f1_dfiota2 a_cab f2_dfiota2 a_sup_set_class a_csn a_wceq f2_dfiota2 a_cab f0_dfiota2 f1_dfiota2 a_sup_set_class f2_dfiota2 a_sup_set_class a_wceq a_wb f1_dfiota2 a_wal f2_dfiota2 a_cab p_unieqi f0_dfiota2 f1_dfiota2 a_cio f0_dfiota2 f1_dfiota2 a_cab f2_dfiota2 a_sup_set_class a_csn a_wceq f2_dfiota2 a_cab a_cuni f0_dfiota2 f1_dfiota2 a_sup_set_class f2_dfiota2 a_sup_set_class a_wceq a_wb f1_dfiota2 a_wal f2_dfiota2 a_cab a_cuni p_eqtri $.
$}

$(Bound-variable hypothesis builder for the ` iota ` class.  (Contributed
       by Andrew Salmon, 11-Jul-2011.)  (Revised by Mario Carneiro,
       15-Oct-2016.) $)

${
	$v ph x  $.
	$d x y  $.
	$d y ph  $.
	f0_nfiota1 $f wff ph $.
	f1_nfiota1 $f set x $.
	i0_nfiota1 $f set y $.
	p_nfiota1 $p |- F/_ x ( iota x ph ) $= f0_nfiota1 f1_nfiota1 i0_nfiota1 p_dfiota2 f0_nfiota1 f1_nfiota1 a_sup_set_class i0_nfiota1 a_sup_set_class a_wceq a_wb f1_nfiota1 i0_nfiota1 p_nfaba1 f1_nfiota1 f0_nfiota1 f1_nfiota1 a_sup_set_class i0_nfiota1 a_sup_set_class a_wceq a_wb f1_nfiota1 a_wal i0_nfiota1 a_cab p_nfuni f1_nfiota1 f0_nfiota1 f1_nfiota1 a_cio f0_nfiota1 f1_nfiota1 a_sup_set_class i0_nfiota1 a_sup_set_class a_wceq a_wb f1_nfiota1 a_wal i0_nfiota1 a_cab a_cuni p_nfcxfr $.
$}

$(Deduction version of ~ nfiota .  (Contributed by NM, 18-Feb-2013.) $)

${
	$v ph ps x y  $.
	$d z ps  $.
	$d z ph  $.
	$d x z  $.
	$d y z  $.
	f0_nfiotad $f wff ph $.
	f1_nfiotad $f wff ps $.
	f2_nfiotad $f set x $.
	f3_nfiotad $f set y $.
	i0_nfiotad $f set z $.
	e0_nfiotad $e |- F/ y ph $.
	e1_nfiotad $e |- ( ph -> F/ x ps ) $.
	p_nfiotad $p |- ( ph -> F/_ x ( iota y ps ) ) $= f1_nfiotad f3_nfiotad i0_nfiotad p_dfiota2 f0_nfiotad i0_nfiotad p_nfv e0_nfiotad e1_nfiotad f0_nfiotad f1_nfiotad f2_nfiotad a_wnf f2_nfiotad a_sup_set_class f3_nfiotad a_sup_set_class a_wceq f2_nfiotad a_wal a_wn p_adantr f2_nfiotad f3_nfiotad p_nfcvf f2_nfiotad a_sup_set_class f3_nfiotad a_sup_set_class a_wceq f2_nfiotad a_wal a_wn f2_nfiotad f3_nfiotad a_sup_set_class a_wnfc f0_nfiotad p_adantl f0_nfiotad f2_nfiotad a_sup_set_class f3_nfiotad a_sup_set_class a_wceq f2_nfiotad a_wal a_wn a_wa f2_nfiotad i0_nfiotad a_sup_set_class p_nfcvd f0_nfiotad f2_nfiotad a_sup_set_class f3_nfiotad a_sup_set_class a_wceq f2_nfiotad a_wal a_wn a_wa f2_nfiotad f3_nfiotad a_sup_set_class i0_nfiotad a_sup_set_class p_nfeqd f0_nfiotad f2_nfiotad a_sup_set_class f3_nfiotad a_sup_set_class a_wceq f2_nfiotad a_wal a_wn a_wa f1_nfiotad f3_nfiotad a_sup_set_class i0_nfiotad a_sup_set_class a_wceq f2_nfiotad p_nfbid f0_nfiotad f1_nfiotad f3_nfiotad a_sup_set_class i0_nfiotad a_sup_set_class a_wceq a_wb f2_nfiotad f3_nfiotad p_nfald2 f0_nfiotad f1_nfiotad f3_nfiotad a_sup_set_class i0_nfiotad a_sup_set_class a_wceq a_wb f3_nfiotad a_wal f2_nfiotad i0_nfiotad p_nfabd f0_nfiotad f2_nfiotad f1_nfiotad f3_nfiotad a_sup_set_class i0_nfiotad a_sup_set_class a_wceq a_wb f3_nfiotad a_wal i0_nfiotad a_cab p_nfunid f0_nfiotad f2_nfiotad f1_nfiotad f3_nfiotad a_cio f1_nfiotad f3_nfiotad a_sup_set_class i0_nfiotad a_sup_set_class a_wceq a_wb f3_nfiotad a_wal i0_nfiotad a_cab a_cuni p_nfcxfrd $.
$}

$(Bound-variable hypothesis builder for the ` iota ` class.  (Contributed
       by NM, 23-Aug-2011.) $)

${
	$v ph x y  $.
	$d ph  $.
	$d x  $.
	$d y  $.
	f0_nfiota $f wff ph $.
	f1_nfiota $f set x $.
	f2_nfiota $f set y $.
	e0_nfiota $e |- F/ x ph $.
	p_nfiota $p |- F/_ x ( iota y ph ) $= f2_nfiota p_nftru e0_nfiota f0_nfiota f1_nfiota a_wnf a_wtru p_a1i a_wtru f0_nfiota f1_nfiota f2_nfiota p_nfiotad f1_nfiota f0_nfiota f2_nfiota a_cio a_wnfc p_trud $.
$}

$(Change bound variables in a description binder.  (Contributed by Andrew
       Salmon, 1-Aug-2011.) $)

${
	$v ph ps x y  $.
	$d z w x  $.
	$d z w y  $.
	$d z w ph  $.
	$d z w ps  $.
	f0_cbviota $f wff ph $.
	f1_cbviota $f wff ps $.
	f2_cbviota $f set x $.
	f3_cbviota $f set y $.
	i0_cbviota $f set z $.
	i1_cbviota $f set w $.
	e0_cbviota $e |- ( x = y -> ( ph <-> ps ) ) $.
	e1_cbviota $e |- F/ y ph $.
	e2_cbviota $e |- F/ x ps $.
	p_cbviota $p |- ( iota x ph ) = ( iota y ps ) $= f0_cbviota f2_cbviota a_sup_set_class i1_cbviota a_sup_set_class a_wceq a_wb i0_cbviota p_nfv f0_cbviota f2_cbviota i0_cbviota p_nfs1v i0_cbviota a_sup_set_class i1_cbviota a_sup_set_class a_wceq f2_cbviota p_nfv f0_cbviota f2_cbviota i0_cbviota a_wsb i0_cbviota a_sup_set_class i1_cbviota a_sup_set_class a_wceq f2_cbviota p_nfbi f0_cbviota f2_cbviota i0_cbviota p_sbequ12 f2_cbviota i0_cbviota i1_cbviota p_equequ1 f2_cbviota a_sup_set_class i0_cbviota a_sup_set_class a_wceq f0_cbviota f0_cbviota f2_cbviota i0_cbviota a_wsb f2_cbviota a_sup_set_class i1_cbviota a_sup_set_class a_wceq i0_cbviota a_sup_set_class i1_cbviota a_sup_set_class a_wceq p_bibi12d f0_cbviota f2_cbviota a_sup_set_class i1_cbviota a_sup_set_class a_wceq a_wb f0_cbviota f2_cbviota i0_cbviota a_wsb i0_cbviota a_sup_set_class i1_cbviota a_sup_set_class a_wceq a_wb f2_cbviota i0_cbviota p_cbval e1_cbviota f0_cbviota f2_cbviota i0_cbviota f3_cbviota p_nfsb i0_cbviota a_sup_set_class i1_cbviota a_sup_set_class a_wceq f3_cbviota p_nfv f0_cbviota f2_cbviota i0_cbviota a_wsb i0_cbviota a_sup_set_class i1_cbviota a_sup_set_class a_wceq f3_cbviota p_nfbi f1_cbviota f3_cbviota a_sup_set_class i1_cbviota a_sup_set_class a_wceq a_wb i0_cbviota p_nfv f0_cbviota i0_cbviota f3_cbviota f2_cbviota p_sbequ e2_cbviota e0_cbviota f0_cbviota f1_cbviota f2_cbviota f3_cbviota p_sbie i0_cbviota a_sup_set_class f3_cbviota a_sup_set_class a_wceq f0_cbviota f2_cbviota i0_cbviota a_wsb f0_cbviota f2_cbviota f3_cbviota a_wsb f1_cbviota p_syl6bb i0_cbviota f3_cbviota i1_cbviota p_equequ1 i0_cbviota a_sup_set_class f3_cbviota a_sup_set_class a_wceq f0_cbviota f2_cbviota i0_cbviota a_wsb f1_cbviota i0_cbviota a_sup_set_class i1_cbviota a_sup_set_class a_wceq f3_cbviota a_sup_set_class i1_cbviota a_sup_set_class a_wceq p_bibi12d f0_cbviota f2_cbviota i0_cbviota a_wsb i0_cbviota a_sup_set_class i1_cbviota a_sup_set_class a_wceq a_wb f1_cbviota f3_cbviota a_sup_set_class i1_cbviota a_sup_set_class a_wceq a_wb i0_cbviota f3_cbviota p_cbval f0_cbviota f2_cbviota a_sup_set_class i1_cbviota a_sup_set_class a_wceq a_wb f2_cbviota a_wal f0_cbviota f2_cbviota i0_cbviota a_wsb i0_cbviota a_sup_set_class i1_cbviota a_sup_set_class a_wceq a_wb i0_cbviota a_wal f1_cbviota f3_cbviota a_sup_set_class i1_cbviota a_sup_set_class a_wceq a_wb f3_cbviota a_wal p_bitri f0_cbviota f2_cbviota a_sup_set_class i1_cbviota a_sup_set_class a_wceq a_wb f2_cbviota a_wal f1_cbviota f3_cbviota a_sup_set_class i1_cbviota a_sup_set_class a_wceq a_wb f3_cbviota a_wal i1_cbviota p_abbii f0_cbviota f2_cbviota a_sup_set_class i1_cbviota a_sup_set_class a_wceq a_wb f2_cbviota a_wal i1_cbviota a_cab f1_cbviota f3_cbviota a_sup_set_class i1_cbviota a_sup_set_class a_wceq a_wb f3_cbviota a_wal i1_cbviota a_cab p_unieqi f0_cbviota f2_cbviota i1_cbviota p_dfiota2 f1_cbviota f3_cbviota i1_cbviota p_dfiota2 f0_cbviota f2_cbviota a_sup_set_class i1_cbviota a_sup_set_class a_wceq a_wb f2_cbviota a_wal i1_cbviota a_cab a_cuni f1_cbviota f3_cbviota a_sup_set_class i1_cbviota a_sup_set_class a_wceq a_wb f3_cbviota a_wal i1_cbviota a_cab a_cuni f0_cbviota f2_cbviota a_cio f1_cbviota f3_cbviota a_cio p_3eqtr4i $.
$}

$(Change bound variables in a description binder.  (Contributed by Andrew
       Salmon, 1-Aug-2011.) $)

${
	$v ph ps x y  $.
	$d ph y  $.
	$d ps x  $.
	f0_cbviotav $f wff ph $.
	f1_cbviotav $f wff ps $.
	f2_cbviotav $f set x $.
	f3_cbviotav $f set y $.
	e0_cbviotav $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_cbviotav $p |- ( iota x ph ) = ( iota y ps ) $= e0_cbviotav f0_cbviotav f3_cbviotav p_nfv f1_cbviotav f2_cbviotav p_nfv f0_cbviotav f1_cbviotav f2_cbviotav f3_cbviotav p_cbviota $.
$}

$(Variable substitution in description binder.  Compare ~ sb8eu .
       (Contributed by NM, 18-Mar-2013.) $)

${
	$v ph x y  $.
	$d w z ph  $.
	$d w z x  $.
	$d w z y  $.
	f0_sb8iota $f wff ph $.
	f1_sb8iota $f set x $.
	f2_sb8iota $f set y $.
	i0_sb8iota $f set z $.
	i1_sb8iota $f set w $.
	e0_sb8iota $e |- F/ y ph $.
	p_sb8iota $p |- ( iota x ph ) = ( iota y [ y / x ] ph ) $= f0_sb8iota f1_sb8iota a_sup_set_class i0_sb8iota a_sup_set_class a_wceq a_wb i1_sb8iota p_nfv f0_sb8iota f1_sb8iota a_sup_set_class i0_sb8iota a_sup_set_class a_wceq a_wb f1_sb8iota i1_sb8iota p_sb8 f0_sb8iota f1_sb8iota a_sup_set_class i0_sb8iota a_sup_set_class a_wceq f1_sb8iota i1_sb8iota p_sbbi e0_sb8iota f0_sb8iota f1_sb8iota i1_sb8iota f2_sb8iota p_nfsb i1_sb8iota f1_sb8iota i0_sb8iota a_sup_set_class p_eqsb3 i1_sb8iota a_sup_set_class i0_sb8iota a_sup_set_class a_wceq f2_sb8iota p_nfv f1_sb8iota a_sup_set_class i0_sb8iota a_sup_set_class a_wceq f1_sb8iota i1_sb8iota a_wsb i1_sb8iota a_sup_set_class i0_sb8iota a_sup_set_class a_wceq f2_sb8iota p_nfxfr f0_sb8iota f1_sb8iota i1_sb8iota a_wsb f1_sb8iota a_sup_set_class i0_sb8iota a_sup_set_class a_wceq f1_sb8iota i1_sb8iota a_wsb f2_sb8iota p_nfbi f0_sb8iota f1_sb8iota a_sup_set_class i0_sb8iota a_sup_set_class a_wceq a_wb f1_sb8iota i1_sb8iota a_wsb f0_sb8iota f1_sb8iota i1_sb8iota a_wsb f1_sb8iota a_sup_set_class i0_sb8iota a_sup_set_class a_wceq f1_sb8iota i1_sb8iota a_wsb a_wb f2_sb8iota p_nfxfr f0_sb8iota f1_sb8iota a_sup_set_class i0_sb8iota a_sup_set_class a_wceq a_wb f1_sb8iota f2_sb8iota a_wsb i1_sb8iota p_nfv f0_sb8iota f1_sb8iota a_sup_set_class i0_sb8iota a_sup_set_class a_wceq a_wb i1_sb8iota f2_sb8iota f1_sb8iota p_sbequ f0_sb8iota f1_sb8iota a_sup_set_class i0_sb8iota a_sup_set_class a_wceq a_wb f1_sb8iota i1_sb8iota a_wsb f0_sb8iota f1_sb8iota a_sup_set_class i0_sb8iota a_sup_set_class a_wceq a_wb f1_sb8iota f2_sb8iota a_wsb i1_sb8iota f2_sb8iota p_cbval f2_sb8iota f1_sb8iota i0_sb8iota p_equsb3 f1_sb8iota a_sup_set_class i0_sb8iota a_sup_set_class a_wceq f2_sb8iota a_sup_set_class i0_sb8iota a_sup_set_class a_wceq f0_sb8iota f1_sb8iota f2_sb8iota p_sblbis f0_sb8iota f1_sb8iota a_sup_set_class i0_sb8iota a_sup_set_class a_wceq a_wb f1_sb8iota f2_sb8iota a_wsb f0_sb8iota f1_sb8iota f2_sb8iota a_wsb f2_sb8iota a_sup_set_class i0_sb8iota a_sup_set_class a_wceq a_wb f2_sb8iota p_albii f0_sb8iota f1_sb8iota a_sup_set_class i0_sb8iota a_sup_set_class a_wceq a_wb f1_sb8iota a_wal f0_sb8iota f1_sb8iota a_sup_set_class i0_sb8iota a_sup_set_class a_wceq a_wb f1_sb8iota i1_sb8iota a_wsb i1_sb8iota a_wal f0_sb8iota f1_sb8iota a_sup_set_class i0_sb8iota a_sup_set_class a_wceq a_wb f1_sb8iota f2_sb8iota a_wsb f2_sb8iota a_wal f0_sb8iota f1_sb8iota f2_sb8iota a_wsb f2_sb8iota a_sup_set_class i0_sb8iota a_sup_set_class a_wceq a_wb f2_sb8iota a_wal p_3bitri f0_sb8iota f1_sb8iota a_sup_set_class i0_sb8iota a_sup_set_class a_wceq a_wb f1_sb8iota a_wal f0_sb8iota f1_sb8iota f2_sb8iota a_wsb f2_sb8iota a_sup_set_class i0_sb8iota a_sup_set_class a_wceq a_wb f2_sb8iota a_wal i0_sb8iota p_abbii f0_sb8iota f1_sb8iota a_sup_set_class i0_sb8iota a_sup_set_class a_wceq a_wb f1_sb8iota a_wal i0_sb8iota a_cab f0_sb8iota f1_sb8iota f2_sb8iota a_wsb f2_sb8iota a_sup_set_class i0_sb8iota a_sup_set_class a_wceq a_wb f2_sb8iota a_wal i0_sb8iota a_cab p_unieqi f0_sb8iota f1_sb8iota i0_sb8iota p_dfiota2 f0_sb8iota f1_sb8iota f2_sb8iota a_wsb f2_sb8iota i0_sb8iota p_dfiota2 f0_sb8iota f1_sb8iota a_sup_set_class i0_sb8iota a_sup_set_class a_wceq a_wb f1_sb8iota a_wal i0_sb8iota a_cab a_cuni f0_sb8iota f1_sb8iota f2_sb8iota a_wsb f2_sb8iota a_sup_set_class i0_sb8iota a_sup_set_class a_wceq a_wb f2_sb8iota a_wal i0_sb8iota a_cab a_cuni f0_sb8iota f1_sb8iota a_cio f0_sb8iota f1_sb8iota f2_sb8iota a_wsb f2_sb8iota a_cio p_3eqtr4i $.
$}

$(Equality theorem for descriptions.  (Contributed by Andrew Salmon,
       30-Jun-2011.) $)

${
	$v ph x y  $.
	$d y z  $.
	$d x z  $.
	$d ph z  $.
	f0_iotaeq $f wff ph $.
	f1_iotaeq $f set x $.
	f2_iotaeq $f set y $.
	i0_iotaeq $f set z $.
	p_iotaeq $p |- ( A. x x = y -> ( iota x ph ) = ( iota y ph ) ) $= f0_iotaeq f1_iotaeq f2_iotaeq i0_iotaeq p_drsb1 f0_iotaeq i0_iotaeq f1_iotaeq a_df-clab f0_iotaeq i0_iotaeq f2_iotaeq a_df-clab f1_iotaeq a_sup_set_class f2_iotaeq a_sup_set_class a_wceq f1_iotaeq a_wal f0_iotaeq f1_iotaeq i0_iotaeq a_wsb f0_iotaeq f2_iotaeq i0_iotaeq a_wsb i0_iotaeq a_sup_set_class f0_iotaeq f1_iotaeq a_cab a_wcel i0_iotaeq a_sup_set_class f0_iotaeq f2_iotaeq a_cab a_wcel p_3bitr4g f1_iotaeq a_sup_set_class f2_iotaeq a_sup_set_class a_wceq f1_iotaeq a_wal i0_iotaeq f0_iotaeq f1_iotaeq a_cab f0_iotaeq f2_iotaeq a_cab p_eqrdv f1_iotaeq a_sup_set_class f2_iotaeq a_sup_set_class a_wceq f1_iotaeq a_wal f0_iotaeq f1_iotaeq a_cab f0_iotaeq f2_iotaeq a_cab i0_iotaeq a_sup_set_class a_csn p_eqeq1d f1_iotaeq a_sup_set_class f2_iotaeq a_sup_set_class a_wceq f1_iotaeq a_wal f0_iotaeq f1_iotaeq a_cab i0_iotaeq a_sup_set_class a_csn a_wceq f0_iotaeq f2_iotaeq a_cab i0_iotaeq a_sup_set_class a_csn a_wceq i0_iotaeq p_abbidv f1_iotaeq a_sup_set_class f2_iotaeq a_sup_set_class a_wceq f1_iotaeq a_wal f0_iotaeq f1_iotaeq a_cab i0_iotaeq a_sup_set_class a_csn a_wceq i0_iotaeq a_cab f0_iotaeq f2_iotaeq a_cab i0_iotaeq a_sup_set_class a_csn a_wceq i0_iotaeq a_cab p_unieqd f0_iotaeq f1_iotaeq i0_iotaeq a_df-iota f0_iotaeq f2_iotaeq i0_iotaeq a_df-iota f1_iotaeq a_sup_set_class f2_iotaeq a_sup_set_class a_wceq f1_iotaeq a_wal f0_iotaeq f1_iotaeq a_cab i0_iotaeq a_sup_set_class a_csn a_wceq i0_iotaeq a_cab a_cuni f0_iotaeq f2_iotaeq a_cab i0_iotaeq a_sup_set_class a_csn a_wceq i0_iotaeq a_cab a_cuni f0_iotaeq f1_iotaeq a_cio f0_iotaeq f2_iotaeq a_cio p_3eqtr4g $.
$}

$(Equivalence theorem for descriptions.  (Contributed by Andrew Salmon,
       30-Jun-2011.) $)

${
	$v ph ps x  $.
	$d ph z  $.
	$d ps z  $.
	$d x z  $.
	f0_iotabi $f wff ph $.
	f1_iotabi $f wff ps $.
	f2_iotabi $f set x $.
	i0_iotabi $f set z $.
	p_iotabi $p |- ( A. x ( ph <-> ps ) -> ( iota x ph ) = ( iota x ps ) ) $= f0_iotabi f1_iotabi f2_iotabi p_abbi f0_iotabi f1_iotabi a_wb f2_iotabi a_wal f0_iotabi f2_iotabi a_cab f1_iotabi f2_iotabi a_cab a_wceq p_biimpi f0_iotabi f1_iotabi a_wb f2_iotabi a_wal f0_iotabi f2_iotabi a_cab f1_iotabi f2_iotabi a_cab i0_iotabi a_sup_set_class a_csn p_eqeq1d f0_iotabi f1_iotabi a_wb f2_iotabi a_wal f0_iotabi f2_iotabi a_cab i0_iotabi a_sup_set_class a_csn a_wceq f1_iotabi f2_iotabi a_cab i0_iotabi a_sup_set_class a_csn a_wceq i0_iotabi p_abbidv f0_iotabi f1_iotabi a_wb f2_iotabi a_wal f0_iotabi f2_iotabi a_cab i0_iotabi a_sup_set_class a_csn a_wceq i0_iotabi a_cab f1_iotabi f2_iotabi a_cab i0_iotabi a_sup_set_class a_csn a_wceq i0_iotabi a_cab p_unieqd f0_iotabi f2_iotabi i0_iotabi a_df-iota f1_iotabi f2_iotabi i0_iotabi a_df-iota f0_iotabi f1_iotabi a_wb f2_iotabi a_wal f0_iotabi f2_iotabi a_cab i0_iotabi a_sup_set_class a_csn a_wceq i0_iotabi a_cab a_cuni f1_iotabi f2_iotabi a_cab i0_iotabi a_sup_set_class a_csn a_wceq i0_iotabi a_cab a_cuni f0_iotabi f2_iotabi a_cio f1_iotabi f2_iotabi a_cio p_3eqtr4g $.
$}

$(Part of Theorem 8.17 in [Quine] p. 56.  This theorem serves as a lemma
       for the fundamental property of iota.  (Contributed by Andrew Salmon,
       11-Jul-2011.) $)

${
	$v ph x y  $.
	$d ph  $.
	$d x y  $.
	f0_uniabio $f wff ph $.
	f1_uniabio $f set x $.
	f2_uniabio $f set y $.
	p_uniabio $p |- ( A. x ( ph <-> x = y ) -> U. { x | ph } = y ) $= f0_uniabio f1_uniabio a_sup_set_class f2_uniabio a_sup_set_class a_wceq f1_uniabio p_abbi f0_uniabio f1_uniabio a_sup_set_class f2_uniabio a_sup_set_class a_wceq a_wb f1_uniabio a_wal f0_uniabio f1_uniabio a_cab f1_uniabio a_sup_set_class f2_uniabio a_sup_set_class a_wceq f1_uniabio a_cab a_wceq p_biimpi f1_uniabio f2_uniabio a_sup_set_class a_df-sn f0_uniabio f1_uniabio a_sup_set_class f2_uniabio a_sup_set_class a_wceq a_wb f1_uniabio a_wal f0_uniabio f1_uniabio a_cab f1_uniabio a_sup_set_class f2_uniabio a_sup_set_class a_wceq f1_uniabio a_cab f2_uniabio a_sup_set_class a_csn p_syl6eqr f0_uniabio f1_uniabio a_sup_set_class f2_uniabio a_sup_set_class a_wceq a_wb f1_uniabio a_wal f0_uniabio f1_uniabio a_cab f2_uniabio a_sup_set_class a_csn p_unieqd f2_uniabio p_vex f2_uniabio a_sup_set_class p_unisn f0_uniabio f1_uniabio a_sup_set_class f2_uniabio a_sup_set_class a_wceq a_wb f1_uniabio a_wal f0_uniabio f1_uniabio a_cab a_cuni f2_uniabio a_sup_set_class a_csn a_cuni f2_uniabio a_sup_set_class p_syl6eq $.
$}

$(Theorem 8.19 in [Quine] p. 57.  This theorem is the fundamental property
       of iota.  (Contributed by Andrew Salmon, 11-Jul-2011.) $)

${
	$v ph x y  $.
	$d ph z  $.
	$d z  $.
	$d x y z  $.
	f0_iotaval $f wff ph $.
	f1_iotaval $f set x $.
	f2_iotaval $f set y $.
	i0_iotaval $f set z $.
	p_iotaval $p |- ( A. x ( ph <-> x = y ) -> ( iota x ph ) = y ) $= f0_iotaval f1_iotaval i0_iotaval p_dfiota2 f2_iotaval p_vex f0_iotaval f1_iotaval f2_iotaval a_sup_set_class i0_iotaval a_sup_set_class a_cvv p_sbeqalb f2_iotaval i0_iotaval p_equcomi f2_iotaval a_sup_set_class a_cvv a_wcel f0_iotaval f1_iotaval a_sup_set_class f2_iotaval a_sup_set_class a_wceq a_wb f1_iotaval a_wal f0_iotaval f1_iotaval a_sup_set_class i0_iotaval a_sup_set_class a_wceq a_wb f1_iotaval a_wal a_wa f2_iotaval a_sup_set_class i0_iotaval a_sup_set_class a_wceq i0_iotaval a_sup_set_class f2_iotaval a_sup_set_class a_wceq p_syl6 f2_iotaval a_sup_set_class a_cvv a_wcel f0_iotaval f1_iotaval a_sup_set_class f2_iotaval a_sup_set_class a_wceq a_wb f1_iotaval a_wal f0_iotaval f1_iotaval a_sup_set_class i0_iotaval a_sup_set_class a_wceq a_wb f1_iotaval a_wal a_wa i0_iotaval a_sup_set_class f2_iotaval a_sup_set_class a_wceq a_wi a_ax-mp f0_iotaval f1_iotaval a_sup_set_class f2_iotaval a_sup_set_class a_wceq a_wb f1_iotaval a_wal f0_iotaval f1_iotaval a_sup_set_class i0_iotaval a_sup_set_class a_wceq a_wb f1_iotaval a_wal i0_iotaval a_sup_set_class f2_iotaval a_sup_set_class a_wceq p_ex f2_iotaval i0_iotaval f1_iotaval p_equequ2 f1_iotaval a_sup_set_class f2_iotaval a_sup_set_class a_wceq f1_iotaval a_sup_set_class i0_iotaval a_sup_set_class a_wceq a_wb f2_iotaval a_sup_set_class i0_iotaval a_sup_set_class p_eqcoms i0_iotaval a_sup_set_class f2_iotaval a_sup_set_class a_wceq f1_iotaval a_sup_set_class f2_iotaval a_sup_set_class a_wceq f1_iotaval a_sup_set_class i0_iotaval a_sup_set_class a_wceq f0_iotaval p_bibi2d i0_iotaval a_sup_set_class f2_iotaval a_sup_set_class a_wceq f0_iotaval f1_iotaval a_sup_set_class f2_iotaval a_sup_set_class a_wceq a_wb f0_iotaval f1_iotaval a_sup_set_class i0_iotaval a_sup_set_class a_wceq a_wb p_biimpd i0_iotaval a_sup_set_class f2_iotaval a_sup_set_class a_wceq f0_iotaval f1_iotaval a_sup_set_class f2_iotaval a_sup_set_class a_wceq a_wb f0_iotaval f1_iotaval a_sup_set_class i0_iotaval a_sup_set_class a_wceq a_wb f1_iotaval p_alimdv i0_iotaval a_sup_set_class f2_iotaval a_sup_set_class a_wceq f0_iotaval f1_iotaval a_sup_set_class f2_iotaval a_sup_set_class a_wceq a_wb f1_iotaval a_wal f0_iotaval f1_iotaval a_sup_set_class i0_iotaval a_sup_set_class a_wceq a_wb f1_iotaval a_wal p_com12 f0_iotaval f1_iotaval a_sup_set_class f2_iotaval a_sup_set_class a_wceq a_wb f1_iotaval a_wal f0_iotaval f1_iotaval a_sup_set_class i0_iotaval a_sup_set_class a_wceq a_wb f1_iotaval a_wal i0_iotaval a_sup_set_class f2_iotaval a_sup_set_class a_wceq p_impbid f0_iotaval f1_iotaval a_sup_set_class f2_iotaval a_sup_set_class a_wceq a_wb f1_iotaval a_wal f0_iotaval f1_iotaval a_sup_set_class i0_iotaval a_sup_set_class a_wceq a_wb f1_iotaval a_wal i0_iotaval a_sup_set_class f2_iotaval a_sup_set_class a_wceq a_wb i0_iotaval p_alrimiv f0_iotaval f1_iotaval a_sup_set_class i0_iotaval a_sup_set_class a_wceq a_wb f1_iotaval a_wal i0_iotaval f2_iotaval p_uniabio f0_iotaval f1_iotaval a_sup_set_class f2_iotaval a_sup_set_class a_wceq a_wb f1_iotaval a_wal f0_iotaval f1_iotaval a_sup_set_class i0_iotaval a_sup_set_class a_wceq a_wb f1_iotaval a_wal i0_iotaval a_sup_set_class f2_iotaval a_sup_set_class a_wceq a_wb i0_iotaval a_wal f0_iotaval f1_iotaval a_sup_set_class i0_iotaval a_sup_set_class a_wceq a_wb f1_iotaval a_wal i0_iotaval a_cab a_cuni f2_iotaval a_sup_set_class a_wceq p_syl f0_iotaval f1_iotaval a_sup_set_class f2_iotaval a_sup_set_class a_wceq a_wb f1_iotaval a_wal f0_iotaval f1_iotaval a_cio f0_iotaval f1_iotaval a_sup_set_class i0_iotaval a_sup_set_class a_wceq a_wb f1_iotaval a_wal i0_iotaval a_cab a_cuni f2_iotaval a_sup_set_class p_syl5eq $.
$}

$(Equivalence between two different forms of ` iota ` .  (Contributed by
       Andrew Salmon, 12-Jul-2011.) $)

${
	$v ph x  $.
	$d ph z  $.
	$d z  $.
	$d x z  $.
	f0_iotauni $f wff ph $.
	f1_iotauni $f set x $.
	i0_iotauni $f set z $.
	p_iotauni $p |- ( E! x ph -> ( iota x ph ) = U. { x | ph } ) $= f0_iotauni f1_iotauni i0_iotauni a_df-eu f0_iotauni f1_iotauni i0_iotauni p_iotaval f0_iotauni f1_iotauni i0_iotauni p_uniabio f0_iotauni f1_iotauni a_sup_set_class i0_iotauni a_sup_set_class a_wceq a_wb f1_iotauni a_wal f0_iotauni f1_iotauni a_cio i0_iotauni a_sup_set_class f0_iotauni f1_iotauni a_cab a_cuni p_eqtr4d f0_iotauni f1_iotauni a_sup_set_class i0_iotauni a_sup_set_class a_wceq a_wb f1_iotauni a_wal f0_iotauni f1_iotauni a_cio f0_iotauni f1_iotauni a_cab a_cuni a_wceq i0_iotauni p_exlimiv f0_iotauni f1_iotauni a_weu f0_iotauni f1_iotauni a_sup_set_class i0_iotauni a_sup_set_class a_wceq a_wb f1_iotauni a_wal i0_iotauni a_wex f0_iotauni f1_iotauni a_cio f0_iotauni f1_iotauni a_cab a_cuni a_wceq p_sylbi $.
$}

$(Equivalence between two different forms of ` iota ` .  (Contributed by
       Mario Carneiro, 24-Dec-2016.) $)

${
	$v ph x  $.
	$d ph  $.
	$d x  $.
	f0_iotaint $f wff ph $.
	f1_iotaint $f set x $.
	p_iotaint $p |- ( E! x ph -> ( iota x ph ) = |^| { x | ph } ) $= f0_iotaint f1_iotaint p_iotauni f0_iotaint f1_iotaint p_uniintab f0_iotaint f1_iotaint a_weu f0_iotaint f1_iotaint a_cab a_cuni f0_iotaint f1_iotaint a_cab a_cint a_wceq p_biimpi f0_iotaint f1_iotaint a_weu f0_iotaint f1_iotaint a_cio f0_iotaint f1_iotaint a_cab a_cuni f0_iotaint f1_iotaint a_cab a_cint p_eqtrd $.
$}

$(Property of iota.  (Contributed by NM, 23-Aug-2011.)  (Revised by Mario
       Carneiro, 23-Dec-2016.) $)

${
	$v ph x  $.
	$d ph z  $.
	$d z  $.
	$d x z  $.
	f0_iota1 $f wff ph $.
	f1_iota1 $f set x $.
	i0_iota1 $f set z $.
	p_iota1 $p |- ( E! x ph -> ( ph <-> ( iota x ph ) = x ) ) $= f0_iota1 f1_iota1 i0_iota1 a_df-eu f0_iota1 f1_iota1 a_sup_set_class i0_iota1 a_sup_set_class a_wceq a_wb f1_iota1 p_sp f0_iota1 f1_iota1 i0_iota1 p_iotaval f0_iota1 f1_iota1 a_sup_set_class i0_iota1 a_sup_set_class a_wceq a_wb f1_iota1 a_wal f0_iota1 f1_iota1 a_cio i0_iota1 a_sup_set_class f1_iota1 a_sup_set_class p_eqeq2d f0_iota1 f1_iota1 a_sup_set_class i0_iota1 a_sup_set_class a_wceq a_wb f1_iota1 a_wal f0_iota1 f1_iota1 a_sup_set_class i0_iota1 a_sup_set_class a_wceq f1_iota1 a_sup_set_class f0_iota1 f1_iota1 a_cio a_wceq p_bitr4d f1_iota1 a_sup_set_class f0_iota1 f1_iota1 a_cio p_eqcom f0_iota1 f1_iota1 a_sup_set_class i0_iota1 a_sup_set_class a_wceq a_wb f1_iota1 a_wal f0_iota1 f1_iota1 a_sup_set_class f0_iota1 f1_iota1 a_cio a_wceq f0_iota1 f1_iota1 a_cio f1_iota1 a_sup_set_class a_wceq p_syl6bb f0_iota1 f1_iota1 a_sup_set_class i0_iota1 a_sup_set_class a_wceq a_wb f1_iota1 a_wal f0_iota1 f0_iota1 f1_iota1 a_cio f1_iota1 a_sup_set_class a_wceq a_wb i0_iota1 p_exlimiv f0_iota1 f1_iota1 a_weu f0_iota1 f1_iota1 a_sup_set_class i0_iota1 a_sup_set_class a_wceq a_wb f1_iota1 a_wal i0_iota1 a_wex f0_iota1 f0_iota1 f1_iota1 a_cio f1_iota1 a_sup_set_class a_wceq a_wb p_sylbi $.
$}

$(Theorem 8.22 in [Quine] p. 57.  This theorem is the result if there
       isn't exactly one ` x ` that satisfies ` ph ` .  (Contributed by Andrew
       Salmon, 11-Jul-2011.) $)

${
	$v ph x  $.
	$d ph z  $.
	$d z  $.
	$d x z  $.
	f0_iotanul $f wff ph $.
	f1_iotanul $f set x $.
	i0_iotanul $f set z $.
	p_iotanul $p |- ( -. E! x ph -> ( iota x ph ) = (/) ) $= f0_iotanul f1_iotanul i0_iotanul a_df-eu f0_iotanul f1_iotanul i0_iotanul p_dfiota2 f0_iotanul f1_iotanul a_sup_set_class i0_iotanul a_sup_set_class a_wceq a_wb f1_iotanul a_wal i0_iotanul p_alnex f0_iotanul f1_iotanul a_sup_set_class i0_iotanul a_sup_set_class a_wceq a_wb f1_iotanul a_wal a_wn i0_iotanul a_sup_set_class i0_iotanul a_sup_set_class a_wceq a_ax-1 f0_iotanul f1_iotanul a_sup_set_class i0_iotanul a_sup_set_class a_wceq a_wb f1_iotanul a_wal a_wn i0_iotanul a_sup_set_class p_eqidd f0_iotanul f1_iotanul a_sup_set_class i0_iotanul a_sup_set_class a_wceq a_wb f1_iotanul a_wal a_wn i0_iotanul a_sup_set_class i0_iotanul a_sup_set_class a_wceq f0_iotanul f1_iotanul a_sup_set_class i0_iotanul a_sup_set_class a_wceq a_wb f1_iotanul a_wal a_wn p_impbid1 f0_iotanul f1_iotanul a_sup_set_class i0_iotanul a_sup_set_class a_wceq a_wb f1_iotanul a_wal a_wn i0_iotanul a_sup_set_class i0_iotanul a_sup_set_class a_wceq f0_iotanul f1_iotanul a_sup_set_class i0_iotanul a_sup_set_class a_wceq a_wb f1_iotanul a_wal p_con2bid f0_iotanul f1_iotanul a_sup_set_class i0_iotanul a_sup_set_class a_wceq a_wb f1_iotanul a_wal a_wn f0_iotanul f1_iotanul a_sup_set_class i0_iotanul a_sup_set_class a_wceq a_wb f1_iotanul a_wal i0_iotanul a_sup_set_class i0_iotanul a_sup_set_class a_wceq a_wn a_wb i0_iotanul p_alimi f0_iotanul f1_iotanul a_sup_set_class i0_iotanul a_sup_set_class a_wceq a_wb f1_iotanul a_wal i0_iotanul a_sup_set_class i0_iotanul a_sup_set_class a_wceq a_wn i0_iotanul p_abbi f0_iotanul f1_iotanul a_sup_set_class i0_iotanul a_sup_set_class a_wceq a_wb f1_iotanul a_wal a_wn i0_iotanul a_wal f0_iotanul f1_iotanul a_sup_set_class i0_iotanul a_sup_set_class a_wceq a_wb f1_iotanul a_wal i0_iotanul a_sup_set_class i0_iotanul a_sup_set_class a_wceq a_wn a_wb i0_iotanul a_wal f0_iotanul f1_iotanul a_sup_set_class i0_iotanul a_sup_set_class a_wceq a_wb f1_iotanul a_wal i0_iotanul a_cab i0_iotanul a_sup_set_class i0_iotanul a_sup_set_class a_wceq a_wn i0_iotanul a_cab a_wceq p_sylib i0_iotanul p_dfnul2 f0_iotanul f1_iotanul a_sup_set_class i0_iotanul a_sup_set_class a_wceq a_wb f1_iotanul a_wal a_wn i0_iotanul a_wal f0_iotanul f1_iotanul a_sup_set_class i0_iotanul a_sup_set_class a_wceq a_wb f1_iotanul a_wal i0_iotanul a_cab i0_iotanul a_sup_set_class i0_iotanul a_sup_set_class a_wceq a_wn i0_iotanul a_cab a_c0 p_syl6eqr f0_iotanul f1_iotanul a_sup_set_class i0_iotanul a_sup_set_class a_wceq a_wb f1_iotanul a_wal i0_iotanul a_wex a_wn f0_iotanul f1_iotanul a_sup_set_class i0_iotanul a_sup_set_class a_wceq a_wb f1_iotanul a_wal a_wn i0_iotanul a_wal f0_iotanul f1_iotanul a_sup_set_class i0_iotanul a_sup_set_class a_wceq a_wb f1_iotanul a_wal i0_iotanul a_cab a_c0 a_wceq p_sylbir f0_iotanul f1_iotanul a_sup_set_class i0_iotanul a_sup_set_class a_wceq a_wb f1_iotanul a_wal i0_iotanul a_wex a_wn f0_iotanul f1_iotanul a_sup_set_class i0_iotanul a_sup_set_class a_wceq a_wb f1_iotanul a_wal i0_iotanul a_cab a_c0 p_unieqd p_uni0 f0_iotanul f1_iotanul a_sup_set_class i0_iotanul a_sup_set_class a_wceq a_wb f1_iotanul a_wal i0_iotanul a_wex a_wn f0_iotanul f1_iotanul a_sup_set_class i0_iotanul a_sup_set_class a_wceq a_wb f1_iotanul a_wal i0_iotanul a_cab a_cuni a_c0 a_cuni a_c0 p_syl6eq f0_iotanul f1_iotanul a_sup_set_class i0_iotanul a_sup_set_class a_wceq a_wb f1_iotanul a_wal i0_iotanul a_wex a_wn f0_iotanul f1_iotanul a_cio f0_iotanul f1_iotanul a_sup_set_class i0_iotanul a_sup_set_class a_wceq a_wb f1_iotanul a_wal i0_iotanul a_cab a_cuni a_c0 p_syl5eq f0_iotanul f1_iotanul a_weu f0_iotanul f1_iotanul a_sup_set_class i0_iotanul a_sup_set_class a_wceq a_wb f1_iotanul a_wal i0_iotanul a_wex f0_iotanul f1_iotanul a_cio a_c0 a_wceq p_sylnbi $.
$}

$(The ` iota ` class is a subset of the union of all elements satisfying
       ` ph ` .  (Contributed by Mario Carneiro, 24-Dec-2016.) $)

${
	$v ph x  $.
	$d ph  $.
	$d x  $.
	f0_iotassuni $f wff ph $.
	f1_iotassuni $f set x $.
	p_iotassuni $p |- ( iota x ph ) C_ U. { x | ph } $= f0_iotassuni f1_iotassuni p_iotauni f0_iotassuni f1_iotassuni a_cio f0_iotassuni f1_iotassuni a_cab a_cuni p_eqimss f0_iotassuni f1_iotassuni a_weu f0_iotassuni f1_iotassuni a_cio f0_iotassuni f1_iotassuni a_cab a_cuni a_wceq f0_iotassuni f1_iotassuni a_cio f0_iotassuni f1_iotassuni a_cab a_cuni a_wss p_syl f0_iotassuni f1_iotassuni a_cab a_cuni p_0ss f0_iotassuni f1_iotassuni p_iotanul f0_iotassuni f1_iotassuni a_weu a_wn f0_iotassuni f1_iotassuni a_cio a_c0 f0_iotassuni f1_iotassuni a_cab a_cuni p_sseq1d f0_iotassuni f1_iotassuni a_weu a_wn f0_iotassuni f1_iotassuni a_cio f0_iotassuni f1_iotassuni a_cab a_cuni a_wss a_c0 f0_iotassuni f1_iotassuni a_cab a_cuni a_wss p_mpbiri f0_iotassuni f1_iotassuni a_weu f0_iotassuni f1_iotassuni a_cio f0_iotassuni f1_iotassuni a_cab a_cuni a_wss p_pm2.61i $.
$}

$(Theorem 8.23 in [Quine] p. 58.  This theorem proves the existence of the
       ` iota ` class under our definition.  (Contributed by Andrew Salmon,
       11-Jul-2011.) $)

${
	$v ph x  $.
	$d ph z  $.
	$d z  $.
	$d x z  $.
	f0_iotaex $f wff ph $.
	f1_iotaex $f set x $.
	i0_iotaex $f set z $.
	p_iotaex $p |- ( iota x ph ) e. _V $= f0_iotaex f1_iotaex i0_iotaex p_iotaval f0_iotaex f1_iotaex a_sup_set_class i0_iotaex a_sup_set_class a_wceq a_wb f1_iotaex a_wal f0_iotaex f1_iotaex a_cio i0_iotaex a_sup_set_class p_eqcomd f0_iotaex f1_iotaex a_sup_set_class i0_iotaex a_sup_set_class a_wceq a_wb f1_iotaex a_wal i0_iotaex a_sup_set_class f0_iotaex f1_iotaex a_cio a_wceq i0_iotaex p_eximi f0_iotaex f1_iotaex i0_iotaex a_df-eu i0_iotaex f0_iotaex f1_iotaex a_cio p_isset f0_iotaex f1_iotaex a_sup_set_class i0_iotaex a_sup_set_class a_wceq a_wb f1_iotaex a_wal i0_iotaex a_wex i0_iotaex a_sup_set_class f0_iotaex f1_iotaex a_cio a_wceq i0_iotaex a_wex f0_iotaex f1_iotaex a_weu f0_iotaex f1_iotaex a_cio a_cvv a_wcel p_3imtr4i f0_iotaex f1_iotaex p_iotanul p_0ex f0_iotaex f1_iotaex a_weu a_wn f0_iotaex f1_iotaex a_cio a_c0 a_cvv p_syl6eqel f0_iotaex f1_iotaex a_weu f0_iotaex f1_iotaex a_cio a_cvv a_wcel p_pm2.61i $.
$}

$(Theorem *14.22 in [WhiteheadRussell] p. 190.  (Contributed by Andrew
       Salmon, 12-Jul-2011.) $)

${
	$v ph x  $.
	$d ph z  $.
	$d z  $.
	$d x z  $.
	f0_iota4 $f wff ph $.
	f1_iota4 $f set x $.
	i0_iota4 $f set z $.
	p_iota4 $p |- ( E! x ph -> [. ( iota x ph ) / x ]. ph ) $= f0_iota4 f1_iota4 i0_iota4 a_df-eu f0_iota4 f1_iota4 a_sup_set_class i0_iota4 a_sup_set_class a_wceq p_bi2 f0_iota4 f1_iota4 a_sup_set_class i0_iota4 a_sup_set_class a_wceq a_wb f1_iota4 a_sup_set_class i0_iota4 a_sup_set_class a_wceq f0_iota4 a_wi f1_iota4 p_alimi f0_iota4 f1_iota4 i0_iota4 p_sb2 f0_iota4 f1_iota4 a_sup_set_class i0_iota4 a_sup_set_class a_wceq a_wb f1_iota4 a_wal f1_iota4 a_sup_set_class i0_iota4 a_sup_set_class a_wceq f0_iota4 a_wi f1_iota4 a_wal f0_iota4 f1_iota4 i0_iota4 a_wsb p_syl f0_iota4 f1_iota4 i0_iota4 p_iotaval f0_iota4 f1_iota4 a_sup_set_class i0_iota4 a_sup_set_class a_wceq a_wb f1_iota4 a_wal f0_iota4 f1_iota4 a_cio i0_iota4 a_sup_set_class p_eqcomd f0_iota4 f1_iota4 i0_iota4 f0_iota4 f1_iota4 a_cio p_dfsbcq2 f0_iota4 f1_iota4 a_sup_set_class i0_iota4 a_sup_set_class a_wceq a_wb f1_iota4 a_wal i0_iota4 a_sup_set_class f0_iota4 f1_iota4 a_cio a_wceq f0_iota4 f1_iota4 i0_iota4 a_wsb f0_iota4 f1_iota4 f0_iota4 f1_iota4 a_cio a_wsbc a_wb p_syl f0_iota4 f1_iota4 a_sup_set_class i0_iota4 a_sup_set_class a_wceq a_wb f1_iota4 a_wal f0_iota4 f1_iota4 i0_iota4 a_wsb f0_iota4 f1_iota4 f0_iota4 f1_iota4 a_cio a_wsbc p_mpbid f0_iota4 f1_iota4 a_sup_set_class i0_iota4 a_sup_set_class a_wceq a_wb f1_iota4 a_wal f0_iota4 f1_iota4 f0_iota4 f1_iota4 a_cio a_wsbc i0_iota4 p_exlimiv f0_iota4 f1_iota4 a_weu f0_iota4 f1_iota4 a_sup_set_class i0_iota4 a_sup_set_class a_wceq a_wb f1_iota4 a_wal i0_iota4 a_wex f0_iota4 f1_iota4 f0_iota4 f1_iota4 a_cio a_wsbc p_sylbi $.
$}

$(Theorem *14.23 in [WhiteheadRussell] p. 191.  (Contributed by Andrew
     Salmon, 12-Jul-2011.) $)

${
	$v ph ps x  $.
	f0_iota4an $f wff ph $.
	f1_iota4an $f wff ps $.
	f2_iota4an $f set x $.
	p_iota4an $p |- ( E! x ( ph /\ ps ) -> [. ( iota x ( ph /\ ps ) ) / x ]. ph ) $= f0_iota4an f1_iota4an a_wa f2_iota4an p_iota4 f0_iota4an f1_iota4an a_wa f2_iota4an p_iotaex f0_iota4an f1_iota4an p_simpl f0_iota4an f1_iota4an a_wa f0_iota4an a_wi f2_iota4an f0_iota4an f1_iota4an a_wa f2_iota4an a_cio a_cvv p_sbcth f0_iota4an f1_iota4an a_wa f2_iota4an a_cio a_cvv a_wcel f0_iota4an f1_iota4an a_wa f0_iota4an a_wi f2_iota4an f0_iota4an f1_iota4an a_wa f2_iota4an a_cio a_wsbc a_ax-mp f0_iota4an f1_iota4an a_wa f2_iota4an p_iotaex f0_iota4an f1_iota4an a_wa f0_iota4an f2_iota4an f0_iota4an f1_iota4an a_wa f2_iota4an a_cio a_cvv p_sbcimg f0_iota4an f1_iota4an a_wa f2_iota4an a_cio a_cvv a_wcel f0_iota4an f1_iota4an a_wa f0_iota4an a_wi f2_iota4an f0_iota4an f1_iota4an a_wa f2_iota4an a_cio a_wsbc f0_iota4an f1_iota4an a_wa f2_iota4an f0_iota4an f1_iota4an a_wa f2_iota4an a_cio a_wsbc f0_iota4an f2_iota4an f0_iota4an f1_iota4an a_wa f2_iota4an a_cio a_wsbc a_wi a_wb a_ax-mp f0_iota4an f1_iota4an a_wa f0_iota4an a_wi f2_iota4an f0_iota4an f1_iota4an a_wa f2_iota4an a_cio a_wsbc f0_iota4an f1_iota4an a_wa f2_iota4an f0_iota4an f1_iota4an a_wa f2_iota4an a_cio a_wsbc f0_iota4an f2_iota4an f0_iota4an f1_iota4an a_wa f2_iota4an a_cio a_wsbc a_wi p_mpbi f0_iota4an f1_iota4an a_wa f2_iota4an a_weu f0_iota4an f1_iota4an a_wa f2_iota4an f0_iota4an f1_iota4an a_wa f2_iota4an a_cio a_wsbc f0_iota4an f2_iota4an f0_iota4an f1_iota4an a_wa f2_iota4an a_cio a_wsbc p_syl $.
$}

$(A method for computing iota.  (Contributed by NM, 17-Sep-2013.) $)

${
	$v ph ps x A V  $.
	$d x y A  $.
	$d x V  $.
	$d x ph  $.
	$d y ps  $.
	f0_iota5 $f wff ph $.
	f1_iota5 $f wff ps $.
	f2_iota5 $f set x $.
	f3_iota5 $f class A $.
	f4_iota5 $f class V $.
	i0_iota5 $f set y $.
	e0_iota5 $e |- ( ( ph /\ A e. V ) -> ( ps <-> x = A ) ) $.
	p_iota5 $p |- ( ( ph /\ A e. V ) -> ( iota x ps ) = A ) $= e0_iota5 f0_iota5 f3_iota5 f4_iota5 a_wcel a_wa f1_iota5 f2_iota5 a_sup_set_class f3_iota5 a_wceq a_wb f2_iota5 p_alrimiv i0_iota5 a_sup_set_class f3_iota5 f2_iota5 a_sup_set_class p_eqeq2 i0_iota5 a_sup_set_class f3_iota5 a_wceq f2_iota5 a_sup_set_class i0_iota5 a_sup_set_class a_wceq f2_iota5 a_sup_set_class f3_iota5 a_wceq f1_iota5 p_bibi2d i0_iota5 a_sup_set_class f3_iota5 a_wceq f1_iota5 f2_iota5 a_sup_set_class i0_iota5 a_sup_set_class a_wceq a_wb f1_iota5 f2_iota5 a_sup_set_class f3_iota5 a_wceq a_wb f2_iota5 p_albidv i0_iota5 a_sup_set_class f3_iota5 f1_iota5 f2_iota5 a_cio p_eqeq2 i0_iota5 a_sup_set_class f3_iota5 a_wceq f1_iota5 f2_iota5 a_sup_set_class i0_iota5 a_sup_set_class a_wceq a_wb f2_iota5 a_wal f1_iota5 f2_iota5 a_sup_set_class f3_iota5 a_wceq a_wb f2_iota5 a_wal f1_iota5 f2_iota5 a_cio i0_iota5 a_sup_set_class a_wceq f1_iota5 f2_iota5 a_cio f3_iota5 a_wceq p_imbi12d f1_iota5 f2_iota5 i0_iota5 p_iotaval f1_iota5 f2_iota5 a_sup_set_class i0_iota5 a_sup_set_class a_wceq a_wb f2_iota5 a_wal f1_iota5 f2_iota5 a_cio i0_iota5 a_sup_set_class a_wceq a_wi f1_iota5 f2_iota5 a_sup_set_class f3_iota5 a_wceq a_wb f2_iota5 a_wal f1_iota5 f2_iota5 a_cio f3_iota5 a_wceq a_wi i0_iota5 f3_iota5 f4_iota5 p_vtoclg f3_iota5 f4_iota5 a_wcel f1_iota5 f2_iota5 a_sup_set_class f3_iota5 a_wceq a_wb f2_iota5 a_wal f1_iota5 f2_iota5 a_cio f3_iota5 a_wceq a_wi f0_iota5 p_adantl f0_iota5 f3_iota5 f4_iota5 a_wcel a_wa f1_iota5 f2_iota5 a_sup_set_class f3_iota5 a_wceq a_wb f2_iota5 a_wal f1_iota5 f2_iota5 a_cio f3_iota5 a_wceq p_mpd $.
$}

$(Formula-building deduction rule for iota.  (Contributed by NM,
       20-Aug-2011.) $)

${
	$v ph ps ch x  $.
	$d x ph  $.
	f0_iotabidv $f wff ph $.
	f1_iotabidv $f wff ps $.
	f2_iotabidv $f wff ch $.
	f3_iotabidv $f set x $.
	e0_iotabidv $e |- ( ph -> ( ps <-> ch ) ) $.
	p_iotabidv $p |- ( ph -> ( iota x ps ) = ( iota x ch ) ) $= e0_iotabidv f0_iotabidv f1_iotabidv f2_iotabidv a_wb f3_iotabidv p_alrimiv f1_iotabidv f2_iotabidv f3_iotabidv p_iotabi f0_iotabidv f1_iotabidv f2_iotabidv a_wb f3_iotabidv a_wal f1_iotabidv f3_iotabidv a_cio f2_iotabidv f3_iotabidv a_cio a_wceq p_syl $.
$}

$(Formula-building deduction rule for iota.  (Contributed by Mario
       Carneiro, 2-Oct-2015.) $)

${
	$v ph ps x  $.
	f0_iotabii $f wff ph $.
	f1_iotabii $f wff ps $.
	f2_iotabii $f set x $.
	e0_iotabii $e |- ( ph <-> ps ) $.
	p_iotabii $p |- ( iota x ph ) = ( iota x ps ) $= f0_iotabii f1_iotabii f2_iotabii p_iotabi e0_iotabii f0_iotabii f1_iotabii a_wb f0_iotabii f2_iotabii a_cio f1_iotabii f2_iotabii a_cio a_wceq f2_iotabii p_mpg $.
$}

$(Membership law for descriptions.

     This can useful for expanding an unbounded iota-based definition (see
     ~ df-iota ).  If you have a bounded iota-based definition, ~ riotacl2 may
     be useful.

     (Contributed by Andrew Salmon, 1-Aug-2011.) $)

${
	$v ph x  $.
	f0_iotacl $f wff ph $.
	f1_iotacl $f set x $.
	p_iotacl $p |- ( E! x ph -> ( iota x ph ) e. { x | ph } ) $= f0_iotacl f1_iotacl p_iota4 f0_iotacl f1_iotacl f0_iotacl f1_iotacl a_cio a_df-sbc f0_iotacl f1_iotacl a_weu f0_iotacl f1_iotacl f0_iotacl f1_iotacl a_cio a_wsbc f0_iotacl f1_iotacl a_cio f0_iotacl f1_iotacl a_cab a_wcel p_sylib $.
$}

$(A condition that allows us to represent "the unique element such that
         ` ph ` " with a class expression ` A ` .  (Contributed by NM,
         30-Dec-2014.) $)

${
	$v ph ps ch x B V  $.
	$d x  $.
	$d B  $.
	$d ps  $.
	f0_iota2df $f wff ph $.
	f1_iota2df $f wff ps $.
	f2_iota2df $f wff ch $.
	f3_iota2df $f set x $.
	f4_iota2df $f class B $.
	f5_iota2df $f class V $.
	e0_iota2df $e |- ( ph -> B e. V ) $.
	e1_iota2df $e |- ( ph -> E! x ps ) $.
	e2_iota2df $e |- ( ( ph /\ x = B ) -> ( ps <-> ch ) ) $.
	e3_iota2df $e |- F/ x ph $.
	e4_iota2df $e |- ( ph -> F/ x ch ) $.
	e5_iota2df $e |- ( ph -> F/_ x B ) $.
	p_iota2df $p |- ( ph -> ( ch <-> ( iota x ps ) = B ) ) $= e5_iota2df e4_iota2df f1_iota2df f3_iota2df p_nfiota1 f3_iota2df f1_iota2df f3_iota2df a_cio a_wnfc f0_iota2df p_a1i e5_iota2df f0_iota2df f3_iota2df f1_iota2df f3_iota2df a_cio f4_iota2df p_nfeqd f0_iota2df f2_iota2df f1_iota2df f3_iota2df a_cio f4_iota2df a_wceq f3_iota2df p_nfbid e3_iota2df e2_iota2df f0_iota2df f3_iota2df a_sup_set_class f4_iota2df a_wceq p_simpr f0_iota2df f3_iota2df a_sup_set_class f4_iota2df a_wceq a_wa f3_iota2df a_sup_set_class f4_iota2df f1_iota2df f3_iota2df a_cio p_eqeq2d f0_iota2df f3_iota2df a_sup_set_class f4_iota2df a_wceq a_wa f1_iota2df f2_iota2df f1_iota2df f3_iota2df a_cio f3_iota2df a_sup_set_class a_wceq f1_iota2df f3_iota2df a_cio f4_iota2df a_wceq p_bibi12d f0_iota2df f3_iota2df a_sup_set_class f4_iota2df a_wceq f1_iota2df f1_iota2df f3_iota2df a_cio f3_iota2df a_sup_set_class a_wceq a_wb f2_iota2df f1_iota2df f3_iota2df a_cio f4_iota2df a_wceq a_wb a_wb p_ex f0_iota2df f3_iota2df a_sup_set_class f4_iota2df a_wceq f1_iota2df f1_iota2df f3_iota2df a_cio f3_iota2df a_sup_set_class a_wceq a_wb f2_iota2df f1_iota2df f3_iota2df a_cio f4_iota2df a_wceq a_wb a_wb a_wi f3_iota2df p_alrimi e3_iota2df e1_iota2df f1_iota2df f3_iota2df p_iota1 f0_iota2df f1_iota2df f3_iota2df a_weu f1_iota2df f1_iota2df f3_iota2df a_cio f3_iota2df a_sup_set_class a_wceq a_wb p_syl f0_iota2df f1_iota2df f1_iota2df f3_iota2df a_cio f3_iota2df a_sup_set_class a_wceq a_wb f3_iota2df p_alrimi e0_iota2df f1_iota2df f1_iota2df f3_iota2df a_cio f3_iota2df a_sup_set_class a_wceq a_wb f2_iota2df f1_iota2df f3_iota2df a_cio f4_iota2df a_wceq a_wb f3_iota2df f4_iota2df f5_iota2df p_vtoclgft f0_iota2df f3_iota2df f4_iota2df a_wnfc f2_iota2df f1_iota2df f3_iota2df a_cio f4_iota2df a_wceq a_wb f3_iota2df a_wnf f3_iota2df a_sup_set_class f4_iota2df a_wceq f1_iota2df f1_iota2df f3_iota2df a_cio f3_iota2df a_sup_set_class a_wceq a_wb f2_iota2df f1_iota2df f3_iota2df a_cio f4_iota2df a_wceq a_wb a_wb a_wi f3_iota2df a_wal f1_iota2df f1_iota2df f3_iota2df a_cio f3_iota2df a_sup_set_class a_wceq a_wb f3_iota2df a_wal f4_iota2df f5_iota2df a_wcel f2_iota2df f1_iota2df f3_iota2df a_cio f4_iota2df a_wceq a_wb p_syl221anc $.
$}

$(A condition that allows us to represent "the unique element such that
       ` ph ` " with a class expression ` A ` .  (Contributed by NM,
       30-Dec-2014.) $)

${
	$v ph ps ch x B V  $.
	$d x  $.
	$d B  $.
	$d ps  $.
	$d x B  $.
	$d x ph  $.
	$d x ch  $.
	f0_iota2d $f wff ph $.
	f1_iota2d $f wff ps $.
	f2_iota2d $f wff ch $.
	f3_iota2d $f set x $.
	f4_iota2d $f class B $.
	f5_iota2d $f class V $.
	e0_iota2d $e |- ( ph -> B e. V ) $.
	e1_iota2d $e |- ( ph -> E! x ps ) $.
	e2_iota2d $e |- ( ( ph /\ x = B ) -> ( ps <-> ch ) ) $.
	p_iota2d $p |- ( ph -> ( ch <-> ( iota x ps ) = B ) ) $= e0_iota2d e1_iota2d e2_iota2d f0_iota2d f3_iota2d p_nfv f0_iota2d f2_iota2d f3_iota2d p_nfvd f0_iota2d f3_iota2d f4_iota2d p_nfcvd f0_iota2d f1_iota2d f2_iota2d f3_iota2d f4_iota2d f5_iota2d p_iota2df $.
$}

$(The unique element such that ` ph ` .  (Contributed by Jeff Madsen,
       1-Jun-2011.)  (Revised by Mario Carneiro, 23-Dec-2016.) $)

${
	$v ph ps x A B  $.
	$d A x  $.
	$d ps x  $.
	f0_iota2 $f wff ph $.
	f1_iota2 $f wff ps $.
	f2_iota2 $f set x $.
	f3_iota2 $f class A $.
	f4_iota2 $f class B $.
	e0_iota2 $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_iota2 $p |- ( ( A e. B /\ E! x ph ) -> ( ps <-> ( iota x ph ) = A ) ) $= f3_iota2 f4_iota2 p_elex f3_iota2 a_cvv a_wcel f0_iota2 f2_iota2 a_weu p_simpl f3_iota2 a_cvv a_wcel f0_iota2 f2_iota2 a_weu p_simpr e0_iota2 f2_iota2 a_sup_set_class f3_iota2 a_wceq f0_iota2 f1_iota2 a_wb f3_iota2 a_cvv a_wcel f0_iota2 f2_iota2 a_weu a_wa p_adantl f3_iota2 a_cvv a_wcel f2_iota2 p_nfv f0_iota2 f2_iota2 p_nfeu1 f3_iota2 a_cvv a_wcel f0_iota2 f2_iota2 a_weu f2_iota2 p_nfan f3_iota2 a_cvv a_wcel f0_iota2 f2_iota2 a_weu a_wa f1_iota2 f2_iota2 p_nfvd f3_iota2 a_cvv a_wcel f0_iota2 f2_iota2 a_weu a_wa f2_iota2 f3_iota2 p_nfcvd f3_iota2 a_cvv a_wcel f0_iota2 f2_iota2 a_weu a_wa f0_iota2 f1_iota2 f2_iota2 f3_iota2 a_cvv p_iota2df f3_iota2 f4_iota2 a_wcel f3_iota2 a_cvv a_wcel f0_iota2 f2_iota2 a_weu f1_iota2 f0_iota2 f2_iota2 a_cio f3_iota2 a_wceq a_wb p_sylan $.
$}

$(A class abstraction with a unique member can be expressed as a singleton.
     (Contributed by Mario Carneiro, 23-Dec-2016.) $)

${
	$v ph x  $.
	f0_sniota $f wff ph $.
	f1_sniota $f set x $.
	p_sniota $p |- ( E! x ph -> { x | ph } = { ( iota x ph ) } ) $= f0_sniota f1_sniota p_nfeu1 f0_sniota f1_sniota p_iota1 f0_sniota f1_sniota a_cio f1_sniota a_sup_set_class p_eqcom f0_sniota f1_sniota a_weu f0_sniota f0_sniota f1_sniota a_cio f1_sniota a_sup_set_class a_wceq f1_sniota a_sup_set_class f0_sniota f1_sniota a_cio a_wceq p_syl6bb f0_sniota f1_sniota p_abid f1_sniota p_vex f1_sniota a_sup_set_class f0_sniota f1_sniota a_cio p_elsnc f0_sniota f1_sniota a_weu f0_sniota f1_sniota a_sup_set_class f0_sniota f1_sniota a_cio a_wceq f1_sniota a_sup_set_class f0_sniota f1_sniota a_cab a_wcel f1_sniota a_sup_set_class f0_sniota f1_sniota a_cio a_csn a_wcel p_3bitr4g f0_sniota f1_sniota a_weu f1_sniota a_sup_set_class f0_sniota f1_sniota a_cab a_wcel f1_sniota a_sup_set_class f0_sniota f1_sniota a_cio a_csn a_wcel a_wb f1_sniota p_alrimi f0_sniota f1_sniota p_nfab1 f0_sniota f1_sniota p_nfiota1 f1_sniota f0_sniota f1_sniota a_cio p_nfsn f1_sniota f0_sniota f1_sniota a_cab f0_sniota f1_sniota a_cio a_csn p_cleqf f0_sniota f1_sniota a_weu f1_sniota a_sup_set_class f0_sniota f1_sniota a_cab a_wcel f1_sniota a_sup_set_class f0_sniota f1_sniota a_cio a_csn a_wcel a_wb f1_sniota a_wal f0_sniota f1_sniota a_cab f0_sniota f1_sniota a_cio a_csn a_wceq p_sylibr $.
$}

$(The ` iota ` operation using the ` if ` operator.  (Contributed by Scott
       Fenton, 6-Oct-2017.) $)

${
	$v ph x  $.
	f0_dfiota4 $f wff ph $.
	f1_dfiota4 $f set x $.
	p_dfiota4 $p |- ( iota x ph ) = if ( E! x ph , U. { x | ph } , (/) ) $= f0_dfiota4 f1_dfiota4 p_iotauni f0_dfiota4 f1_dfiota4 a_weu f0_dfiota4 f1_dfiota4 a_cab a_cuni a_c0 p_iftrue f0_dfiota4 f1_dfiota4 a_weu f0_dfiota4 f1_dfiota4 a_cio f0_dfiota4 f1_dfiota4 a_cab a_cuni f0_dfiota4 f1_dfiota4 a_weu f0_dfiota4 f1_dfiota4 a_cab a_cuni a_c0 a_cif p_eqtr4d f0_dfiota4 f1_dfiota4 p_iotanul f0_dfiota4 f1_dfiota4 a_weu f0_dfiota4 f1_dfiota4 a_cab a_cuni a_c0 p_iffalse f0_dfiota4 f1_dfiota4 a_weu a_wn f0_dfiota4 f1_dfiota4 a_cio a_c0 f0_dfiota4 f1_dfiota4 a_weu f0_dfiota4 f1_dfiota4 a_cab a_cuni a_c0 a_cif p_eqtr4d f0_dfiota4 f1_dfiota4 a_weu f0_dfiota4 f1_dfiota4 a_cio f0_dfiota4 f1_dfiota4 a_weu f0_dfiota4 f1_dfiota4 a_cab a_cuni a_c0 a_cif a_wceq p_pm2.61i $.
$}

$(Class substitution within a description binder.  (Contributed by Scott
       Fenton, 6-Oct-2017.) $)

${
	$v ph x y A V  $.
	$d A y z  $.
	$d x y z  $.
	$d ph z  $.
	f0_csbiotag $f wff ph $.
	f1_csbiotag $f set x $.
	f2_csbiotag $f set y $.
	f3_csbiotag $f class A $.
	f4_csbiotag $f class V $.
	i0_csbiotag $f set z $.
	p_csbiotag $p |- ( A e. V -> [_ A / x ]_ ( iota y ph ) = ( iota y [. A / x ]. ph ) ) $= f1_csbiotag i0_csbiotag a_sup_set_class f3_csbiotag f0_csbiotag f2_csbiotag a_cio p_csbeq1 f0_csbiotag f1_csbiotag i0_csbiotag f3_csbiotag p_dfsbcq2 i0_csbiotag a_sup_set_class f3_csbiotag a_wceq f0_csbiotag f1_csbiotag i0_csbiotag a_wsb f0_csbiotag f1_csbiotag f3_csbiotag a_wsbc f2_csbiotag p_iotabidv i0_csbiotag a_sup_set_class f3_csbiotag a_wceq f1_csbiotag i0_csbiotag a_sup_set_class f0_csbiotag f2_csbiotag a_cio a_csb f1_csbiotag f3_csbiotag f0_csbiotag f2_csbiotag a_cio a_csb f0_csbiotag f1_csbiotag i0_csbiotag a_wsb f2_csbiotag a_cio f0_csbiotag f1_csbiotag f3_csbiotag a_wsbc f2_csbiotag a_cio p_eqeq12d i0_csbiotag p_vex f0_csbiotag f1_csbiotag i0_csbiotag p_nfs1v f0_csbiotag f1_csbiotag i0_csbiotag a_wsb f1_csbiotag f2_csbiotag p_nfiota f0_csbiotag f1_csbiotag i0_csbiotag p_sbequ12 f1_csbiotag a_sup_set_class i0_csbiotag a_sup_set_class a_wceq f0_csbiotag f0_csbiotag f1_csbiotag i0_csbiotag a_wsb f2_csbiotag p_iotabidv f1_csbiotag i0_csbiotag a_sup_set_class f0_csbiotag f2_csbiotag a_cio f0_csbiotag f1_csbiotag i0_csbiotag a_wsb f2_csbiotag a_cio p_csbief f1_csbiotag i0_csbiotag a_sup_set_class f0_csbiotag f2_csbiotag a_cio a_csb f0_csbiotag f1_csbiotag i0_csbiotag a_wsb f2_csbiotag a_cio a_wceq f1_csbiotag f3_csbiotag f0_csbiotag f2_csbiotag a_cio a_csb f0_csbiotag f1_csbiotag f3_csbiotag a_wsbc f2_csbiotag a_cio a_wceq i0_csbiotag f3_csbiotag f4_csbiotag p_vtoclg $.
$}


