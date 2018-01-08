$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Auxiliary_axiom_schemes_(4_schemes)/Axiom_scheme_ax-6_(Quantified_Negation).mm $]
$( /* =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
            Axiom scheme ax-7 (Quantifier Commutation)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
*/

$)
$( /* Axiom of Quantifier Commutation.  This axiom says universal quantifiers
     can be swapped.  One of the 4 axioms of pure predicate calculus.  Axiom
     scheme C6' in [Megill] p. 448 (p. 16 of the preprint).  Also appears as
     Lemma 12 of [Monk2] p. 109 and Axiom C5-3 of [Monk2] p. 113.  This axiom
     scheme is logically redundant (see ~ ax7w ) but is used as an auxiliary
     axiom to achieve metalogical completeness.  (Contributed by NM,
     5-Aug-1993.) */

$)
${
	fax-7_0 $f wff ph $.
	fax-7_1 $f set x $.
	fax-7_2 $f set y $.
	ax-7 $a |- ( A. x A. y ph -> A. y A. x ph ) $.
$}
$( /* Swap quantifiers in an antecedent.  (Contributed by NM, 5-Aug-1993.) */

$)
${
	fa7s_0 $f wff ph $.
	fa7s_1 $f wff ps $.
	fa7s_2 $f set x $.
	fa7s_3 $f set y $.
	ea7s_0 $e |- ( A. x A. y ph -> ps ) $.
	a7s $p |- ( A. y A. x ph -> ps ) $= fa7s_0 fa7s_2 wal fa7s_3 wal fa7s_0 fa7s_3 wal fa7s_2 wal fa7s_1 fa7s_0 fa7s_3 fa7s_2 ax-7 ea7s_0 syl $.
$}
$( /* If ` x ` is not free in ` ph ` , it is not free in ` A. y ph ` .
       (Contributed by NM, 5-Aug-1993.) */

$)
${
	fhbal_0 $f wff ph $.
	fhbal_1 $f set x $.
	fhbal_2 $f set y $.
	ehbal_0 $e |- ( ph -> A. x ph ) $.
	hbal $p |- ( A. y ph -> A. x A. y ph ) $= fhbal_0 fhbal_2 wal fhbal_0 fhbal_1 wal fhbal_2 wal fhbal_0 fhbal_2 wal fhbal_1 wal fhbal_0 fhbal_0 fhbal_1 wal fhbal_2 ehbal_0 alimi fhbal_0 fhbal_2 fhbal_1 ax-7 syl $.
$}
$( /* Theorem 19.5 of [Margaris] p. 89.  (Contributed by NM, 5-Aug-1993.) */

$)
${
	falcom_0 $f wff ph $.
	falcom_1 $f set x $.
	falcom_2 $f set y $.
	alcom $p |- ( A. x A. y ph <-> A. y A. x ph ) $= falcom_0 falcom_2 wal falcom_1 wal falcom_0 falcom_1 wal falcom_2 wal falcom_0 falcom_1 falcom_2 ax-7 falcom_0 falcom_2 falcom_1 ax-7 impbii $.
$}
$( /* Theorem *11.21 in [WhiteheadRussell] p. 160.  (Contributed by Andrew
     Salmon, 24-May-2011.) */

$)
${
	falrot3_0 $f wff ph $.
	falrot3_1 $f set x $.
	falrot3_2 $f set y $.
	falrot3_3 $f set z $.
	alrot3 $p |- ( A. x A. y A. z ph <-> A. y A. z A. x ph ) $= falrot3_0 falrot3_3 wal falrot3_2 wal falrot3_1 wal falrot3_0 falrot3_3 wal falrot3_1 wal falrot3_2 wal falrot3_0 falrot3_1 wal falrot3_3 wal falrot3_2 wal falrot3_0 falrot3_3 wal falrot3_1 falrot3_2 alcom falrot3_0 falrot3_3 wal falrot3_1 wal falrot3_0 falrot3_1 wal falrot3_3 wal falrot3_2 falrot3_0 falrot3_1 falrot3_3 alcom albii bitri $.
$}
$( /* Rotate 4 universal quantifiers twice.  (Contributed by NM, 2-Feb-2005.)
     (Proof shortened by Fan Zheng, 6-Jun-2016.) */

$)
${
	falrot4_0 $f wff ph $.
	falrot4_1 $f set x $.
	falrot4_2 $f set y $.
	falrot4_3 $f set z $.
	falrot4_4 $f set w $.
	alrot4 $p |- ( A. x A. y A. z A. w ph <-> A. z A. w A. x A. y ph ) $= falrot4_0 falrot4_4 wal falrot4_3 wal falrot4_2 wal falrot4_1 wal falrot4_0 falrot4_2 wal falrot4_4 wal falrot4_3 wal falrot4_1 wal falrot4_0 falrot4_2 wal falrot4_1 wal falrot4_4 wal falrot4_3 wal falrot4_0 falrot4_4 wal falrot4_3 wal falrot4_2 wal falrot4_0 falrot4_2 wal falrot4_4 wal falrot4_3 wal falrot4_1 falrot4_0 falrot4_2 falrot4_3 falrot4_4 alrot3 albii falrot4_0 falrot4_2 wal falrot4_1 falrot4_3 falrot4_4 alrot3 bitri $.
$}
$( /* Deduction form of bound-variable hypothesis builder ~ hbal .
       (Contributed by NM, 2-Jan-2002.) */

$)
${
	fhbald_0 $f wff ph $.
	fhbald_1 $f wff ps $.
	fhbald_2 $f set x $.
	fhbald_3 $f set y $.
	ehbald_0 $e |- ( ph -> A. y ph ) $.
	ehbald_1 $e |- ( ph -> ( ps -> A. x ps ) ) $.
	hbald $p |- ( ph -> ( A. y ps -> A. x A. y ps ) ) $= fhbald_0 fhbald_1 fhbald_3 wal fhbald_1 fhbald_2 wal fhbald_3 wal fhbald_1 fhbald_3 wal fhbald_2 wal fhbald_0 fhbald_1 fhbald_1 fhbald_2 wal fhbald_3 ehbald_0 ehbald_1 alimdh fhbald_1 fhbald_3 fhbald_2 ax-7 syl6 $.
$}

