$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Tarski_s_system_S2_(1_rule,_6_schemes)/Universal_quantifier__define__exists__and__not_free_.mm $]
$( /* =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
       Rule scheme ax-gen (Generalization)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
*/

$)
$( /* Rule of Generalization.  The postulated inference rule of pure predicate
       calculus.  See e.g.  Rule 2 of [Hamilton] p. 74.  This rule says that if
       something is unconditionally true, then it is true for all values of a
       variable.  For example, if we have proved ` x = x ` , we can conclude
       ` A. x x = x ` or even ` A. y x = x ` .  Theorem ~ allt shows the
       special case ` A. x T. ` .  Theorem ~ spi shows we can go the other way
       also: in other words we can add or remove universal quantifiers from the
       beginning of any theorem as required.  (Contributed by NM,
       5-Aug-1993.) */

$)
${
	fax-gen_0 $f wff ph $.
	fax-gen_1 $f set x $.
	eax-gen_0 $e |- ph $.
	ax-gen $a |- A. x ph $.
$}
$( /* Generalization applied twice.  (Contributed by NM, 30-Apr-1998.) */

$)
$v y $.
${
	fgen2_0 $f wff ph $.
	fgen2_1 $f set x $.
	fgen2_2 $f set y $.
	egen2_0 $e |- ph $.
	gen2 $p |- A. x A. y ph $= fgen2_0 fgen2_2 wal fgen2_1 fgen2_0 fgen2_2 egen2_0 ax-gen ax-gen $.
$}
$( /* Modus ponens combined with generalization.  (Contributed by NM,
       24-May-1994.) */

$)
${
	fmpg_0 $f wff ph $.
	fmpg_1 $f wff ps $.
	fmpg_2 $f set x $.
	empg_0 $e |- ( A. x ph -> ps ) $.
	empg_1 $e |- ph $.
	mpg $p |- ps $= fmpg_0 fmpg_2 wal fmpg_1 fmpg_0 fmpg_2 empg_1 ax-gen empg_0 ax-mp $.
$}
$( /* Modus ponens on biconditional combined with generalization.
       (Contributed by NM, 24-May-1994.)  (Proof shortened by Stefan Allan,
       28-Oct-2008.) */

$)
${
	fmpgbi_0 $f wff ph $.
	fmpgbi_1 $f wff ps $.
	fmpgbi_2 $f set x $.
	empgbi_0 $e |- ( A. x ph <-> ps ) $.
	empgbi_1 $e |- ph $.
	mpgbi $p |- ps $= fmpgbi_0 fmpgbi_2 wal fmpgbi_1 fmpgbi_0 fmpgbi_2 empgbi_1 ax-gen empgbi_0 mpbi $.
$}
$( /* Modus ponens on biconditional combined with generalization.
       (Contributed by NM, 24-May-1994.)  (Proof shortened by Stefan Allan,
       28-Oct-2008.) */

$)
${
	fmpgbir_0 $f wff ph $.
	fmpgbir_1 $f wff ps $.
	fmpgbir_2 $f set x $.
	empgbir_0 $e |- ( ph <-> A. x ps ) $.
	empgbir_1 $e |- ps $.
	mpgbir $p |- ph $= fmpgbir_0 fmpgbir_1 fmpgbir_2 wal fmpgbir_1 fmpgbir_2 empgbir_1 ax-gen empgbir_0 mpbir $.
$}
$( /* Deduce that ` x ` is not free in ` ph ` from the definition.
       (Contributed by Mario Carneiro, 11-Aug-2016.) */

$)
${
	fnfi_0 $f wff ph $.
	fnfi_1 $f set x $.
	enfi_0 $e |- ( ph -> A. x ph ) $.
	nfi $p |- F/ x ph $= fnfi_0 fnfi_1 wnf fnfi_0 fnfi_0 fnfi_1 wal wi fnfi_1 fnfi_0 fnfi_1 df-nf enfi_0 mpgbir $.
$}
$( /* No variable is (effectively) free in a theorem.

       This and later "hypothesis-building" lemmas, with labels starting
       "hb...", allow us to construct proofs of formulas of the form
       ` |- ( ph -> A. x ph ) ` from smaller formulas of this form.  These are
       useful for constructing hypotheses that state " ` x ` is (effectively)
       not free in ` ph ` ."  (Contributed by NM, 5-Aug-1993.) */

$)
${
	fhbth_0 $f wff ph $.
	fhbth_1 $f set x $.
	ehbth_0 $e |- ph $.
	hbth $p |- ( ph -> A. x ph ) $= fhbth_0 fhbth_1 wal fhbth_0 fhbth_0 fhbth_1 ehbth_0 ax-gen a1i $.
$}
$( /* No variable is (effectively) free in a theorem.  (Contributed by Mario
       Carneiro, 11-Aug-2016.) */

$)
${
	fnfth_0 $f wff ph $.
	fnfth_1 $f set x $.
	enfth_0 $e |- ph $.
	nfth $p |- F/ x ph $= fnfth_0 fnfth_1 fnfth_0 fnfth_1 enfth_0 hbth nfi $.
$}
$( /* The true constant has no free variables.  (This can also be proven in one
     step with ~ nfv , but this proof does not use ~ ax-17 .)  (Contributed by
     Mario Carneiro, 6-Oct-2016.) */

$)
${
	fnftru_0 $f set x $.
	nftru $p |- F/ x T. $= wtru fnftru_0 tru nfth $.
$}
$( /* Generalization rule for negated wff.  (Contributed by NM,
       18-May-1994.) */

$)
${
	fnex_0 $f wff ph $.
	fnex_1 $f set x $.
	enex_0 $e |- -. ph $.
	nex $p |- -. E. x ph $= fnex_0 wn fnex_0 fnex_1 wex wn fnex_1 fnex_0 fnex_1 alnex enex_0 mpgbi $.
$}
$( /* No variable is (effectively) free in a non-theorem.  (Contributed by
       Mario Carneiro, 6-Dec-2016.) */

$)
${
	fnfnth_0 $f wff ph $.
	fnfnth_1 $f set x $.
	enfnth_0 $e |- -. ph $.
	nfnth $p |- F/ x ph $= fnfnth_0 fnfnth_1 fnfnth_0 fnfnth_0 fnfnth_1 wal enfnth_0 pm2.21i nfi $.
$}

