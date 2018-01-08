$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Other_axiomatizations_of_classical_propositional_calculus.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    Universal quantifier; define "exists" and "not free"

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( Declare new symbols needed for pure predicate calculus. $)
$c A.  $.
$( "inverted A" universal quantifier (read:  "for all") $)
$c set  $.
$( Individual variable type (read:  "the following is an
             individual (set) variable" $)
$( Add 'set' as a typecode. $)
$( $j syntax 'set'; $)
$( Declare some names for individual variables. $)
$( Let ` x ` be an individual variable. $)
$( Let ` y ` be an individual variable. $)
$( Let ` z ` be an individual variable. $)
$( Let ` w ` be an individual variable. $)
$( Let ` v ` be an individual variable. $)
$( Let ` u ` be an individual variable. $)
$( Let ` t ` be an individual variable. $)
$( Extend wff definition to include the universal quantifier ('for all').
     ` A. x ph ` is read " ` ph ` (phi) is true for all ` x ` ."  Typically, in
     its final application ` ph ` would be replaced with a wff containing a
     (free) occurrence of the variable ` x ` , for example ` x = y ` .  In a
     universe with a finite number of objects, "for all" is equivalent to a big
     conjunction (AND) with one wff for each possible case of ` x ` .  When the
     universe is infinite (as with set theory), such a propositional-calculus
     equivalent is not possible because an infinitely long formula has no
     meaning, but conceptually the idea is the same. $)
$v x $.
${
	fwal_0 $f wff ph $.
	fwal_1 $f set x $.
	wal $a wff A. x ph $.
$}
$( Register 'A.' as a primitive expression (lacking a definition). $)
$( $j primitive 'wal'; $)
$( Declare the existential quantifier symbol. $)
$c E.  $.
$( Backwards E (read:  "there exists") $)
$( Extend wff definition to include the existential quantifier ("there
     exists"). $)
${
	fwex_0 $f wff ph $.
	fwex_1 $f set x $.
	wex $a wff E. x ph $.
$}
$( Define existential quantification. ` E. x ph ` means "there exists at
     least one set ` x ` such that ` ph ` is true."  Definition of [Margaris]
     p. 49.  (Contributed by NM, 5-Aug-1993.) $)
${
	fdf-ex_0 $f wff ph $.
	fdf-ex_1 $f set x $.
	df-ex $a |- ( E. x ph <-> -. A. x -. ph ) $.
$}
$( Theorem 19.7 of [Margaris] p. 89.  (Contributed by NM, 5-Aug-1993.) $)
${
	falnex_0 $f wff ph $.
	falnex_1 $f set x $.
	alnex $p |- ( A. x -. ph <-> -. E. x ph ) $= falnex_0 falnex_1 wex falnex_0 wn falnex_1 wal falnex_0 falnex_1 df-ex con2bii $.
$}
$c F/  $.
$( The not-free symbol. $)
$( Extend wff definition to include the not-free predicate. $)
${
	fwnf_0 $f wff ph $.
	fwnf_1 $f set x $.
	wnf $a wff F/ x ph $.
$}
$( Define the not-free predicate for wffs.  This is read " ` x ` is not free
     in ` ph ` ".  Not-free means that the value of ` x ` cannot affect the
     value of ` ph ` , e.g., any occurrence of ` x ` in ` ph ` is effectively
     bound by a "for all" or something that expands to one (such as "there
     exists").  In particular, substitution for a variable not free in a wff
     does not affect its value ( ~ sbf ).  An example of where this is used is
     ~ stdpc5 .  See ~ nf2 for an alternative definition which does not involve
     nested quantifiers on the same variable.

     Not-free is a commonly used constraint, so it is useful to have a notation
     for it.  Surprisingly, there is no common formal notation for it, so here
     we devise one.  Our definition lets us work with the not-free notion
     within the logic itself rather than as a metalogical side condition.

     To be precise, our definition really means "effectively not free," because
     it is slightly less restrictive than the usual textbook definition for
     not-free (which only considers syntactic freedom).  For example, ` x ` is
     effectively not free in the bare expression ` x = x ` (see ~ nfequid ),
     even though ` x ` would be considered free in the usual textbook
     definition, because the value of ` x ` in the expression ` x = x ` cannot
     affect the truth of the expression (and thus substitution will not change
     the result).

     This predicate only applies to wffs.  See ~ df-nfc for a not-free
     predicate for class variables.  (Contributed by Mario Carneiro,
     11-Aug-2016.) $)
${
	fdf-nf_0 $f wff ph $.
	fdf-nf_1 $f set x $.
	df-nf $a |- ( F/ x ph <-> A. x ( ph -> A. x ph ) ) $.
$}

