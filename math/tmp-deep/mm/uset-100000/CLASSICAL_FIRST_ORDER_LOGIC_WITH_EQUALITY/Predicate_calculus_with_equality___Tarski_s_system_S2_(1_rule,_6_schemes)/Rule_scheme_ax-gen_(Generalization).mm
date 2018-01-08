
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Tarski_s_system_S2_(1_rule,_6_schemes)/Universal_quantifier__define__exists__and__not_free_.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
       Rule scheme ax-gen (Generalization)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    ax-g.1 $e |- ph $.
    $( Rule of Generalization.  The postulated inference rule of pure predicate
       calculus.  See e.g.  Rule 2 of [Hamilton] p. 74.  This rule says that if
       something is unconditionally true, then it is true for all values of a
       variable.  For example, if we have proved ` x = x ` , we can conclude
       ` A. x x = x ` or even ` A. y x = x ` .  Theorem ~ allt shows the
       special case ` A. x T. ` .  Theorem ~ spi shows we can go the other way
       also: in other words we can add or remove universal quantifiers from the
       beginning of any theorem as required.  (Contributed by NM,
       5-Aug-1993.) $)
    ax-gen $a |- A. x ph $.
  $}

  ${
    gen2.1 $e |- ph $.
    $( Generalization applied twice.  (Contributed by NM, 30-Apr-1998.) $)
    gen2 $p |- A. x A. y ph $=
      wph vy wal vx wph vy gen2.1 ax-gen ax-gen $.
  $}

  ${
    mpg.1 $e |- ( A. x ph -> ps ) $.
    mpg.2 $e |- ph $.
    $( Modus ponens combined with generalization.  (Contributed by NM,
       24-May-1994.) $)
    mpg $p |- ps $=
      wph vx wal wps wph vx mpg.2 ax-gen mpg.1 ax-mp $.
  $}

  ${
    mpgbi.1 $e |- ( A. x ph <-> ps ) $.
    mpgbi.2 $e |- ph $.
    $( Modus ponens on biconditional combined with generalization.
       (Contributed by NM, 24-May-1994.)  (Proof shortened by Stefan Allan,
       28-Oct-2008.) $)
    mpgbi $p |- ps $=
      wph vx wal wps wph vx mpgbi.2 ax-gen mpgbi.1 mpbi $.
  $}

  ${
    mpgbir.1 $e |- ( ph <-> A. x ps ) $.
    mpgbir.2 $e |- ps $.
    $( Modus ponens on biconditional combined with generalization.
       (Contributed by NM, 24-May-1994.)  (Proof shortened by Stefan Allan,
       28-Oct-2008.) $)
    mpgbir $p |- ph $=
      wph wps vx wal wps vx mpgbir.2 ax-gen mpgbir.1 mpbir $.
  $}

  ${
    nfi.1 $e |- ( ph -> A. x ph ) $.
    $( Deduce that ` x ` is not free in ` ph ` from the definition.
       (Contributed by Mario Carneiro, 11-Aug-2016.) $)
    nfi $p |- F/ x ph $=
      wph vx wnf wph wph vx wal wi vx wph vx df-nf nfi.1 mpgbir $.
  $}

  ${
    hbth.1 $e |- ph $.
    $( No variable is (effectively) free in a theorem.

       This and later "hypothesis-building" lemmas, with labels starting
       "hb...", allow us to construct proofs of formulas of the form
       ` |- ( ph -> A. x ph ) ` from smaller formulas of this form.  These are
       useful for constructing hypotheses that state " ` x ` is (effectively)
       not free in ` ph ` ."  (Contributed by NM, 5-Aug-1993.) $)
    hbth $p |- ( ph -> A. x ph ) $=
      wph vx wal wph wph vx hbth.1 ax-gen a1i $.

    $( No variable is (effectively) free in a theorem.  (Contributed by Mario
       Carneiro, 11-Aug-2016.) $)
    nfth $p |- F/ x ph $=
      wph vx wph vx hbth.1 hbth nfi $.
  $}

  $( The true constant has no free variables.  (This can also be proven in one
     step with ~ nfv , but this proof does not use ~ ax-17 .)  (Contributed by
     Mario Carneiro, 6-Oct-2016.) $)
  nftru $p |- F/ x T. $=
    wtru vx tru nfth $.

  ${
    nex.1 $e |- -. ph $.
    $( Generalization rule for negated wff.  (Contributed by NM,
       18-May-1994.) $)
    nex $p |- -. E. x ph $=
      wph wn wph vx wex wn vx wph vx alnex nex.1 mpgbi $.
  $}

  ${
    nfnth.1 $e |- -. ph $.
    $( No variable is (effectively) free in a non-theorem.  (Contributed by
       Mario Carneiro, 6-Dec-2016.) $)
    nfnth $p |- F/ x ph $=
      wph vx wph wph vx wal nfnth.1 pm2.21i nfi $.
  $}


