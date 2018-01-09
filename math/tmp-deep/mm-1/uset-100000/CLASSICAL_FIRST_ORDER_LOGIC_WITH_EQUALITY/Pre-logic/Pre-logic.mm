$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                           Pre-logic

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  This section includes a few "housekeeping" mechanisms before we begin
  defining the basics of logic.

$)
$( Declare the primitive constant symbols for propositional calculus. $)
$c (  $.
$( Left parenthesis $)
$c )  $.
$( Right parenthesis $)
$c ->  $.
$( Right arrow (read:  "implies") $)
$c -.  $.
$( Right handle (read:  "not") $)
$( Well-formed formula symbol (read:  "the following symbol
               sequence is a wff") $)
$( Turnstile (read:  "the following symbol sequence is provable" or
              'a proof exists for") $)
$( Define the syntax and logical typecodes, and declare that our grammar is
     unambiguous (verifiable using the KLR parser, with compositing depth 5).
     (This $ j comment need not be read by verifiers, but is useful for parsers
     like mmj2.) $)
$( $j
    syntax 'wff';
    syntax '|-' as 'wff';
    unambiguous 'klr 5';
  $)
$( wff variable sequence:  ph ps ch th ta et ze si rh mu la ka $)
$( Introduce some variable names we will use to represent well-formed
     formulas (wff's). $)
$( Greek phi $)
$( Greek psi $)
$( Greek chi $)
$( Greek theta $)
$( Greek tau $)
$( Greek eta $)
$( Greek zeta $)
$( Greek sigma $)
$( Greek rho $)
$( Greek mu $)
$( Greek lambda $)
$( Greek kappa $)
$( Specify some variables that we will use to represent wff's.
     The fact that a variable represents a wff is relevant only to a theorem
     referring to that variable, so we may use $f hypotheses.  The symbol
     ` wff ` specifies that the variable that follows it represents a wff. $)
$( Let variable ` ph ` be a wff. $)
$( Let variable ` ps ` be a wff. $)
$( Let variable ` ch ` be a wff. $)
$( Let variable ` th ` be a wff. $)
$( Let variable ` ta ` be a wff. $)
$( Let variable ` et ` be a wff. $)
$( Let variable ` ze ` be a wff. $)
$( Let variable ` si ` be a wff. $)
$( Let variable ` rh ` be a wff. $)
$( Let variable ` mu ` be a wff. $)
$( Let variable ` la ` be a wff. $)
$( Let variable ` ka ` be a wff. $)

