/*****************************************************************************/
/*        Copyright (C) 2015  NORMAN MEGILL  nm at alum.mit.edu              */
/*            License terms:  GNU General Public License                     */
/*****************************************************************************/
/*34567890123456 (79-character line to adjust editor window) 2345678901234567*/

/* Part 1 of help file for Metamath */
/* To add a new help entry, you must add the command syntax to mmcmdl.c
   as well as adding it here. */

#include <string.h>
#include <stdio.h>
#include "mmvstr.h"
#include "mmdata.h"
#include "mmcmds.h"
#include "mmhlpa.h"

/* help0 is for toolsMode */
void help0(vstring helpCmd)
{

/* 5-Sep-2012 nm */
vstring saveHelpCmd = "";
/* help0() may be called with a temporarily allocated argument (left(),
   cat(), etc.), and the let()s in the eventual print2() calls will
   deallocate and possibly corrupt helpCmd.  So, we grab a non-temporarily
   allocated copy here.  (And after this let(), helpCmd will become invalid
   for the same reason.)  */
let(&saveHelpCmd, helpCmd);

printHelp = !strcmp(saveHelpCmd, "HELP");
H("This utility assists with some common file manipulations.");
H("Most commands will perform an identical operation on each line of a file.");
H("Use HELP ? to see list of help topics.");
H("Note:  When an output file is created, any previous version is renamed,");
H(
 "with ~1 appended, and any ~1 renamed to ~2, etc. (up to ~9, which is lost).");
H("Note:  All string-matching command arguments are case-sensitive.");
H("");
H("Line-by-line editing commands:");
H("  ADD - Add a specified string to each line in a file");
H("  CLEAN - Trim spaces and tabs on each line in a file; convert characters");
H("  DELETE - Delete a section of each line in a file");
H("  INSERT - Insert a string at a specified column in each line of a file");
H("  SUBSTITUTE - Make a simple substitution on each line of the file");
H("  TAG - Like ADD, but restricted to a range of lines");
/*H("  LSUBSTITUTE - Substitute according to a match-and-substitute list");*/
H("  SWAP - Swap the two halves of each line in a file");
H("Other file processing commands:");
H("  BREAK - Break up (parse) a file into a list of tokens (one per line)");
H("  BUILD - Build a file with multiple tokens per line from a list");
H("  COUNT - Count the occurrences in a file of a specified string");
/*H("  FORMAT - Produce a formatted list of tokens for documentation");*/
H("  NUMBER - Create a list of numbers");
H("  PARALLEL - Put two files in parallel");
H("  REVERSE - Reverse the order of the lines in a file");
H("  RIGHT - Right-justify lines in a file (useful before sorting numbers)");
H("  SORT - Sort the lines in a file with key starting at specified string");
H("  MATCH - Extract lines containing (or not) a specified string");
/*H("  LEXTRACT - Extract lines containing (or not) strings from a list");*/
H("  UNDUPLICATE - Eliminate duplicate occurrences of lines in a file");
H("  DUPLICATE - Extract first occurrence of any line occurring more than");
H("      once in a file, discarding lines occurring exactly once");
H("  UNIQUE - Extract lines occurring exactly once in a file");
H("  UPDATE - Update a C program for revision control");
H(
"  (UNDUPLICATE, DUPLICATE, and UNIQUE also sort the lines as a side effect.)");
H("  TYPE (10 lines) - Display 10 lines of a file; similar to Unix \"head\"");
/*H("  COPY, RENAME - Similar to Unix cat, mv but with backups created");*/
H(
"  COPY - Similar to Unix \"cat\" but safe (same input & output name allowed)");
H("  SUBMIT - Run a script containing Tools commands.");
H("");
if (listMode) {
H("Command syntax ([] means optional):");
H("  From TOOLS prompt:  Tools> <command> [<arg1> <arg2>...]");
H("  From VMS shell:  $ DO TOOLS [<command>] [<arg1> <arg2>...]");
H("  From Unix/DOS shell:  tools [<command>] [<arg1> <arg2>...]");
H("You need to type only as many characters of the command as are needed to");
H("uniquely specify it.  Any arguments will answer questions automatically");
H("until the argument list is exhausted; the remaining questions will be");
H("prompted.  An argument may be optionally enclosed in quotes.  Use \"\" for");
H("default or null argument.  [Note:  VMS does not allow single quotes (')");
H("around DCL arguments; use double quotes (\").  Single quotes are OK in");
H("immediate mode.] [Note: Quotes MUST be put around Unix pathname arguments");
H("with a \"/\" in them, except they may be omitted in direct response to");
H("an argument prompt.]");
H("");
H("Notes:");
H("(1) The commands are not case sensitive.  File names and match strings");
H("are case sensitive.");
H("(2) Output files are created only after a command finishes running.");
H("Therefore it is usually safe to hit ^C before a command is completed.");
H("(3) The file \"zztools.tmp\", which is always created, can be used as a");
H("command file to re-run the command sequence with the SUBMIT command.");
H("(4) Previous versions of output files (except under VMS) are renamed with");
H("~1 (most recent), ~2,...,~9 (oldest) appended to file name.  Purge them");
H("periodically.");
H("(5) The command B(EEP) will make the terminal beep.  It can be useful to");
H("type it ahead to let you know when the current command is finished.");
H("(6) It is suggested you use a \".tmp\" file extension for intermediate");
H("results to eliminate directory clutter.");
H("");
H("Please see NDM if you have any suggestions for this program.");
} /* if listMode */


printHelp = !strcmp(saveHelpCmd, "HELP ADD");
H("This command adds a character string prefix and/or suffix to each");
H("line in a file.");
H("Syntax:  ADD <iofile> <begstr> <endstr>");

/* 2-Jul-2011 nm Added TAG command */
printHelp = !strcmp(saveHelpCmd, "HELP TAG");
H("TAG is the same as ADD but has 4 additional arguments that let you");
H("specify a range of lines.  Syntax:");
H("  TAG <iofile> <begstr> <endstr> <startmatch> <s#> <endmatch> <e#>");
H("where");
H("  <iofile> = input/output file");
H("  <begstr> = string to add to beginning of each line");
H("  <endstr> = string to add to end of each line");
H("  <startmatch> = a string to match; if empty, match any line");
H("  <s#> = the 1st, 2nd, etc. occurrence of <startmatch> to start the range");
H("  <endmatch> = a string to match; if empty, match any line");
H("  <e#> = the 1st, 2nd, etc. occurrence of <endmatch> from the");
H("      start of range line (inclusive) after which to end the range");
H("Example:  To add \"!\" to the end of lines 51 through 60 inclusive:");
H("  TAG \"a.txt\" \"\" \"!\" \"\" 51 \"\" 10");
H("Example:  To add \"@@@\" to the beginning of each line in theorem");
H("\"abc\" through the end of its proof:");
H("  TAG \"set.mm\" \"@@@\" \"\" \"abc $p\" 1 \"$.\" 1");
H("so that later, SUBSTITUTE can be used to affect only those lines.  You");
H("can remove the \"@@@\" tags with SUBSTITUTE when done.");

printHelp = !strcmp(saveHelpCmd, "HELP DELETE");
H("This command deletes the part of a line between (and including)");
H("two specified strings for all lines in a file.");
H("Syntax:  DELETE <iofile> <startstr> <endstr>");

printHelp = !strcmp(saveHelpCmd, "HELP CLEAN");
H("This command processes spaces and tabs in each line of a file");
H("according to the following subcommands:");
H("  D - Delete all spaces and tabs");
H("  B - Delete spaces and tabs at the beginning of each line");
H("  E - Delete spaces and tabs at the end of each line");
H("  R - Reduce multiple spaces and tabs to one space");
H("  Q - Do not alter characters in quotes (ignored by T and U)");
H("  T - (Tab) Convert spaces to equivalent tabs");
H("  U - (Untab) Convert tabs to equivalent spaces");
H("Some other subcommands are also available:");
H("  P - Trim parity (8th) bit from each character");
H("  G - Discard garbage characters CR,FF,ESC,BS");
H("  C - Convert to upper case");
H("  L - Convert to lower case");
H("  V - Convert VT220 screen print frame graphics to -,|,+ characters");
H("Subcommands may be joined with commas (but no spaces), e.g., \"B,E,R,Q\"");
H("Syntax:  CLEAN <iofile> <subcmd,subcmd,...>");

printHelp = !strcmp(saveHelpCmd, "HELP SUBSTITUTE")
    || !strcmp(helpCmd, "HELP S");
H("This command performs a simple string substitution in each line of a file.");
H("If the string to be replaced is \"\\n\", then every other line will");
H("be joined to the one below it.  If the replacement string is \"\\n\", then");
H("each line will be split into two if there is a match.");
H("The <matchstr> specifies a string that must also exist on a line");
H("before the substitution takes place; null means match any line.");
H("Syntax:  SUBSTITUTE <iofile> <oldstr> <newstr> <occurrence> <matchstr>");
H("Note: The SUBSTITUTE command may be abbreviated by S.");

printHelp = !strcmp(saveHelpCmd, "HELP SWAP");
H("This command swaps the parts of each line before and after a");
H("specified string.");


printHelp = !strcmp(saveHelpCmd, "HELP INSERT");
H("This command inserts a string at a specifed column in each line");
H("in a file.  It is intended to aid further processing of column-");
H("sensitive files.");
H("Syntax:  INSERT <iofile> <string> <column>");


printHelp = !strcmp(saveHelpCmd, "HELP BREAK");
H("This command breaks up a file into tokens, one per line, breaking at");
H("whitespace and any special characters you specify as delimiters.");
H("Syntax:  BREAK <iofile> <specchars>");

printHelp = !strcmp(saveHelpCmd, "HELP BUILD");
H("This command combines a list of tokens into multiple tokens per line,");
H("as many as will fit per line, separating them with spaces.");
H("Syntax:  BUILD <iofile>");


printHelp = !strcmp(saveHelpCmd, "HELP MATCH");
H("This command extracts from a file those lines containing (Y) or not");
H("containing (N) a specified string.");
H("Syntax:  MATCH <iofile> <matchstr> <Y/N>");


printHelp = !strcmp(saveHelpCmd, "HELP SORT");
H("This command sorts a file, comparing lines starting at a key string.");
H("If the key string is blank, the line is compared starting at column 1.");
H("If a line doesn't contain the key, it is compared starting at column 1.");
H("Syntax:  SORT <iofile> <key>");


printHelp = !strcmp(saveHelpCmd, "HELP UNDUPLICATE");
H("This command sorts a file then removes any duplicate lines from the output.");
H("Syntax:  UNDUPLICATE <iofile>");


printHelp = !strcmp(saveHelpCmd, "HELP DUPLICATE");
H("This command finds all duplicate lines in a file and places them, in");
H("sorted order, into the output file.");
H("Syntax:  DUPLICATE <iofile>");


printHelp = !strcmp(saveHelpCmd, "HELP UNIQUE");
H("This command finds all unique lines in a file and places them, in");
H("sorted order, into the output file.");
H("Syntax:  UNIQUE <iofile>");


printHelp = !strcmp(saveHelpCmd, "HELP REVERSE");
H("This command reverses the order of the lines in a file.");
H("Syntax:  REVERSE <iofile>");


printHelp = !strcmp(saveHelpCmd, "HELP RIGHT");
H("This command right-justifies the lines in a file by putting spaces in");
H("front of them so that they end in the same column as the longest line");
H("in the file.");
H("Syntax:  RIGHT <iofile>");


printHelp = !strcmp(saveHelpCmd, "HELP PARALLEL");
H("This command puts two files side-by-side.");
H("The two files should have the same number of lines; if not, a warning is");
H("issued and the longer file paralleled with empty strings at the end.");
H("Syntax:  PARALLEL <inpfile1> <inpfile2> <outfile> <btwnstr>");


printHelp = !strcmp(saveHelpCmd, "HELP NUMBER");
H("This command creates a list of numbers.  Hint:  Use the RIGHT command to");
H("right-justify the list after creating it.");
H("Syntax:  NUMBER <outfile> <first> <last> <incr>");


printHelp = !strcmp(saveHelpCmd, "HELP COUNT");
H("This command counts the occurrences of a string in a file and displays");
H("some other statistics about the file.  The sum of the lines is obtained");
H("by extracting digits and is only valid if the file consists of genuine");
H("numbers.");
H("Syntax:  COUNT <inpfile> <string>");


printHelp = !strcmp(saveHelpCmd, "HELP TYPE") || !strcmp(helpCmd, "HELP T");
H("This command displays (i.e. types out) the first n lines of a file on the");
H("terminal screen.  If n is not specified, it will default to 10.  If n is");
H("the string \"ALL\", then the whole file will be typed.");
H("Syntax:  TYPE <inpfile> <n>");
H("Note: The TYPE command may be abbreviated by T.");


printHelp = !strcmp(saveHelpCmd, "HELP COPY") || !strcmp(helpCmd, "HELP C");
H("This command copies (concatenates) all input files in a comma-separated");
H("list (no blanks allowed) to an output file.  The output file may have");
H("the same name as an input file.  Any previous version of the output");
H("file is renamed with a ~1 extension.");
H("Example: \"COPY 1.tmp,1.tmp,2.tmp 1.tmp\" followed by \"UNIQUE 1.tmp\"");
H("will result in 1.tmp containing those lines of 2.tmp that didn't");
H("previously exist in 1.tmp.");
H("Syntax:  COPY <inpfile,inpfile,...> <outfile>");
H("Note: The COPY command may be abbreviated by C.");

printHelp = !strcmp(saveHelpCmd, "HELP UPDATE");
H("This command tags edits made to a program source.  The idea is to keep");
H("all past history of a file in the file itself, in the form of comments.");
H("UPDATE was written for a proprietary language that allowed nested C-style");
H("comments, and it may not be generally useful without some modification.");
H("Essentially a (Unix) diff-like algorithm looks for changes between an");
H("original and a revised file and puts the original lines into the revised");
H("file in the form of comments.  Currently it is not well documented and it");
H("may be easiest just to type UPDATE <return> and answer the questions.");
H("Try it on an original and edited version of a test file to see if you");
H("find it useful.");
H("Syntax:  UPDATE <originfile> <editedinfile> <editedoutfile> <tag> <match>");

printHelp = !strcmp(saveHelpCmd, "HELP CLI");
H("Each command line is an English-like word followed by arguments separated");
H("by spaces, as in SUBMIT abc.cmd.  Commands are not case sensitive, and");
H("only as many letters are needed as are necessary to eliminate ambiguity;");
H("for example, \"a\" would work for the command ADD.  Command arguments");
H("which are file names and match strings are case-sensitive (although file");
H("names may not be on some operating systems).");
H("");
H("A command line is entered typing it in then pressing the <return> key.");
H("");
H("To find out what commands are available, type ? at the \"TOOLS>\" prompt.");
H("");
H("To find out the choices at any point in a command, press <return> and you");
H("will be prompted for them.  The default choice (the one selected if you");
H("just press <return>) is shown in brackets (<>).");
H("");
H("You may also type ? in place of a command word to tell");
H("you what the choices are.  The ? method won't work, though, if a");
H("non-keyword argument such as a file name is expected at that point,");
H("because the CLI will think the ? is the argument.");
H("");
H("Some commands have one or more optional qualifiers which modify the");
H("behavior of the command.  Qualifiers are indicated by a slash (/), such as");
H("in ABC xyz / IJK.  Spaces are optional around the /.  If you need");
H("to use a slash in a command argument, as in a Unix file name, put single");
H("or double quotes around the command argument.");
H("");
H("If the response to a command is more than a screenful, you will be");
H("prompted to \"<return> to continue, Q to quit, or S to scroll to end\".");
H("Q will complete the command internally but suppress further output until");
H("the next \"TOOLS>\" prompt.  S will suppress further pausing until the next");
H("\"TOOLS>\" prompt.");
H("");
H("A command line enclosed in quotes is executed by your operating system.");
H("See HELP SYSTEM.");
H("");
H("Some other commands you may want to review with HELP are:");
H("    SUBMIT");
H("");

printHelp = !strcmp(saveHelpCmd, "HELP SUBMIT");
H("Syntax:  SUBMIT <filename> [/ SILENT]");
H("");
H("This command causes further command lines to be taken from the specified");
H("file.  Note that any line beginning with an exclamation point (!) is");
H("treated as a comment (i.e. ignored).  Also note that the scrolling");
H("of the screen output is continuous.");
H("");
H("Optional qualifier:");
H("    / SILENT - This qualifier suppresses the screen output of the SUBMIT");
H("        command.");
H("");
H("SUBMIT can be called recursively, i.e., SUBMIT commands are allowed");
H("inside of a command file.");


printHelp = !strcmp(saveHelpCmd, "HELP SYSTEM");
H("A line enclosed in single or double quotes will be executed by your");
H("computer's operating system, if it has such a feature.  For example, on a");
H("Unix system,");
H("    Tools> 'ls | more'");
H("will list disk directory contents.  Note that this feature will not work");
H("on the pre-OSX Macintosh, which does not have a command line interface.");
H("");
H("For your convenience, the trailing quote is optional, for example:");
H("    Tools> 'ls | more");
H("");

let(&saveHelpCmd, ""); /* Deallocate memory */

return;
} /* help0 */


/* Note: help1 should contain Metamath help */
void help1(vstring helpCmd)
{

/* 5-Sep-2012 nm */
vstring saveHelpCmd = "";
/* help1() may be called with a temporarily allocated argument (left(),
   cat(), etc.), and the let()s in the eventual print2() calls will
   deallocate and possibly corrupt helpCmd.  So, we grab a non-temporarily
   allocated copy here.  (And after this let(), helpCmd will become invalid
   for the same reason.)  */
let(&saveHelpCmd, helpCmd);


printHelp = !strcmp(saveHelpCmd, "HELP CLI");
H("The Metamath program was first developed on a VAX/VMS system, and some");
H("aspects of its command line behavior reflect this heritage.  Hopefully");
H(
"you will find it reasonably user-friendly once you get used to it.");
H("");
H("Each command line is a sequence of English-like words separated by");
H("spaces, as in SHOW SETTINGS.  Command words are not case sensitive, and");
H("only as many letters are needed as are necessary to eliminate ambiguity;");
H("for example, \"sh se\" would work for the command SHOW SETTINGS.  In some");
H("cases arguments such as file names, statement labels, or symbol names are");
H("required; these are case-sensitive (although file names may not be on");
H("some operating systems).");
H("");
H("A command line is entered by typing it in then pressing the <return> key.");
H("");
H("To find out what commands are available, type ? at the MM> prompt,");
H("followed by <return>. (This is actually just a trick to force an error");
H("message, since ? is not a legal command.)");
H("");
H("To find out the choices at any point in a command, press <return> and you");
H("will be prompted for them.  The default choice (the one selected if you");
H("just press <return>) is shown in brackets (<>).");
H("");
H("You may also type ? in place of a command word to force Metamath to tell");
H("you what the choices are.  The ? method won't work, though, if a");
H("non-keyword argument such as a file name is expected at that point,");
H("because the CLI will think the ? is the argument.");
H("");
H("Some commands have one or more optional qualifiers that modify the");
H("behavior of the command.  Qualifiers are indicated by a slash (/), such as");
H("in READ set.mm / VERIFY.  Spaces are optional around / and =.  If you need");
H("to use / or = in a command argument, as in a Unix file name, put single");
H("or double quotes around the command argument.  See the last section of");
H("HELP LET for more information on special characters in arguments.");
H("");
H("The OPEN LOG command will save everything you see on the screen, and is");
H("useful to help you recover should something go wrong in a proof, or if");
H("you want to document a bug.");
H("");
H("If the response to a command is more than a screenful, you will be");
H("prompted to '<return> to continue, Q to quit, or S to scroll to end'.");
H("Q will complete the command internally but suppress further output until");
H("the next \"MM>\" prompt.  S will suppress further pausing until the next");
H("\"MM>\" prompt.  After the first screen, you can also choose B to go back");
H("a screenful.  Note that B may also be entered at the \"MM>\" prompt");
H("immediately after a command to scroll back through the output of that");
H("command.  Scrolling can be disabled with SET SCROLL CONTINUOUS.");
H("");
H("**Warning**  Pressing CTRL-C will abort the Metamath program");
H("unconditionally.  This means any unsaved work will be lost.");
H("");
H("A command line enclosed in quotes is executed by your operating system.");
H("See HELP SYSTEM.");
H("");
H("Some additional CLI-related features are explained by:");
H("    HELP SET ECHO");
H("    HELP SET SCROLL");
H("    HELP SET WIDTH");  /* 18-Nov-05 nm Was SCREEN_WIDTH */
H("    HELP SET HEIGHT"); /* 18-Nov-05 nm New */
H("    HELP SUBMIT");
H("");



printHelp = !strcmp(saveHelpCmd, "HELP LANGUAGE");
H("The language is best learned by reading the book and studying a few proofs");
H("with the Metamath program.  This is a brief summary for reference.");
H("");
H("The database contains a series of tokens separated by whitespace (spaces,");
H("tabs, returns).  A token is a keyword, a <label>, or a <symbol>.");
H("");
H("The pure language keywords are:  $c $v $a $p $e $f $d ${ $} $. and $=");
H("The auxiliary keywords are:  $( $) $[ and $]");
H("This is the complete set of language keywords.");
H("");
H("<symbol>s and <label>s are user-defined.  <symbol>s may contain any");
H("printable characters other than $ , and <label>s may contain alphanumeric");
H("characters, periods, dashes and underscores.");
H("");
H("Scoping statements:");
H("");
H("  ${ - Start of scope.");
H("       Syntax:  \"${\"");
H("");
H("  $} - End of scope:  all $v, $e, $f, and $d statements in the current");
H("         scope become inactive.");
H("       Syntax:  \"$}\"");
H("");
H("  Note that $a and $p statements remain active forever.  Note that $c's");
H("  may be used only in the outermost scope, so they are always active.");
H("  The outermost scope is not bracketed by ${ ... $} .  The scope of a $v,");
H("  $e, $f, or $d statement starts where the statement occurs and ends with");
H("  the $} that matches the previous ${.  The scope of a $c, $a, or $p");
H("  statement starts where the statement occurs and ends at the end of the");
H("  database.");
H("");
H("Declarations:");
H("");
H("  $c - Constant declaration.  The <symbol>s become active constants.");
H("       Syntax:  \"$c <symbol> ... <symbol> $.\"");
H("");
H("  $v - Variable declaration.  The <symbols>s become active variables.");
H("       Syntax:  \"$v <symbol> ... <symbol> $.\"");
H("");
H("Hypotheses:");
H("");
H("  $f - Variable-type (or \"floating\") hypothesis (meaning it is");
H("         \"required\" by a $p or $a statement in its scope only if its");
H("         variable occurs in the $p or $a statement or in the essential");
H("         hypotheses of the $p or $a statement).  Every $d, $e, $p, and $a");
H("         statement variable must have an earlier active $f statement to");
H("         specify the variable type.  Non-required i.e. \"optional\" $f");
H("         statements may be referenced inside a proof when dummy variables");
H("         are needed by the proof.");
H("       Syntax:  \"<label> $f <constant> <variable> $.\" where both symbols");
H("         are active");
H("");
H("  $e - Logical (or \"essential\") hypothesis (meaning it is always");
H("         required by a $p or $a statement in its scope)");
H("       Syntax:  \"<label> $e <symbol> ... <symbol> $.\"  where the first");
H("         (and possibly only) <symbol> is a constant");
H("");
H("Assertions:");
H("");
H("  $a - Axiomatic assertion (starting assertion; used for axioms,");
H("         definitions, and language syntax specification)");
H("       Syntax:  \"<label> $a <symbol> ... <symbol> $.\"  where the first");
H("         (and possibly only) <symbol> is a constant");
H("");
H("  $p - Provable assertion (derived assertion; used for deductions and");
H("         theorems; must follow from previous statements as demonstrated by");
H("         its proof)");
H("       Syntax:");
H("         \"<label> $p <symbol> ... <symbol> $= <label> ... <label> $.\"");
H("         where the first (and possibly only) <symbol> is a constant.");
H("         \"$= <label> ... <label> $.\" is the proof; see the book for more");
H("         information.  Proofs may be compressed for storage efficiency.  A");
H("         compressed proof is a series of labels in parentheses followed by");
H("         a string of capital letters; see book for compression algorithm.");
H("         SAVE PROOF <label> / NORMAL will convert a compressed proof to");
H("         its uncompressed form.");
H("");
H("  A substitution is the replacement of a variable with a <symbol> string");
H("  throughout an assertion and its required hypotheses.  The required");
H("  hypotheses are shown as the \"mandatory hypotheses\" listed by");
H("  SHOW STATEMENT <label> / FULL.");
H("");
H("  In a proof, the label of a hypothesis ($e or $f) pushes the stack, and");
H("  the label of an assertion ($a or $p) pops from the stack a number of");
H("  entries equal to the number of the assertion's required hypotheses and");
H("  replaces the stack's top.  Whenever an assertion is specified, a unique");
H("  set of substitutions must exist that makes the assertion's hypotheses");
H("  match the top entries of the stack.");
H("");
H("  To see a readable proof format, type SHOW PROOF <label>, where <label>");
H("  is the label of a $p statement.  To see how substitutions are made in a");
H("  proof step, type SHOW PROOF <label> / DETAILED_STEP <n>, where <n> is");
H("  the step number from the SHOW PROOF <label> listing.");
H("");
H("Disjoint variable restriction:");
H("");
H("  The substitution of symbol strings into variables may be subject to a");
H("  $d restriction:");
H("");
H("  $d - Disjoint variable restriction (meaning substititutions may not");
H("         share variables in common)");
H("       Syntax:  \"$d <symbol> ... <symbol> $.\" where <symbol> is active");
H("         and previously declared with $v, and all <symbol>s are distinct");
H("");
H("Auxiliary keywords:");
H("");
H("  $(   Begin comment");
H("  $)   End comment");
H("       Inside of comments:");
H("         ` <symbol> ` - use graphical <symbol> in LaTeX/HTML output;");
H("             `` means literal `; several <symbol>s may occur inside");
H("             ` ... ` separated by whitespace");
H("         ~ <label> - use typewriter font (hyperlink) in LaTeX (HTML) output;");
H("             if <label> begins with \"http://\", it is assumed to be");
H("             a URL (which is used as-is, except a \"~\" in the URL should");
H("             be specified as \"~~\") rather than a statement label (which");
H("             will have \".html\" appended for the hyperlink); only $a and $p");
H("             statement labels may be used, since $e, $f pages don't exist");
H("         [<author>] - link to bibliography; see HELP HTML and HELP WRITE");
H("             BIBLIOGRAPHY");
H("         $t - flags comment as containing LaTeX and/or HTML typesetting");
H("             definitions; see HELP LATEX or HELP HTML");
H("         _ - Italicize text from <space>_<non-space> to");
H("             <non-space>_<space>; normal punctuation (e.g. trailing");
H("             comma) is ignored when determining <space>");
H("         _ - <non-space>_<non-space-string> will make <non-space-string>");
H("             a subscript");
H("       Note:  Comments may not be nested.");
H("");
H("  $[ <file-name> $] - place contents of file <file-name> here; a second,");
H("       recursive, or self reference to a file is ignored");
H("");


printHelp = !strcmp(saveHelpCmd, "HELP EXPLORE");
H("When you first enter Metamath, you will first want to READ in a Metamath");
H("source file.  The source file provided for set theory is called set.mm;");
H("to read it type");
H("    READ set.mm");
H("");
H("You may want to look over the contents of the source file with a text");
H("editor, to get an idea of what's in it, before starting to use Metamath.");
H("");
H("The following commands will help you study the source file statements");
H("and their proofs.  Use the HELP for the individual commands to get");
H("more information about them.");
H("    SEARCH <label-match> \"<symbol-match>\" - Displays statements whose");
H("        labels match <label-match> and that contain <symbol-match>.");
H("    SEARCH <label-match> \"<search-string>\" / COMMENTS - Shows statements");
H("        whose preceding comment contains <search-string>");
H("    SHOW LABELS <label-match> - Lists all labels matching <label-match>,");
H("        with * and ? wildcards:  for example \"abc?def*\" will match all");
H("        labels beginning with \"abc\" followed by any single character");
H("        followed by \"def\".");
H("    SHOW STATEMENT <label> / COMMENT - Shows the comment, contents, and");
H("        logical hypotheses associated with a statement.");
H("    SHOW PROOF <label> - Shows the proof of a $p statement in various");
H("        formats, depending on what qualifiers you select.  One of the");
H("        qualifiers, / TEX, lets you create LaTeX source for the proof.");
H("        The / DETAILED_STEP qualifier is useful while you're learning how");
H("        Metamath unifies the sources and targets of a step.  The");
H("        / STATEMENT_SUMMARY qualifier gives you a quick summary of all");
H("        the statements referenced in the proof.");
H("    SHOW TRACE_BACK <label> - Traces a proof back to axioms, depending");
H("        on various qualifiers you select.");
H("    SHOW USAGE <label> - Shows what later proofs make use of this");
H("        statement.");
H("");


printHelp = !strcmp(saveHelpCmd, "HELP PROOF_ASSISTANT");
H("Before using the Proof Assistant, you must add a $p to your source file");
H("(using a text editor) containing the statement you want to prove.  Its");
H("proof should consist of a single ?, meaning \"unknown step.\"  Example:");
H("    eqid $p x = x $= ? $.");
H("");
H("To enter the Proof Assistant, type PROVE <label>, e.g. PROVE eqid.");
H("Metamath will respond with the MM-PA> prompt.");
H("");
H("Proofs are created working backwards from the statement being proved,");
H("primarily using a series of ASSIGN commands.  A proof is complete when");
H("all steps are assigned to statements and all steps are unified and");
H("completely known.  During the creation of a proof, Metamath will allow");
H("only operations that are legal based on what is known up to that point.");
H("For example, it will not allow an ASSIGN of a statement that cannot be");
H("unified with the unknown proof step being assigned.");
H("");
H("IMPORTANT:  You should figure out your first few proofs completely and");
H("write them down by hand, before using the Proof Assistant.  Otherwise you");
H("will become extremely frustrated.  The Proof Assistant is NOT a tool to");
H("help you discover proofs.  It is just a tool to help you add them to the");
H("database.  For a tutorial read Section 2.4 of the Metamath book.  To");
H("practice using the Proof Assistant, you may want to PROVE an existing");
H("theorem, then delete all steps with DELETE ALL, then re-create it with");
H("the Proof Assistant while looking at its proof display (before deletion).");
H("");
H("The commands available to help you create a proof are the following.");
H("See the help for the individual commands for more detail.");
H("    SHOW NEW_PROOF [/ ALL,...] - Displays the proof in progress.");
H("        You will use this command a lot; see HELP SHOW NEW_PROOF to");
H("        become familiar with its qualifiers.  The qualifiers / UNKNOWN");
H("        and / NOT_UNIFIED are useful for seeing the work remaining to be");
H("        done.  The combination / ALL / UNKNOWN is useful identifying");
H("        dummy variables that must be assigned, or attempts to use illegal");
H("        syntax, when IMPROVE ALL is unable to complete the syntax");
H("        constructions.  Unknown variables are shown as $1, $2,...");
H("    ASSIGN <step> <label> - Assigns an unknown step with the statement");
H("        specified by <label>.  This will normally be your most frequently");
H("        used command for creating proofs.  The usual proof entry process");
H("        consists of successively ASSIGNing labels to unknown steps shown");
H("        by SHOW NEW_PROOF / UNKNOWN.");
H("    LET VARIABLE <variable> = \"<symbol sequence>\" - Forces a symbol");
H("        sequence to replace an unknown variable in a proof.  It is useful");
H("        for helping difficult unifications, and is necessary when you");
H("        have dummy variables that must be specified.");
H("    LET STEP <step> = \"<symbol sequence>\" - Forces a symbol sequence");
H("        to replace the contents of a proof step, provided it can be");
H("        unified with the existing step contents.  (Rarely useful.)");
H("    UNIFY STEP <step> (or UNIFY ALL) - Unifies the source and target of");
H("        a step.  If you specify a specific step, you will be prompted");
H("        to select among the unifications that are possible.  If you");
H("        specify ALL, only those steps with unique unifications will be");
H("        unified.  UNIFY ALL / INTERACTIVE goes through all non-unified");
H("        steps.");
H("    INITIALIZE <step> (or ALL) - De-unifies the target and source of");
H("        a step (or all steps), as well as the hypotheses of the source,");
H("        and makes all variables in the source unknown.  Useful after");
H("        an ASSIGN or LET mistake resulted in incorrect unifications.");
H("    DELETE <step> (or ALL or FLOATING_HYPOTHESES) - Deletes the specified");
H("        step(s).  DELETE FLOATING_HYPOTHESES then INITIALIZE ALL then");
H("        UNIFY ALL / INTERACTIVE is useful for recovering from mistakes");
H("        where incorrect unifications assigned wrong math symbol strings to");
H("        variables.");
H("    IMPROVE <step> (or ALL) - Automatically creates a proof for steps");
H("        (with no unknown variables) whose proof requires no statements");
H("        with $e hypotheses.  Useful for filling in proofs of $f");
H("        hypotheses.  The / DEPTH qualifier will also try statements");
H("        whose $e hypotheses contain no new variables.  WARNING: Save your");
H("        work (SAVE NEW_PROOF, WRITE SOURCE) before using / DEPTH = 2 or");
H("        greater, since the search time grows exponentially and may never");
H("        terminate in a reasonable time, and you cannot interrupt the");
H("        search.  I have rarely found / DEPTH = 3 or greater to be useful.");
H("    SAVE NEW_PROOF - Saves the proof in progress internally in the");
H("        database buffer.  To save it permanently, use WRITE SOURCE after");
H("        SAVE NEW_PROOF.  To revert to the last SAVE NEW_PROOF,");
H("        EXIT / FORCE from the Proof Assistant then re-enter the Proof");
H("        Assistant.");
H("    SHOW NEW_PROOF / COMPRESSED - Displays the proof in progress on the");
H("        screen in a format that can be copied and pasted into the");
H("        database source, as an alternative to a SAVE NEW_PROOF.");
H("    MATCH STEP <step> (or MATCH ALL) - Shows what statements are");
H("        possibilities for the ASSIGN statement. (This command is not very");
H("        useful in its present form and hopefully will be improved");
H("        eventually.  In the meantime, use the SEARCH statement for");
H("        candidates matching specific math token combinations.)");
H("    MINIMIZE_WITH - After a proof is complete, this command will attempt");
H("        to match other database theorems to the proof to see if the proof");
H("        size can be reduced as a result.");
H("    UNDO - Undo the effect of a proof-changing command (all but the SHOW");
H("        and SAVE commands above).");
H("    REDO - Reverse the previous UNDO.");
H("");
H("The following commands set parameters that may be relevant to your proof:");
H("    SET UNIFICATION_TIMEOUT");
H("    SET SEARCH_LIMIT");
H("    SET EMPTY_SUBSTITUTION - note that default is OFF (contrary to book)");
H("");
H("Type EXIT to exit the MM-PA> prompt and get back to the MM> prompt.");
H("Another EXIT will then get you out of Metamath.");
H("");

printHelp = !strcmp(saveHelpCmd, "HELP UNDO");
H("Syntax:  UNDO");
H("");
H("This command, available in the Proof Assistant only, allows any command");
H("(such as ASSIGN, DELETE, IMPROVE) that affects the proof to be reversed.");
H("See also HELP REDO and HELP SET UNDO.");
H("");


printHelp = !strcmp(saveHelpCmd, "HELP REDO");
H("Syntax:  REDO");
H("");
H("This command, available in the Proof Assistant only, reverses the");
H("effect of the last UNDO command.  Note that REDO can be issued only");
H("if no proof-changing commands (such as ASSIGN, DELETE, IMPROVE)");
H("were issued after the last UNDO.  A sequence of REDOs will reverse as");
H("many UNDOs as were issued since the last proof-changing command.");
H("");


printHelp = !strcmp(saveHelpCmd, "HELP SET UNDO"); /* 1-Nov-2013 nm */
H("Syntax:  SET UNDO <number>");
H("");
H("(This command affects the Proof Assistant only.)");
H("");
H("This command changes the maximum number of UNDOs.  The current maximum");
H("can be seen with SHOW SETTINGS.  Making it larger uses more memory,");
H("especially for large proofs.  See also HELP UNDO.");
H("");
H("If this command is issued while inside of the Proof Assistant, the");
H("UNDO stack is reset (i.e. previous possible UNDOs will be lost).");
H("");



printHelp = !strcmp(saveHelpCmd, "HELP HTML");
H("To create an HTML output file for a $a or $p statement, use");
H("    SHOW STATEMENT <label> / HTML");
H("The created web page will include a Description taken from the comment");
H("that immediately precedes the $a or $p statement.  A warning will be");
H("issued if this comment is not present.  Optional markup in the comment");
H("will be processed according to the markup syntax described under HELP");
H("LANGUAGE, in the \"Inside of comments\" section.  Warnings will be");
H("issued for any errors in the markup.  Note that all other comments in");
H("the database are ignored, including comments preceding $e statements.");
H("");
H("When <label> has wildcard (* and ?) characters, all statements with");
H("matching labels will have HTML files produced for them.  Also, when");
H("<label> starts with a * wildcard character, three additional files,");
H("mmdefinitions.html, mmtheoremsall.html, and mmascii.html will be");
H("produced.  Thus:");
H("    SHOW STATEMENT * / HTML");
H("will output the complete HTML proof database in the current directory,");
H("one file per $a and $p statement, along with mmdefinitions.html,");
H("mmtheoremsall.html, and mmascii.html.  The statement:");
H("    SHOW STATEMENT *! / HTML");
H("will produce only mmdefinitions.html, mmmmtheoremsall.html, and");
H("mmascii.html, but no other HTML files (because no labels can match \"*!\"");
H("since \"!\" is illegal in a statement label).  The statement:");
H("    SHOW STATEMENT ?* / HTML");
H("will output the complete HTML proof database but will not produce");
H("mmdefinitions.html, etc.  Note added 30-Jan-06:  The mmtheoremsall.html");
H("file produced by this command is deprecated and is replaced by the output");
H("of WRITE THEOREM_LIST.");
H("");
H("The HTML definitions for the symbols and and other features are");
H("specified by statements in a special typesetting comment in the input");
H("database file.  The typesetting comment is identified by the token \"$t\"");
H("in the comment, and the typesetting statements run until the next \"$)\":");
H("   ...  $( ...  $t ................................ $) ...");
H("                   <-- HTML definitions go here -->");
H("See the set.mm database file for an extensive example of a $t comment");
H("illustrating all features described below.  In the HTML definition");
H("section, C-style comments /* ... */ are recognized.  The main HTML");
H("specification statements are:");
H("    htmldef \"<mathtoken>\" as \"<HTML code for mathtoken symbol>\" ;");
H("                    ...");
H("    htmldef \"<mathtoken>\" as \"<HTML code for mathtoken symbol>\" ;");
H("    htmltitle \"<HTML code for title>\" ;");
H("    htmlhome \"<HTML code for home link>\" ;");
H("    htmlvarcolors \"<HTML code for variable color list>\" ;");
H("    htmlbibliography \"<HTML file>\" ;");
H("        (This <HTML file> is assumed to have a <A NAME=...> tag for each");
H("        bibiographic reference in the database comments.  For example");
H("        if \"[Monk]\" occurs in a comment, then \"<A NAME='Monk'>\" must");
H("        be present in the <HTML file>; if not, a warning message is");
H("        given.)");
H("Single or double quotes surround the field strings, and fields too long");
H("for a line may be broken up into multiple quoted strings connected with");
H("(whitespace-surrounded) \"+\" signs (no quotes around them).  Inside");
H("quoted strings, the opposite kind of quote may appear.  If both kinds of");
H("quotes are needed, use separate quoted strings connected by \"+\".");
H("Note that the \"$)\" character sequence will flag the end of the");
H("typesetting Metamath comment even if embedded in quotes (which are not");
H("meaningful for the Metamath language parser), so such a sequence must be");
H("broken with \"+\".");
H("");
H("The typesetting Metamath comment may also contain LaTeX definitions");
H("(with \"latexdef\" statements) that are ignored for HTML output.");
H("");
H("Several other qualifiers exist.  The command");
H("    SHOW STATEMENT <label> / ALT_HTML");
H("does the same as SHOW STATEMENT <label> / HTML, except that the HTML code");
H("for the symbols is taken from \"althtmldef\" statements instead of");
H("\"htmldef\" statements in the $(...$t...$) comment.  This is useful when");
H("an alternate representation of symbols is desired, for example one that");
H("uses Unicode entities instead of GIF images.  Associated with althtmldef");
H("are the statements");
H("    htmldir \"<directory for GIF HTML version>\" ;");
H("    althtmldir \"<directory for Unicode HTML version>\" ;");
H("that produce links to the alternate version.");
H("");
H("The command");
H("    SHOW STATEMENT * / BRIEF_HTML");
H("invokes a special mode that just produces definition and theorem lists");
H("accompanied by their symbol strings, in a format suitable for copying and");
H("pasting into another web page.");
H("");
H("Finally, the command");
H("    SHOW STATEMENT * / BRIEF_ALT_HTML");
H("does the same as SHOW STATEMENT * / BRIEF_HTML for the alternate HTML");
H("symbol representation.");
H("");
H("When two different types of pages need to be produced from a single");
H("database, such as the Hilbert Space Explorer that extends the Metamath");
H("Proof Explorer, \"extended\" variables may be declared in the $t comment:");
H("    exthtmltitle \"<HTML code for title>\" ;");
H("    exthtmlhome \"<HTML code for home link>\" ;");
H("    exthtmlbibliography \"<HTML file>\" ;");
H("When these are declared, you also must declare");
H("    exthtmllabel \"<label>\" ;");
H("When the output statement is the one declared with \"exthtmllabel\" or");
H("a later one, the HTML code assigned to \"exthtmltitle\" and");
H("\"exthtmlhome\" is used instead of that assigned to \"htmltitle\" and");
H("\"htmlhome\" respectively.");
H("");

printHelp = !strcmp(saveHelpCmd, "HELP LATEX");
H("See HELP TEX.");
H("");

printHelp = !strcmp(saveHelpCmd, "HELP TEX");
H("Metamath will create a \"turn-key\" LaTeX source file which can be");
H("immediately compiled and printed using a TeX program.  The TeX program");
H("must have the following minimum requirements:  the LaTeX style option and");
H("the AMS font set, available from the American Mathematical Society.");
H("");
H("To write out a statement and its proof, use a command sequence similar");
H("to the following example:");
H("    (Enter Metamath)");
H("    READ set.mm");
H("    OPEN TEX example.tex");
H("    SHOW STATEMENT uneq2 / TEX");
H("    SHOW PROOF uneq2 / LEMMON / RENUMBER / TEX");
H("    CLOSE TEX");
H("");
H("The LaTeX symbol definitions should be included in a special comment");
H("containing a $t token.  See the set.mm file for an example.");
H("");


printHelp = !strcmp(saveHelpCmd, "HELP BEEP") || !strcmp(helpCmd, "HELP B");
H("Syntax:  BEEP");
H("");
H("This command will produce a beep.  By typing it ahead after a long-");
H("running command has started, it will alert you that the command is");
H("finished. B is an abbreviation for BEEP.");
H("");
H("Note: If B is typed at the MM> prompt immediately after the end of a");
H("multiple-page display paged with \"Press <return> for more...\" prompts,");
H("then the B will back up to the previous page rather than perform the BEEP");
H("command.");
H("");


printHelp = !strcmp(saveHelpCmd, "HELP QUIT");
H("Syntax:  QUIT [/ FORCE]");
H("");
H("This command is a synonym for EXIT.  See HELP EXIT.");
H("");


printHelp = !strcmp(saveHelpCmd, "HELP EXIT");
H("Syntax:  EXIT [/ FORCE]");
H("");
H("This command exits from Metamath.  If there have been changes to the");
H("database with the SAVE PROOF or SAVE NEW_PROOF commands, you will be given");
H("an opportunity to WRITE SOURCE to permanently save the changes.");
H("");
H("(In Proof Assistant mode) The EXIT command will return to the MM> prompt.");
H("If there were changes to the proof, you will be given an opportunity to");
H("SAVE NEW_PROOF.  In the Proof Assistant, _EXIT_PA is a synonym for EXIT");
H("that gives an error message outside of the Proof Assistant.  This can be");
H("useful to prevent scripts from exiting Metamath due to an error entering");
H("the Proof Assistant.");
H("");
H("The QUIT command is a synonym for EXIT.");
H("");
H("Optional qualifier:");
H("    / FORCE - Do not prompt if changes were not saved.  This qualifier is");
H("        useful in SUBMIT command files (scripts) to ensure predictable");
H("        behavior.");
H("");
H("**Warning**  Pressing CTRL-C will abort the Metamath program");
H("unconditionally.  This means any unsaved work will be lost.");
H("");


printHelp = !strcmp(saveHelpCmd, "HELP READ");
H("Syntax:  READ <file> [/ VERIFY]");
H("");
H("This command will read in a Metamath language source file and any included");
H("files.  Normally it will be the first thing you do when entering Metamath.");
H("Statement syntax is checked, but proof syntax is not checked.");
H("Note that the file name may be enclosed in single or double quotes;");
H("this is useful if the file name contains slashes, as might be the case");
H("under Unix.");
H("");
H("If you are getting an \"?Expected VERIFY or NOVERIFY\" error when trying");
H("to read a Unix file name with slashes, you probably haven't quoted it.");
H("");
H("You need nested quotes when a Unix file name with slashes is a Metamath");
H("invocation argument.  See HELP INVOKE for examples.");
H("");
H("If you are prompted for the file name (by pressing <return> after READ)");
H("you should _not_ put quotes around it, even if it is a Unix file name.");
H("with slashes.");
H("");
H("Optional qualifier:");
H("    / VERIFY - Verify all proofs as the database is read in.  This");
H("        qualifier will slow down reading in the file.");
H("");
H("See also HELP ERASE.");
H("");


printHelp = !strcmp(saveHelpCmd, "HELP ERASE");
H("Syntax:  ERASE");
H("");
H("This command will reset Metamath to its starting state, deleting any");
H("database that was READ in.");
H("");


printHelp = !strcmp(saveHelpCmd, "HELP OPEN LOG");
H("Syntax:  OPEN LOG <file>");
H("");
H("This command will open a log file that will store everything you see on");
H("the screen.  It is useful to help recovery from a mistake in a long Proof");
H("Assistant session, or to document bugs.");
H("");
H("The screen output of operating system commands (HELP SYSTEM) is not");
H("logged.");
H("");
H("The log file can be closed with CLOSE LOG.  It will automatically be");
H("closed upon exiting Metamath.");
H("");


printHelp = !strcmp(saveHelpCmd, "HELP CLOSE LOG");
H("Syntax:  CLOSE LOG");
H("");
H("The CLOSE LOG command closes a log file if one is open.  See also OPEN");
H("LOG.");
H("");


printHelp = !strcmp(saveHelpCmd, "HELP OPEN TEX");
H("Syntax:  OPEN TEX <file>");
H("");
H("This command opens a file for writing LaTeX source and writes a LaTeX");
H("header to the file.  LaTeX source can be written with the SHOW PROOF,");
H("SHOW NEW_PROOF, and SHOW STATEMENT commands using the / TEX qualifier.");
H("The mapping to LaTeX symbols is defined in a special comment containing");
H("a $t token.  See the set.mm database file for an example.");
H("");
H("To format and print the LaTeX source, you will need the TeX program,");
H("which is standard in most Linux, Unix, and MacOSX installations and");
H("available for Windows.");
H("");
H("Optional qualifier:");
H("    / NO_HEADER - This qualifier prevents a standard LaTeX header and");
H("        trailer from being included with the output LaTeX code.");
H("Optional qualifier:");
H("    / OLD_TEX - This qualifier produces a header with macro definitions");
H("        for use with / OLD_TEX qualifiers of SHOW STATEMENT and SHOW");
H("        PROOF.  It is obsolete and will be removed eventually.");
H("");
H("See also CLOSE TEX.");
H("");


printHelp = !strcmp(saveHelpCmd, "HELP CLOSE TEX");
H("Syntax:  CLOSE TEX");
H("");
H("This command writes a trailer to any LaTeX file that was opened with OPEN");
H("TEX (unless / NO_HEADER was used with OPEN) and closes the LaTeX file.");
H("");
H("See also OPEN TEX.");
H("");


printHelp = !strcmp(saveHelpCmd, "HELP TOOLS");
H("Syntax:  TOOLS");
H("");
H("This command invokes a utility to manipulate ASCII text files.  Type TOOLS");
H("to enter this utility, which has its own HELP commands.  Once inside you");
H("are inside, EXIT will return to Metamath.");
H("");

let(&saveHelpCmd, ""); /* Deallocate memory */
return;

} /* help1 */
