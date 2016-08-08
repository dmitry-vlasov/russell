This package contains the metamath program and several Metamath-e 
databases.-e 
-e 
-e 
Copyright-e 
----------e 
-e 
The metamath program is copyright under the terms of the GNU GPL license-e 
version 2 or later.  See the file LICENSE.TXT in this directory.-e 
-e 
Individual databases (*.mm files) are either public domain or under-e 
the GNU GPL, as indicated by comments in their headers.-e 
-e 
See http://us.metamath.org/copyright.html for further license and-e 
copyright information that applies to the content of this package.-e 
-e 
-e 
Instructions-e 
-------------e 
-e 
For Windows, click on "metamath.exe" and type "read set.mm".-e 
-e 
For Unix/Linux/Cygwin/MacOSX using the gcc compiler, compile with the-e 
command "gcc m*.c -o metamath", then type "./metamath set.mm" to run.-e 
-e 
As an alternative, if you have autoconf, automake, and a C compiler, you-e 
can compile with the command "autoreconf -i && ./configure && make".-e 
This "autoconf" approach automatically finds your compiler and its-e 
options, and configure takes the usual options (e.g., "--prefix=/usr").-e 
The resulting executable will typically be faster because it will check for-e 
and enable available optimizations; tests found that the "improve"-e 
command ran 28% faster on gcc when using an autoconf-generated "configure".-e 
You can again type "./metamath set.mm" to run.  After "make" you may-e 
install it elsewhere using "sudo make install" (note that this installs-e 
".mm" files in the pkgdata directory, by default-e 
"/usr/local/share/metamath/").  If you install it this way, you can then-e 
run metamath as "metamath /usr/share/metamath/set.mm", copy set.mm-e 
locally (cp /usr/share/metamath/set.mm . ; metamath set.mm), or run-e 
metamath and type:  read "/usr/share/metamath/set.mm" (note that inside-e 
metamath, filenames containing "/" must be quoted).-e 
-e 
-e 
Optional enhancements-e 
----------------------e 
-e 
For optimized performance under gcc, you can compile as follows:-e 
-e 
  gcc m*.c -o metamath -O3 -funroll-loops -finline-functions \-e 
     -fomit-frame-pointer -Wall -pedantic-e 
-e 
If your compiler supports it, you can also add the option -DINLINE=inline-e 
to achieve the 28% performance increase described above.-e 
-e 
-e 
On Linux/MacOSX/Unix, the Metamath program will be more pleasant to use-e 
if you run it inside of rlwrap http://utopia.knoware.nl/~hlub/rlwrap/-e 
(checked 3-Jun-2015) which provides up-arrow command history and other-e 
command-line editing features.  After you install rlwrap per its-e 
instructions, invoke the Metamath program with "rlwrap ./metamath-e 
set.mm".-e 
-e 
-e 
In some Linux distributions (such as Debian Woody), if the Backspace-e 
key doesn't delete characters typed after the "MM>" prompt, try adding-e 
this line to your ~/.bash_profile file:-e 
-e 
  stty echoe echok echoctl echoke-e 
-e 
Using rlwrap as described above will also solve this problem.-e 
-e 
-e 
Additional MacOSX information-e 
------------------------------e 
-e 
On MacOSX, select the Terminal application from Applications/Utilities-e 
to get to the command line.  On recent versions of MacOSX, you need to-e 
install gcc separately.  Typing "whereis gcc" will return "/usr/bin/gcc"-e 
if it is installed.  The XCode package is typically used to install it,-e 
but it can also be installed without XCode; see-e 
-e 
  https://github.com/kennethreitz/osx-gcc-installer/ (checked 15-Feb-2014)-e 
-e 
-e 
Optional rlwrap user interface enhancement-e 
-------------------------------------------e 
-e 
On Linux/MacOSX/Unix, the Metamath program will be more pleasant to use-e 
if you run it inside of rlwrap:-e 
-e 
  http://utopia.knoware.nl/~hlub/uck/rlwrap/ (checked 15-Feb-2014)-e 
-e 
which provides up-arrow command history and other command-line editing-e 
features.  After you install rlwrap per its instructions, invoke the-e 
Metamath program with "rlwrap ./metamath set.mm".-e 
-e 
(The Windows version of the Metamath program was compiled with lcc,-e 
which has similar features built-in.)-e 
-e 
-e 
Windows Compilation-e 
--------------------e 
-e 
To reproduce the included metamath.exe for Windows, use lcc-win32-e 
version 3.8, with the following command:-e 
-e 
  lc -O m*.c -o metamath.exe-e 
-e 
-e 
Further suggestions-e 
--------------------e 
-e 
Once in the program, use the "help" command to guide you.  For more-e 
information, see the Metamath book available at http://metamath.org .-e 
-e 
-e 
To uninstall-e 
-------------e 
-e 
To uninstall, just delete the "metamath" directory - nothing else-e 
(Registry, etc.) is touched in your system.-e 
-e 
If you used autoconf's "make install" to install it in system locations,-e 
you can use "make uninstall" to remove it.-e 
-e 
-e 
List of databases-e 
------------------e 
-e 
The data base files included are:-e 
-e 
  set.mm - logic and set theory database (see Ch. 3 of the Metamath book).-e 
      The Metamath Proof Explorer pages were generated from this database.-e 
  nf.mm - logic and set theory database for Quine's New Foundations set-e 
      theory.-e 
  hol.mm - higher order logic (simple type theory) database.-e 
  iset.mm - intuitionistic logic database.-e 
  ql.mm - quantum logic database.  The Quantum Logic Explorer pages were-e 
      generated from this database.-e 
  demo0.mm - demo of simple formal system (see Ch. 2 of the Metamath book)-e 
  miu.mm - Hofstadter's MIU-system (see Appendix D of the Metamath book)-e 
  big-unifier.mm - A unification stress test (see comments in the file).-e 
  peano.mm - A nicely commented presentation of Peano arithmetic, written-e 
      by Robert Solovay (unlike the ones above, this database is NOT public-e 
      domain but is copyright under the terms of the GNU GPL license)-e 
