OpenGEODE
=========

OpenGEODE is a tiny open-source SDL editor that is developed for
the purpose of providing an easy to use and free state machine editor and
Ada code generator to the TASTE toolchain from the European Space Agency,
running in combination with ESA's ASN.1 "Space Certifiable" ASN.1 compiler.

SDL is the Specification and Description Language (Z100 standard from ITU-T).

This is NOT related to the graphical Simple DirectMedia Layer libraries!

Visit http://sdl-forum.org for more information about SDL.
Visit http://www.pragmadev.com to get a full-featured commercial SDL tool and support


![alt tag](icons/opengeode-screenshot.png)


Features
--------

- Graphical editor of SDL processes and procedures.
- SDL2010 features: state composition and state aggregation
- Works on pure PR+CIF files (textual SDL notation)
- Supports ASN.1 data types - using ESA Space Certified compiler (www.github.com/ttsiodras/asn1scc)
- Generates Ada code
- Automatic conversion to Statechart diagrams
- Save the complete or parts of the model to PNG/SVG/PDF files
- Hyperlinks (link a symbol content to any external document or web page)
- Context-dependent text auto-completion
- Syntax highlighting
- Undo/Redo, Copy-Paste
- (Limited) VIM mode - You can use :wq or :%s,search,replace,g, and /search pattern
- Python API to parse and render SDL from other Python modules

Installation
============

On Windows, download the binary from [here](http://download.tuxfamily.org/taste/opengeode_windows.zip)

Uzip it and run opengeode.exe. It contains everything without any other external dependencies.

Linux Pre-requisites
--------------------

To install OpenGEODE on Linux you need to install some system-level dependencies:

- Python 2.7 with pip (installed by default on nearly all Linux distributions)
- Pyside
- Graphviz
- [ASN1SCC](https://github.com/ttsiodras/asn1scc)
- GNAT

And optionally llvm and llvmpy

On Debian, Ubuntu, and probably other distributions:

```bash
$ sudo apt install pkg-config python-pyside pyside-tools graphviz python-ply \
                       graphviz-dev libgraphviz-dev  python-pip gnat \
                       libmono-system-runtime4.0-cil libmono-corlib4.0-cil \
                       libmono-system-runtime-serialization-formatters-soap4.0-cil \
                       libmono-system-web4.0-cil libmono-system-xml4.0-cil \
                       libmono-system4.0-cil mono-runtime libmono-system-numerics4.0-cil \
                       libmono-system-data-linq4.0-cil libmono-corlib2.0-cil libmono-system2.0-cil
```

Some of these packages may be more recent on your distribution.

To install the ASN.1 compiler, run (possibly as root):

```bash
$ cd /opt
$ wget http://download.tuxfamily.org/taste/ASN1SCC/ASN1SCC-latest.tgz
$ tar zxvf ASN1SCC-latest.tgz
$ echo 'export PATH=$PATH:/opt/asn1scc' >> ~/.bashrc
```

Open a new terminal and check that it works:

```bash
$ mono /opt/asn1scc/asn1.exe
```

OpenGEODE installation
----------------------

Make sure all dependencies are installed.

If you see a certificate error while cloning from [Gitlab](https://gitrepos.estec.esa.int/taste/opengeode), you may need to run the following commands:

```bash
$ echo -n | openssl s_client -connect gitrepos.estec.esa.int:443 | sed -ne '/-BEGIN CERTIFICATE-/,/-END CERTIFICATE-/p' > gitrepos.cert
$ sudo cp gitrepos.cert /usr/local/share/ca-certificates/gitrepos.crt
$ sudo update-ca-certificates
```

There is no such issue if you use Github:


```bash
$ git clone --recursive https://github.com/esa/opengeode.git
```

And install it:

```bash
$ cd opengeode
$ make full-install
```


Information and contact
=======================

OpenGEODE is part of the [TASTE project](http://taste.tuxfamily.org)

For additional information please contact:
maxime (dot) perrotin (at) esa (dot) int


The LLVM backend was designed and implemented by Diego Barbera during the ESA
Summer of Code 2014 (It is unfortunately unmaintained now and does not support all features of the tool).
Some parts implemented by Laurent Meyer (native SDL type support in the parser)


The ASN.1 compiler (ASN1Scc) that OpenGEODE is based on was
developed by George Mamais and Thanassis Tsiodras for the European
Space Agency. Information at https://github.com/ttsiodras/asn1scc

Licence
=======

License is LGPL (see file LICENSE)
There is no runtime, and the generated code is not subject to any license.

The fonts are the fonts from Ubuntu, check licence in file FONT-LICENSE.TXT
The background pattern was downloaded from www.subtlepatterns.com

Changelog
=========

1.5.37 (05/2017)
    - Fix Ada backend bug with sequence of literals in nested states

1.5.36 (05/2017)
    - Fix Unicode issues in Ada backend

1.5.35 (05/2017)
    - Fix FOR LOOPS code generation

1.5.34 (05/2017)
    - Fix statechart message selection box

1.5.33 (04/2017)
    - Fix unicode issue with the simulation code
    - Use -fPIC when building the simulation library

1.5.32 (04/2017)
    - Unicode bugfixes in Ada backend
    - Bugfix with SEQUENCE OF literals in Ada backend
    - Various bugfixes with mixed int32/64 bits

1.5.28 (03/2017)
    - Added preliminary support for PROCESS TYPE and instances

1.5.26 (02/2017)
    - Statecharts can be configured to filter out signals

1.5.25 (01/2017)
    - Ada backend generates aliased context (used for model checking)

1.5.24 (01/2017)
    - PR file use better indentation for text areas (no line return)

1.5.23 (12/2016)
    - In simulation mode, bugfix in the declaration of the startup function
    - Code generator prepared for model checking

1.5.22 (12/2016)
    - Simulation function save/restore context fix

1.5.21 (11/2016)
    - Fix regression with test-math (import of external functions)
    - Use monospace font in the HTML rendering of ASN.1 files

1.5.20 (11/2016)
    - Fix wrongly formatted error reporting in FOR loops
    - Support SDL2010 dot field separator (variable.field,
      while sdl92 only supported variable!field)
    - Sequence of literals now support field selectors
      (i.e. { variable.field } is now a valid statement)
    - Support inner procedure call with return statement

1.5.19 (11/2016)
    - Fix integer cast in Ada

1.5.18 (11/2016)
    - Fix parsing of ASN.1 constants that use an annonymous inner type

1.5.17 (11/2016)
    - Fixed issue with initialization of generated code in state aggregations

1.5.16 (11/2016)
    - Fix minor indentation issue when saving

1.5.15 (10/2016)
    - Report incomplete startup transitions as errors in nested states

1.5.14 (10/2016)
    - Support named integers (requires asn1scc 3.3.04 or more recent)

1.5.13 (10/2016)
    - Better support of warnings
    - Fixed detection of CHOICE assignment erros
    - Raise error if process miss the start transition
    - Raise error in case of SEQUENCE OF type mismatch

1.5.12 (09/2016)
    - Detect duplicate declaration of procedures

1.5.11 (09/2016)
    - Allow semicolon in the declaration of procedures after RETURNS keyword

1.5.10 (09/2016)
    - readonly mode with more restrictions

1.5.9 (09/2016)
    - Added --readonly command line to restrict process modifications

1.5.8 (09/2016)
    - Bugfix - Ada backend failed when there were continuous signals in
               nested states but none at root level (missing end if)
    - Load fix when there is no dataview
    - Additional type checks

1.5.7 (09/2016)
    - Bugfix - Update completion list of process symbol
    - Sort ASN.1 types in data dictionary

1.5.6 (08/2016)
    - vi interface supports history
    - vi interface for substitution can apply to the whole model (with g)
    - refactoring function via vi interface (eg. %state,fromName,toName,)
    - Fixed issue with rendering (coordinates of symbols could be wrong)
    - Introduce data dictionary

1.5.4 (08/2016)
    - Various GUI improvements

1.5.3 (07/2016):
    - Ada backend fix: Continous signals now handled in states
      where input is not consumed

1.5.2 (07/2016):
    - Asn1scc API added to interface with DMT/asn2dataModel
    - Better statechart rendering (less distance between nodes)

1.4.5 (07/2016):
    - Context variable was not prefixed properly
    - Callback function for timers use 64bits integer
    - RIs use prefix with unicode separation to avoid name clashes


1.4.4 (06/2016)
    - Minor bugfix in Ada backend to support typeless systems

1.4.3 (06/2016)
    - Add support for priority of continuous signals in Ada code generator

1.4.2 (06/2016)
    - Reload / render properly priority of continuous signals

1.4.1 (06/2016)
    - Continuous states can check the presence of messages in the input queue
      to respect the SDL semantics
    - Bugfix in Ada code generator on continuous states

1.3.28 (06/2016)
    - Excluded states (with *(statelist) ) were case sensitive

1.3.27 (05/2016)
    - Fix bug in Ada backend when using continous signals
    - Better handling of simulation script

1.3.26 (05/2016)
    - Fix parser issues with negative expressions

1.3.25 (05/2016)
    - Fix reporting of syntax errors in state aggregations

1.3.22 (05/2016)
    - Bug fix in range checks for division and subtraction
    - Optimise loading when there are no CIF comments

1.3.21 (05/2016)
    - Complete support of optional fields
      (check tests/regression/test-optionalfields)

1.3.20 (05/2016)
    - Improve simulator interface

1.3.19 (04/2016)
    - Various bugfixes with ternary operator
    - Added demo "test-save" showing how to emulate the behaviour of the SAVE
      symbol
    - ASN.1 types are shown with SDL-syntax (no hyphens)

1.3.18 (04/2016)
    - Add support for value notation of NULL type
    - Remove warning when accessing CHOICE fields

1.3.17 (04/2016)
    - Add support for value notation of empty SEQUENCEs ("{}")

1.3.16 (03/2016)
    - Bugfix in testing aggregation states in the GUI

1.3.15 (03/2016)
    - Bugfix in Ada backend when a state aggregation contained only empty
      states (directly returning states).

1.3.14
    - Minor bugfix with command line handling

1.3.13
    - Bugfix in rendering of Continuous signals

1.3.12
    - Render properly parameterless procedures that are declared in the .pr
      file but without a textbox
    - When going to parent scene, fixed rendering issue

1.3.11
    - Parser is more tolerant to incomplete systems

1.3.9/10 (01/2016)
    - Checker verifies that decision coverage is complete on Real and Boolean
      types
    - F3 generates Ada code

1.3.8 (01/2016)
    - Fix logging when LLVM is not installed

1.3.7 (12/2015)
    - Added icon to use Continuous Signals from the GUI

1.3.6 (11/2015)
     - Support external procedures having a return statement
       this allows to import math functions from the libmath without having
       to provide manual code. see test-math

1.3.5 (11/2015)
     - Better support for continous signals

1.3.4 (11/2015)
     - Early support for continous signals
     - Regression issue fixed (test-nocif2)

1.3.3 (11/2015)
     - Better support of platform-dependent screen resolution and dpi
     - Minor fixes in statechart scenes (no negative coordinates)

1.3.1 (11/2015)
     - Support for State Aggregations (parallel states)
     - Improved statechart rendering

1.2.10 (10/2015)
     - Better support of renamePolicy
     - Better handling of models without CIF coordinates
     - Minor bug fixes
     - Forloop syntax error handled correctly when using range
     - support Hex and bit string literals when working with OCTET STRING
     - support OUT keyword for procedure FPAR

1.2.4 (07/2015)
     - Use version 3.2.x of the ASN1SCC compiler with new -renamePolicy flag
     - Improve robustness

1.1.1 (07/2015)
     - Strongly report syntax errors with symbol location and warning if user
       tries to save a model with syntax errors

1.1.0 (07/2015)
     - Write/Writeln procedure support enumerated types

1.0.1 (06/2015)
     - Bugfix: use mono when calling asn1.exe by default (needed redhat-based
                                                          distros)

1.0.0 (06/2015)
     - Bugfixes and minor improvements
     - Python API / Simulator function (coupled with other TASTE components)

1.0RC (10/2014)
     - Release candidate Version 1
     - Allow standalone systems (made of one process)
     - Major refactoring of parser and Ada backend
     - Many bugfixes and improvements
     - First version of LLVM backend

0.994 (07/2014)
     - Maintenance release, minor fixes

0.993 (07/2014)
     - Parser bugfixes
     - Better support for nested states
     - Ada generator improvements
     - Support for unicode
     - Indentation of PR code
     - Copy-paste of procedures and nested states
     - Improved regression testing

0.99 (04/2014)
     - Refactoring of the backend engine, now using singledispatch
     - Support of hierachical states
     - Minor bugfixes


0.98
     - Added support for FOR loops
       In a task, use "for x in range([start], stop, [range]): ... endfor"
       or "for x in sequenceOfvariable: ... endfor"
     - Default symbol size is smaller
     - Various minor bugfixes


0.97
     - added support for default value when declaring a variable
       e.g. DCL myVar myType ::= { x 5, y 2 };
       default value must be a ground expression

