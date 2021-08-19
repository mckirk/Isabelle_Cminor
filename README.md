### Overview

This project is the product of my Master's thesis at the chair for Logic and Verification at TU Munich.
Its goal was to connect the verified C-compiler [CompCert](https://compcert.org/) (which is written in Coq) to the Isabelle ecosystem, in order to make it possible for future Isabelle/HOL projects to benefit from CompCert's verified-compilation stack.

In order to accomplish this, I ported the formalization for Cminor (one of CompCert's intermediate languages) to Isabelle/HOL.
To make it possible to extract programs from Isabelle and compile them in CompCert, I added code to enable exporting of Cminor code in JSON and patched CompCert so it could interpret the encoded programs.
Additionally, I set up a separation logic reasoning infrastructure for Cminor, based on Peter Lammich's work on [Isabelle LLVM](https://github.com/lammich/isabelle_llvm).
As a case study, I defined a basic Cminor program in Isabelle/HOL, proved its correctness, exported it to JSON, and compiled it using CompCert.

### Theories

- The Cminor formalization and the theories it depends on can be found in `theory/compcert`:
    - `Cminor`
        - Contains the formalization of both the small-step and the big-step semantics of Cminor and a proof of their consistency, as is done in CompCert
        - Also contains a deterministic "step_fun" for use in testing the small-step semantics, which works because all non-deterministic parts of Cminor are not yet formalized (i.e. the missing external functions)
        - In general, care was taken to not use the so-far-still-given determinism of statements to prove anything in the Separation Logic, however

- The reasoning infrastructure is mainly located in `theory/src/Sep_Logic` (which admittedly could be split into smaller files) and depends on a number of helper theories:
    - `Basic_Lens`:

        Provides a "very well-behaved" lens (in the terminology of the [Optics library](https://www.isa-afp.org/browser_info/current/AFP/Optics/document.pdf)) library that directly interoperates with the sep. logic library.
        The main motivation behind this library was to make it easy to relate a concrete state and its abstract separation-algebra representation, by defining two lenses for the respective forms of the state and proving their "equivalence" under the abstraction function (`α`).

        I.e.: You have a concrete memory view and an abstract one, and you define lenses that (given a pointer) focus on the same address in memory. If you can prove that the two lenses correspond to each other (in the sense of: `put`ing a concrete value means a `get` in the abstract will yield the sep.-algebra representation of the value, etc), then you get many of the properties you need to set up a separation logic "for free".

    - `TSA_Map_α`:

        Helper library that defines an separation-algebra version of a `Map` (and a corresponding abstraction-function `α`), using Lammich's `tsa_opt` type:
        
        `m x = Some v` corresponds to `(α m) x = TRIV v` and `m x = None` corresponds to `(α m) x = ZERO`.

        The `tsa_opt` type is used here instead of the `option` type because the `option` type instantiates the separation algebra class differently:
        Where `tsa_opt` is a trivial embedding of arbitrary values (`TRIV v` is disjoint only with `ZERO`), `option` embeds another sep.-algebra type (`Some v` is disjoint with `Some v'` iff `v` is disjoint with `v'`).

    - `State_Ops`:

        To instantiate Lammich's separation logic library, you need _weakest precondition_ (`wp`) predicates for the operations you want to model.
        The `State_Ops` theory defines a general-purpose `wp` predicate for operations that modify any kind of (concrete) state.

- On top of this separation logic, there's an alternative view on Cminor's memory in `theory/src/Chunkvals`.
    Cminor by itself sees memory byte-wise, which is not the most convenient way to talk about memory in assertions.
    A `chunkval` on the other hand directly contains a number of bytes (1, 2, 4, or 8) as a machine-word and makes it easier to talk about values in memory, so long as their granularity doesn't change (i.e., casts between byte-sizes still require extra care).
- Using this `chunkval` view, `theory/src/Chunkval_Interface` defines an array primitive with corresponding pseudo-instructions for allocation, access and deallocation.

- Finally, the case study can be found in `theory/src/Case_Study`.
    - Defines the case-study program, proves its correctness and exports it in JSON format
    - There is one variant of the case study that only uses Cminor's base instructions, and one variant that uses the `chunkval` array interface, which is also the one that gets exported at the moment.
    - The `fix` lemmas circumvent a currently-still-persisting problem with the Cminor formalization:
        Cminor provides (in theory) two different ways to call an external function (such as `malloc`/`free`).
        One can either use the `Sbuiltin` instruction to call it directly, or define it in the global environment first and call it using `Scall`.
        As the `Sbuiltin` path seemed a lot simpler, I chose to formalize it first -- but had to find out that Cminor does not, in fact, allow calling arbitrary external functions using `Sbuiltin` and instead expects the `Scall` approach for library functions such as `malloc`/`free`.
        For this reason, the `fix` lemmas serve as a crude patch just before the export to Cminor.
        Note that they are horribly hacky and essentially break the proving environment; but that is fine so long as nothing gets proven after they are defined.
    - This theory exports the `array_case_study.cmj` file that can be compiled with the patched CompCert

### General Notes
- The theories are built for Isabelle2021
- They depend on the following AFP libraries:
    - Show
    - Word_Lib (which in turn depends on the Word library from HOL-Library)
    - IEEE_Floating_Point
    - Separation_Algebra
    - more through Lammich's lib (at least Automatic_Refinement and Refine_Imperative_HOL)

### Known Issues/Limitations
- At the moment, the reasoning infrastructure does not support function calls, as the local-variable environment is modeled as a single, static environment instead of a stack.
- The `Sbuiltin`/`Scall` problem mentioned above: `malloc` and `free` should be invoked as external functions using `Scall` instead of through the `Sbuiltin` instruction
- Not all of Cminor's features are formalized; many external functions, which would introduce non-determinism into the semantics, are still missing for example (only `malloc`, `free` and `memcpy` are implemented so far)
- In the sep. logic, memory can't be shared at the moment; a memory location is always fully owned by any code that wants to access it

- So far, there is no guarantee that the Cminor formalization here is equivalent to the one used by CompCert.
    It is not unlikely that this is the case, because the translation was largely done using the Python scripts found in `scripts`, but there might very well be errors introduced by manual fine-tuning of the produced code.
    Ideally, there would be various tests that compared execution-traces resulting from the two semantics to ensure their interpretation of code is the same.

### Directory Structure

- ./theory: Isabelle Theories
    - src: My additions
        - Sep_Generic_Wp: Also part of Lammich's library, but modified (`wp` and `htriple`s modified to add invariants and unchanged context-values, `wp_from_inductive` added)
        - State_Ops: Weakest precondition for generalized "state operations" (used to wrap Cminor's base functions for the VCG)
        - Mini_SepLogic: Minimal separation logic example from the thesis
        - Serialize: JSON serialization library/code
        - Basic_Lens
        - TSA_Map: Implementation of the "TSA Map α" from the thesis
        - Sep_Logic: Set up of the separation logic
        - Chunkvals:
            - Alternative view on memory
            - Directly referring to 8/16/32/64-bit machine words in memory instead of CompCert's single-byte "mvals" (or the "val encoded with chunk" mem_val assertion)
            - Seemed like a more natural way of modeling memory contents, especially for array-access, which is primarily interested in having elements of same size
        - Chunkval_Interface: Defines the array interface used in the Case Study, based on the chunkval-view on memory
        - Case_Study
    - lib: [Separation Logic library by Lammich](https://github.com/lammich/isabelle_llvm)
    - compcert: Cminor formalization (listed here with the paths to their CompCert analogues)
        - FP32: Extension of the IEE754 library used, which doesn't define a 32-bit float type
        - BinNums: part of Coq library, not CompCert
        - Archi: x86_64/Archi.v
        - Floats: lib/Floats.v
        - Integers: lib/Integers,v
        - Maps: lib/Maps.v
        - AST: common/AST.v
        - Events: common/Events.v
        - Globalenvs: common/Globalenvs.v
        - Memdata: common/Memdata.v
        - Memory: common/Memory.v
        - Memtype: common/Memtype.v
        - Smallstep: common/Smallstep.v
        - Switch: common/Switch.v
        - Values: common/Values.v
        - Cminor and Cminor_Syntax: backend/Cminor.v (split for performance reasons)
- ./scripts: Python tools
    - build_serialize.py: JSON (de)serialization code generator
    - transl_gallina.py: Gallina translator
    - transl_simple.py: "Simple" Gallina translation using regexes; also used by transl\_gallina.py
    - cminor.jssl: Specification file containing the instructions to generate serialization code for Cminor's types
    - *.mli: The interface files taken from the extracted CompCert code defining Cminor's types
- ./compcert
    - thesis.patch: Patch containing the changes to enable Cminor-JSON-deserialization

### Building CompCert
- The CompCert version used as the base of this thesis was [this GitHub commit](https://github.com/AbsInt/CompCert/commit/26ddb90280b45e92d90eead89edb237f2922824a) (slightly newer than version 3.7):
- Starting in the directory of this readme, it can be checked out and patched with
    ```shell
    cd compcert
    git clone https://github.com/AbsInt/CompCert.git
    cd CompCert
    git checkout 26ddb902
    git apply ../thesis.patch
    ```
- The build process is the one described [here](https://compcert.org/man/manual002.html), with an additional dependency on the `yojson` package:
    ```shell
    opam update
    opam switch create 4.07.1
    eval ``opam env``
    opam install coq=8.11.2 menhir yojson
    ```
- As target platform I used x86_64-linux:
    ```shell
    ./configure x86_64-linux
    make all
    ```

### Compiling the Case Study
- The case study can then be compiled with
    ```shell
    ./ccomp -dcminor -dasm array_case_study.cmj -o array_case_study
    ```
    This will produce the files
    - `array_case_study.cm`: CompCert's Cminor reading of the .cmj file
    - `array_case_study.s`: generated Assembler code
    - `array_case_study`: compiled binary

### Acknowledgements

Since this project would have been impossible to realize without them, I'd like to (again) thank my advisors [Dr. Peter Lammich](https://www21.in.tum.de/~lammich/) and [Dr. Maximilian Haslbeck](https://www21.in.tum.de/~haslbema/), as well as [Prof. Tobias Nipkow](https://www21.in.tum.de/~nipkow/)!