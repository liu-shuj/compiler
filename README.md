# compiler
compiler for subset of racket (with experimental floating point support)

Shujun Liu 2019

Follows IU compiler course
https://github.com/IUCompilerCourse/Essentials-of-Compilation


Usage: 
1. use all passes in order in compiler.rkt (or compiler_fp.rkt) to translate program into assembly code, 
2. save as .s file, 
3. run "gcc filename.s runtime.c",
4. run a.out,
5. run "echo $?" to see results because result is returned as return value of the program.
