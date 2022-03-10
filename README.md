A compiler for a toy 16-bit load-store ISA I made, for a CPU built in the "Turing Complete" game available on Steam.  
The code is in Chez Scheme, and, since I was figuring out what I'm doing as I went along, really bad. Now that it has gone too complicated for mortals to understand or reasonably modify, I sequester it to this repository where it can exist as an artifact of learning having happened.  
The compiled language is simple and low-level, as my main focus was learning about optimizing the generated machine code. The first two passes create an AST and convert it to a linear IR, which mostly serve to digest the code into a form ready for generating the assembly, although there's some optimizations there, like detecting tail calls(hell yeah TCO). The bulk of the compiler is the assembly generator, with a (poor) register allocator based on a (inaccurate) linear scan lifetime analysis, and a pile of very ad-hoc optimization steps.  
The bottom of the file contains some test programs, which should be fairly readable to anyone not afraid of excess parentheses. The one I find the funniest is the "gc" one which, yeah, abuses the ability to read the stack address to implement a bare-bones Boehm-like garbage collector, and (usually) manages not to run out of stack while scanning the entire memory.  
Ideally I would have included schematics for the game CPU that can run this code, and instructions on using it, but this would require effort. However, if you run the source using chezscheme-9.5.4 or a more recent one, it should compile and run all of the test programs, demonstrating that at least some sort of computing has occured.  
The instruction set is dead simple as I wanted something that would be easy to implement in CPU, and make for an interesting target for learning about optimizing compilers without getting bogged down in the mechanics of complicated instructions.  
Compilers are fun, but pretty hard.  

