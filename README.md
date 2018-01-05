## Ruby Core

My project consists of two main elements (1) AST conversion into the core language and (2) the redex semantics of the core language

## AST Conversion
The ast conversion is written in node.c under the section labeled AST conversion.  The conversion is pretty straightforward with some edge cases that were handled specifically.
Essentially, the entire AST is walked and any recognized nodes are converted into the core langauge recursively.  I made extensive use of macros to handle string manipulation.
To run a conversion:
1. compile  (may need to use sudo) by calling make all
2. run "./ruby --dump parsetree SOURCEFILE; cat RubyCoreLang.core"
3. both the AST and the core language conversion will print

## Core Language Semantics
My core language semantics is a redex semantics with a configuration consisting of a tuple (C,E,S,K) with C representing the control string (the current exp being executed) E is the environment,
S is the Store, and K is the continuation. The environment is actually kept in the store and each E is simply the environment's store location.  
Various metafunctions are used to manipulate the store and environment to simplify the reduction rules. To summarize execution of an example program, the machine descends
into subexpressions storing a new continuation at the head of the implicit linked list of continuations with a hole representing the current subexpression begin computed.  
This proceeds until there is an atomic expression paired with the halt continuation. The most interesting cases of the semantics are with do and non-local return.  
In the case of do, the environment is passed along each statement in the sequence so that variable assignments made earlier on in the do are available in later statements, more like th
e control flow in ruby.  Since assignments only occur in do's  with actual Ruby programs this does not violate lexical scoping. Since environments are mutable this is easily implemente
 by not changing the environment reference while descending into each statement in the sequence.  The next interesting case is the non-local return behavior.
To implement non-local return, if a function is called with a block argument, the current continuation is bound in the block's environment, so in the event of a return from the block, it will always have the proper continuation to call.  
At the bottom of the file there are various test cases for the reduction rules, and at the very bottom, there are 7 example programs that I copied from the AST conversion.  The comment
s indicate which example the test is from.  The ruby code for each example is stored in RubyCore/ruby\_examples .  
To copy your own programs, just write them out in Ruby and run the AST conversion. Only a subset of the language is supported (function application, +, if, lambdas, procs, blocks), strings, numbers, variables, assignments) so just check that the AST conversion output
 doesn't contain ERROR anywhere (this is the default case in the recursive switch statement).

## Important Issues Encountered
Two issues that stand out in my mind are (1) if environments aren't mutable, functions can't refer to functions that are defined after them.  This logic is simple, if a closure is
created at the definition of f1 before f2 is defined, that environment won't be updated with the binding of f2.  (2)  The second is that if continuations aren't stored at the point
of creation of a block, there is no way to have a stack-based non-local return system if there can be multiple yields into blocks in higher functions. The reason is that when
yield is called, that pushes more stack frames onto the stack, and when return is called from a top-level block, popping frames off until reaching the most recent
function-call-with-block will fail, because a top level block should return to the least recent function-call-with-block frame. To solve this, as mentioned earlier, each
continuation is stored in the environment of the block, so it can be referred to if return is ever called.
