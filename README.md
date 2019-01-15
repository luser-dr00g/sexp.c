sexp.c
======

A very primitive LISP interpreter

debugged with help from StackOverflow:
http://stackoverflow.com/questions/18096456/why-wont-my-little-lisp-quote

Designed to follow closely the original definitions in the McCarthy paper.

prematurely submitted for review:
https://groups.google.com/forum/#!topic/comp.lang.lisp/mpRg2BwGgdo
https://groups.google.com/d/topic/comp.lang.c/FiC6hbH1azw/discussion

"As a language, it's probably worse than any Lisp that has ever 
existed, including the early work by John McCarthy's group." --Kaz Kylheku

What's a hackish way to do a ceiling divide on integers? 2015/02/12 (Kaz saves the day, again)
https://groups.google.com/d/topic/comp.lang.c/fXEAmat6-Pk/discussion

For the example statements from the Micro Manual for Lisp.

    josh@Z1 ~/sexp.c
    $ cat test
    (QUOTE A)
    (CAR (QUOTE (A B C)))
    (CDR (QUOTE (A B C)))
    (CONS (QUOTE A) (QUOTE (B C)))
    (EQ (CAR (QUOTE (A B))) (QUOTE A))
    (ATOM (QUOTE A))
    (COND ((ATOM (QUOTE A))(QUOTE B))((QUOTE T)(QUOTE C)))
    ((LAMBDA (X Y) (CONS (CAR X) Y)) (QUOTE (A B)) (CDR (QUOTE (C D))))
    ((LABEL FF (LAMBDA (X)(COND ((ATOM X) X) ((QUOTE T)(FF (CAR X))))))(QUOTE ((A B) C)))

`sexp` yields the follow (correct) output.

    josh@Z1 ~/sexp.c
    $ ./sexp <test
    >A 
    >A 
    >(B C )
    >(A B C )
    >T 
    >T 
    >B 
    >(A D )
    >A 
    >

Off and on, I've considered what to do next with this project.

One idea is to delve further into the Lisp 1.5 manual and implement the remaining functions, hopefully approaching a usable language (at least for vintage programs).

But the idea I have a real desire to do is to add a compiler targetting this crazy interpreter based on unrelated research into the roots of FORTH and machine code.
https://groups.google.com/d/topic/comp.lang.c/WGSl7ERMu1U/discussion

AFAIUI I only need to write the code-generation part. The existing implementation can serve as a frpnt-end to the compiler for bootstrapping.

Some related projects from which I'm drawing inspiration are
[Zozotez](https://code.google.com/p/zozotez) 
and [Scheme from Scratch](http://michaux.ca/articles/scheme-from-scratch-bootstrap-v0_1-integers).

I'm 3 chapters into the 1979 book *Anatomy of Lisp*. So the compiler part should happen in the near(er) future. I'm considering adding alternate implementations for various pieces like the definition of symbols (preserve case, fold to upper, fold to lower), and the behavior of environments (association lists, Weizenbaum environments, other).

