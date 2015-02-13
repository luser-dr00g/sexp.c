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

For the example statements from the Micro Manual for Lisp
(amended to restrict atoms to a maximum of 5 characters),

    josh@Z1 ~/sexp.c
    $ cat test
    (QUOTE A)
    (CAR (QUOTE (A B C)))
    (CDR (QUOTE (A B C)))
    (CONS (QUOTE A) (QUOTE (B C)))
    (EQ (CAR (QUOTE (A B))) (QUOTE A))
    (ATOM (QUOTE A))
    (COND ((ATOM (QUOTE A))(QUOTE B))((QUOTE T)(QUOTE C)))
    ((LAMBD (X Y) (CONS (CAR X) Y)) (QUOTE (A B)) (CDR (QUOTE (C D))))
    ((LABEL FF (LAMBD (X)(COND ((ATOM X) X) ((QUOTE T)(FF (CAR X))))))(QUOTE ((A B) C)))

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


