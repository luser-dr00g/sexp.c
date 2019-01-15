/* sexp.c - an integer-coded tiny lisp.

  $ make sexp CFLAGS='-Wno-implicit-int -Wno-implicit-function-declaration'

cf.
http://www.ioccc.org/1989/jar.2.c                  <-- memory 'cursors'
http://leon.bottou.org/projects/minilisp           <-- compact 'C'-able cell encoding
http://www.jsoftware.com/jwiki/Essays/Incunabulum  <-- tiny APL interpreter
http://www-formal.stanford.edu/jmc/recursive/recursive.html  <-- original lisp paper
http://www.paulgraham.com/rootsoflisp.html                   <-- alternate presentation of core (with bugfix)
http://www.cse.sc.edu/~mgv/csce330f13/micromanualLISP.pdf    <-- original micro-manual for lisp
http://codegolf.stackexchange.com/questions/284/write-an-interpreter-for-the-untyped-lambda-calculus/3290#3290
http://stackoverflow.com/questions/18096456/why-wont-my-little-lisp-quote  <-- earlier version of this program
http://www.nhplace.com/kent/Papers/Special-Forms.html   <-- FEXPRs NLAMBDAs and MACROs, oh my!
https://web.archive.org/web/20070317222311/http://www.modeemi.fi/~chery/lisp500/lisp500.c <-- similar idea
 */
#include<assert.h>
#include<ctype.h> //isspace
#include<signal.h>
#include<stdarg.h>
#include<stdio.h>
#include<stdlib.h>
#include<string.h>
#include<unistd.h>
#include"ppnarg.h"   /*https://github.com/luser-dr00g/sexp.c/blob/master/ppnarg.h*/

/*defun macro thanks to Kaz Kylheku: https://groups.google.com/d/msg/comp.lang.c/FiC6hbH1azw/-Tiuw2oQoyAJ*/
#define defun(NAME,ARGS,...) int NAME ARGS { return __VA_ARGS__; }
#define ALPHA "T"
#define NIL   (0)
#define T atom(ALPHA)
#define LPAR  "("
#define RPAR  ")"
#define ATOMBUFSZ  10


/* each word is interpreted as a 2 bit tag
   and a sizeof(int)*8-2 bit signed number. 32bit int :: 30bit + 2bit tag [^minilisp]*/
enum { TAGCONS, TAGATOM, TAGOBJ, TAGNUM,
       TAGBITS = 2,
       TAGMASK = (1U<<TAGBITS)-1 };
defun(  val,  (x),x>>TAGBITS)
defun(  tag,  (x),x&TAGMASK)
defun(  listp,(x),tag(x)==TAGCONS) /* predicates */
defun(  atomp,(x),tag(x)==TAGATOM)
defun(objectp,(x),tag(x)==TAGOBJ)
defun(numberp,(x),tag(x)==TAGNUM)
defun(  consp,(x),x&&listp(x))


/* memory is organized as a large array of ints
   each int is a "word" and memory can be accessed by
       m[int]
   the int here is a cursor called herein a "pointer" (<-- always in quotes) [^codegolf jar2]*/
int*m,*n,msz; /*memory next mem-size*/

/*build lists [^ppnarg found in:comp.lang.c ^variadic functions:k&r2]
  list() variadic macro uses ppnarg.h to count the arguments and call listn
https://github.com/luser-dr00g/sexp.c/blob/master/ppnarg.h
  listn() variadic function copies n (int) arguments to memory and call lista
  lista() constructs a list of n elements from pointer to memory
 */
int lista(int c,int*a){int z=NIL;for(;c;)z=cons(a[--c],z);return z;}
int listn(int c,...){va_list a;int*z=n;
    va_start(a,c);for(;c--;)*n++=va_arg(a,int);va_end(a);
    c=n-z;return lista(c,z);}
#define list(...) listn(PP_NARG(__VA_ARGS__),__VA_ARGS__)


/* global environment for REPL, modified by SET, SETQ and DEFUN */
int env;

/* bias the alphabet at the ascii code for T,  [<my own brilliant idea]
   this way, the word 1 means 30bit 0 + 2bit 01 :: the symbol T
        and, the word 0  ::   30bit 0 + 2bit 00 :: the list NIL
                 word 5  ::   30bit 1 + 2bit 01 :: the symbol NIL
                 word 9  ::   30bit 2 + 2bit 01 :: the symbol SETQ
                 word 4  ::   30bit 1 + 2bit 00 :: the list at address 1
                 word 8  ::   30bit 2 + 2bit 00 :: the list at address 2

   tag  00 : list   : val is "pointer" to 2-cell pair
        01 : atom   : val is encoded as 5 6-bit codes packed low-to-high,
                                        with the first code biased at `enc('T')` (ie. 20)
        10 : object : val is "pointer" to an object union
        11 : number : val is a 30bit fixnum
   [^minilisp ^lisp500]
*/

//defun(atom,(char*s),0)
//defun(prnatom,(unsigned x),0)
//defun(rdatom,(char**p,char*buf,int i),atom(buf))

defun(number, (x),     x<<TAGBITS|TAGNUM)
defun(object, (x),     x<<TAGBITS|TAGOBJ)
enum objecttag {SUBR, FSUBR, SUBR2, FSUBR2, STRING};
union object {int tag;
      struct {int tag; int(*f)();} f;
      struct {int tag; char*s;   } s;
                                     };
defun(objptr, (union object*p,union object o),*p=o,object((int*)p-m))
union object*newobjptr(){void *p=n;return n+=(sizeof(union object)+sizeof*n-1)/sizeof*n,p;}
defun(objfunc,(enum objecttag t,int(*f)()),objptr(newobjptr(),(union object){.f={.tag=t,.f=f}}) )
defun( subr1,(int(*f)()),objfunc( SUBR, f))
defun(fsubr1,(int(*f)()),objfunc(FSUBR, f))
defun( subr2,(int(*f)()),objfunc( SUBR2,f))
defun(fsubr2,(int(*f)()),objfunc(FSUBR2,f))

char*newstrptr(char*s){return n+=(strlen(s)+1+sizeof*n-1)/sizeof*n,s;}
defun(objstr,(char*s),objptr(newobjptr(),(union object){.s={.tag=STRING,.s=s}}))
defun(string,(char*s),objstr(newstrptr(strcpy((char*)n,s))))
union object *strobj(int x){return (void *) &m[x>>TAGBITS];}
defun(prnstring,(x),printf("%s ", strobj(x)->s.s))
defun(stringp,(x),tag(x)==TAGOBJ&&strobj(x)->tag==STRING)

defun(prnatom,(unsigned x),prnatom0(x>>TAGBITS),printf(" "))
defun(atom,   (char*s),encstr(s)<<TAGBITS|TAGATOM)
char *rdatom(char**p,char*buf,int i){return memcpy(buf,*p,i), (*p)+=i, buf;}

int atoms;
defun(findstr, (char*s,int slist,int i), !strcmp(strobj(car(slist))->s.s,s)? i:
            		    cdr(slist)? findstr(s,cdr(slist),i+1): (rplacd(slist,list(string(s))),i+1))
defun(encstr, (char*s),findstr(s,atoms,0))

defun(prnatomx,(x,atoms),x?prnatomx(x-1,cdr(atoms)):printf("%s", strobj(car(atoms))->s.s))
defun(prnatom0,(x),prnatomx(x,atoms))

/*manipulating lists.
  val() of course returns an int i which indexes `int *m;`
                             ^^^^^:our "pointer"  ^^^^^^:the memory
  using the commutativity of indexing in C: m[i] == *(m + i) == i[m] */
defun(cons,  (x,y),*n++=x,*n++=y,(n-m)-2<<TAGBITS|TAGCONS)
defun(rplaca,(x,y),consp(x)?val(x)[m]=y:0)
defun(rplacd,(x,y),consp(x)?val(x)[m+1]=y:0)
defun(car,   (x),  consp(x)?val(x)[m]:0)
defun(cdr,   (x),  consp(x)?val(x)[m+1]:0)
defun(caar,  (x),          car(car(x)))
defun(cadr,  (x),          car(cdr(x)))
defun(cddr,  (x),          cdr(cdr(x)))
defun(cadar, (x),      car(cdr(car(x))))
defun(caddr, (x),      car(cdr(cdr(x))))
defun(cdddr, (x),      cdr(cdr(cdr(x))))
defun(caddar,(x),  car(cdr(cdr(car(x)))))
defun(cadddr,(x),  car(cdr(cdr(cdr(x)))))

/*auxiliary functions [^jmc]*/
defun(eq,(x,y),x==y)
defun(ff,(x),atomp(x)?x:ff(car(x))) /* find first atom */
defun(subst,(x,y,z),atomp(z)?(eq(z,y)?x:z): cons(subst(x,y,car(z)),subst(x,y,cdr(z))))
defun(equal,(x,y),(atomp(x)&&atomp(y)&&eq(x,y))
        ||(consp(x)&&consp(y)&&equal(car(x),car(y))&&equal(cdr(x),cdr(y)))) /*lists equal?*/
defun(null,(x),listp(x)&&val(x)==0) /*list == NIL?*/

/*association lists [^jmc]*/
defun(append,(x,y),null(x)?y:cons(car(x),append(cdr(x),y)))
defun(among,(x,y),!null(y)&&equal(x,car(y))||among(x,cdr(y)))
defun(pair,(x,y),null(x)&&null(y)?NIL:consp(x)&&consp(y)? cons(list(car(x),car(y)),pair(cdr(x),cdr(y))):0)
defun(assoc,(x,y),eq(caar(y),x)?cadar(y):null(y)?0:assoc(x,cdr(y)))

/*the universal function eval() [^jmc]*/
defun(sub2,(x,z),null(x)?z:eq(caar(x),z)?cadar(x):sub2(cdr(x),z))
defun(sublis,(x,y),atomp(y)?sub2(x,y):cons(sublis(x,car(y)),sublis(x,cdr(y))))
defun(apply,(f,args),eval(cons(f,appq(args)),NIL))
defun(appq,(m),null(m)?NIL:cons(list(atom("QUOTE"),car(m)),appq(cdr(m))))
defun(eval,(e,a),
    //prnlst(e), printf("\n"),
    numberp(e)? e:
    atomp(e)? assoc(e,a):
    atomp(car(e))?(
	eq(car(e),atom("QUOTE"))? cadr(e):
	eq(car(e),atom("ATOM"))?  atomp(eval(cadr(e),a)):
	eq(car(e),atom("EQ"))?    eval(cadr(e),a)==eval(caddr(e),a):
	eq(car(e),atom("COND"))?  evcon(cdr(e),a):
	eq(car(e),atom("CAR"))?   car(eval(cadr(e),a)):
	eq(car(e),atom("CDR"))?   cdr(eval(cadr(e),a)):
	eq(car(e),atom("CONS"))?  cons(eval(cadr(e),a),eval(caddr(e),a)):
//	eq(car(e),atom("DEFUN"))? (a=list(atom("LABEL"),cadr(e),list(atom("LAMBDA"),caddr(e),cadddr(e))),
//	    			   env=append(env, list(list(cadr(e),a))), a):
        eval(cons(assoc(car(e),a),cdr(e)),a)):
        //eval(cons(assoc(car(e),a),evlis(cdr(e),a)),a) ): /*<jmc ^rootsoflisp*/
    objectp(car(e))? 	       evobj(e,a):
    eq(caar(e),atom("LABEL"))? eval(cons(caddar(e),cdr(e)),cons(list(cadar(e),car(e)),a)):
    eq(caar(e),atom("LAMBDA"))? eval(caddar(e),append(pair(cadar(e),evlis(cdr(e),a)),a)):
                   /*LAMBDA with 5-char atoms */
    0)
defun(evcon,(c,a),eval(caar(c),a)?eval(cadar(c),a):evcon(cdr(c),a))
defun(evlis,(m,a),null(m)?NIL:cons(eval(car(m),a),evlis(cdr(m),a)))

defun(evobjo,(o,e,a)union object o;, o.tag== SUBR ? o.f.f(eval(cadr(e),a)):
                                     o.tag==FSUBR ? o.f.f(cdr(e)):
			             o.tag== SUBR2? o.f.f(eval(cadr(e),a), eval(caddr(e),a)):
                                     o.tag==FSUBR2? o.f.f(cadr(e),caddr(e)): 0)
defun(evobj,(e,a),evobjo(*(union object*)(m+val(car(e))),e,a))

defun(maplist,(x,f),null(x)?NIL:cons(apply(f,x),maplist(cdr(x),f)))

defun(assocpair,(x,y),eq(caar(y),x)?car(y):null(y)?0:assocpair(x,cdr(y)))
defun(seta,(a,x,y),(a?rplacd(a,list(y)):(env=append(list(list(x,y),env)))),y)
defun(set,   (x,y),seta(assocpair(x,env),x,y))

defun(prn,(x),atomp(x)  ?prnatom(x)               : /*print with dot-notation [^stackoverflow]*/
      	      stringp(x)?prnstring(x)             :
	      numberp(x)?printf("%d ",val(x))     :
	      objectp(x)?printf("OBJ_%d ",val(x)) :
	      consp(x)  ?printf("( "),prn(car(x)),printf(". "),prn(cdr(x)),printf(") "):
	                 printf("NIL "))
defun(prnlstn,(x),!listp(x)?prn(x):
        ((car(x)?prnlst(car(x)):0),(cdr(x)?prnlstn(cdr(x)):0)))
defun(prnlst,(x),!listp(x)?prn(x):
        (printf(LPAR),(car(x)?prnlst(car(x)):0),(cdr(x)?prnlstn(cdr(x)):0),printf(RPAR)))

defun(rdlist,(p,z,u)char**p;,u==atom(RPAR)?z:append(cons(u,NIL),rdlist(p,z,rd(p))))
defun(rdnum,(p,v)char**p;,*++*p>='0'&&**p<='9'?rdnum(p,v*10+**p-'0'):v)
defun(rdbuf,(char**p,char*buf,char c),(c?(c==' '        ?(++(*p),rd(p)                ):
			                  c==*RPAR      ?(++(*p),atom(RPAR)           ):
				          c==*LPAR      ?(++(*p),rdlist(p,NIL,rd(p))  ):
			                  c>='0'&&c<='9'?        number(rdnum(p,c-'0')):
					        atom(rdatom(p,buf,strcspn(*p,"() \t"))) ):0))
defun(rd,(char**p),rdbuf(p,(char[ATOMBUFSZ]){""},**p))

//void fix(x){signal(SIGSEGV,fix);sbrk(sizeof(int)*(msz*=2));} /*grow memory in response to memory-access fault*/
int main(){
    //char *s;
    char s[BUFSIZ];
    char *p;
    int x;

    /* improved assertions thanks to Tim Rentsch, cf.
       https://groups.google.com/d/msg/comp.lang.c/FZldZaPpTT4/5g4bWdsxAwAJ */
    assert((-1 & 3) == 3); /* that ints are 2's complement */
    assert((-1 >> 1) < 0); /* that right shift keeps sign */
    //assert((-1>>1)==-1);	/*require 2's-complement and right-shift must be sign-preserving */
    //printf("");  /* exercise stdio so it (hopefully) malloc's what it needs before we take sbrk() */
    //snprintf(NULL, 0, "%c%d%f", 'x', 42, 72.27);
    //n=m=sbrk(sizeof(int)*(msz=getpagesize()));*n++=0;*n++=0; /*initialize memory and begin at cell 2*/
    //signal(SIGSEGV,fix); /*might let it run longer, obscures problems*/
    n=m=calloc(msz=getpagesize(),sizeof(int));

    n += 16;
    atoms = list(
		 string("T"),
		 string("NIL")
		 );
    //prnlst(atoms);
    //prnatom(atom("T"));
    //prnatom(atom("NIL"));
    env = list(
            list(atom("T"),     atom("T")   ),
            list(atom("NIL"),        NIL    ),
            list(atom("CAAR"),  subr1(caar) ),
            list(atom("CADR"),  subr1(cadr) ),
            list(atom("CDDR"),  subr1(cddr) ),
            list(atom("CADAR"), subr1(cadar)),
            list(atom("CADDR"), subr1(caddr)),
            list(atom("CDDDR"), subr1(cdddr)),
            list(atom("SET"),   subr2(set)  ),
            list(atom("SETQ"), fsubr2(set)  )
            );
    //prnlst(atoms);
    //prnlst(env);
    //fflush(stdout);

    while(1) {
        //printf("env:\n"); prnlst(env); printf("\n");
        printf(">");
        fflush(0);
        if (!fgets(s,sizeof s,stdin))
            break;
        s[strlen(s)-1]=0;
        p = s;
        x = rd (&p);
        //printf ("%s\n", s);

        //prn(x); printf("\n");
        //prnlst(x);
        //fflush(0);
        //printf ("\nEVAL\n");
        x = eval(x, env);

        //printf ("x: %d\n", x);
        //printf ("0: %o\n", x);
        //printf ("0x: %x\n", x);
        //printf ("tag(x): %d\n", tag (x));
        //printf ("val(x): %d\n", val (x));
        //printf ("car(x): %d\n", car (x));
        //printf ("cdr(x): %d\n", cdr (x));
        //prn (x); printf("\n");
        prnlst(x); printf("\n");
    }

    return 0;
}
