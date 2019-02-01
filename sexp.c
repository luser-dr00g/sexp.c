//  sexp.c - an integer-coded tiny lisp.
//  comments at end
#include<assert.h>
#include<ctype.h>
#include<signal.h>
#include<stdarg.h>
#include<stdio.h>
#include<stdlib.h>
#include<string.h>
#include<unistd.h>
#include"ppnarg.h"   /*https://github.com/luser-dr00g/sexp.c/blob/master/ppnarg.h*/

#ifdef DEBUGMODE
   #define CHECK_DEBUG_LEVEL(LVL) (LVL<=DEBUGMODE)
   #define DEBUG(LVL,...) ( CHECK_DEBUG_LEVEL(LVL) ? fprintf(stderr, __VA_ARGS__) : 0 )
#define IFDEBUG(LVL,...) ( CHECK_DEBUG_LEVEL(LVL) ? __VA_ARGS__ : 0 )
#else
   #define DEBUG(...) 0
   #define IFDEBUG(...) 0
#endif
#define nil   (0)
#define LPAR  "("
#define RPAR  ")"
#define ATOMBUFSZ  10
#define defun(NAME,ARGS,...) int NAME ARGS { IFDEBUG(2, fprintf(stderr, "%s ",__func__)); return __VA_ARGS__; }

struct state {
int*m,*n,msz, /*memory next mem-size*/
    env,      /* global environment for REPL, modified by SET, SETQ and DEFUN */
    atoms;    /* head of atom list */
    char linebuf[BUFSIZ];
    char *inputptr;
} global = { .linebuf = { 0 } };

#define INIT_ALL     INIT_MEMORY INIT_ATOM_LIST INIT_ENVIRONMENT INIT_INPUTPTR
#define INIT_MEMORY  global.n=16+(global.m=calloc(global.msz=getpagesize(),sizeof(int)));
#define ATOM_PROPS(x)     list(TO_STRING(x))
#define INIT_ATOM_LIST    global.atoms = list(ATOMSEEDS(ATOM_PROPS));
#define INIT_ENVIRONMENT                           \
    global.env = list(                             \
	       list(T,              T           ), \
	       list(NIL,            nil         ), \
	       list(atom("CAAR"),   subr1(caar) ), \
	       list(atom("CADR"),   subr1(cadr) ), \
	       list(atom("CDDR"),   subr1(cddr) ), \
	       list(atom("CADAR"),  subr1(cadar)), \
	       list(atom("CADDR"),  subr1(caddr)), \
	       list(atom("CDDDR"),  subr1(cdddr)), \
	       list(atom("SET"),    subr2(set)  ), \
	       list(SETQ,          fsubr2(set)  )  \
            );
#define INIT_INPUTPTR     global.inputptr = global.linebuf;

enum { TAGCONS, TAGATOM, TAGOBJ, TAGNUM,  TAGBITS = 2, TAGMASK = (1U<<TAGBITS)-1 };
defun(  val,  (x),x>>TAGBITS)
defun(  tag,  (x),x&TAGMASK)
defun(number, (x),x<<TAGBITS|TAGNUM)
defun(object, (x),x<<TAGBITS|TAGOBJ)
enum objecttag {SUBR, FSUBR, SUBR2, FSUBR2, STRING};
union object {int tag;
      struct {int tag; int(*f)();} f;
      struct {int tag; char*s;   } s;
};

defun(objptr, (union object*p,union object o),*p=o,object((int*)p-global.m))
union object*newobjptr(void*p){return global.n+=(sizeof(union object)+sizeof*global.n-1)/sizeof*global.n,p;}
union object*ptrobj(int x){return(void*)&global.m[x>>TAGBITS];}
defun(objfunc,(enum objecttag t,int(*f)()),objptr(newobjptr(global.n),(union object){.f={.tag=t,.f=f}}) )
defun( subr1,(int(*f)()),objfunc( SUBR, f))
defun(fsubr1,(int(*f)()),objfunc(FSUBR, f))
defun( subr2,(int(*f)()),objfunc( SUBR2,f))
defun(fsubr2,(int(*f)()),objfunc(FSUBR2,f))

int lista(int c,int*a){int z=nil;for(;c;)z=cons(a[--c],z);return z;}
int listn(int c,...){va_list a;int*z=global.n;
    va_start(a,c);while(c--)*global.n++=va_arg(a,int);va_end(a);return lista(global.n-z,z);}
#define list(...) listn(PP_NARG(__VA_ARGS__),__VA_ARGS__)

#define ATOMSEEDS(x) x(T),x(NIL),x(SETQ),x(QUOTE),x(ATOM),x(EQ),x(COND),\
		     x(CAR),x(CDR),x(LAMBDA),x(LABEL),x(CONS),x(DEFUN),x(QUIT)
#define atom_enum(x) ATOM_##x
#define short_cut(x) x=atom_enum(x)<<TAGBITS|TAGATOM
enum{ATOMSEEDS(atom_enum),ATOMSEEDS(short_cut)};
#define TO_STRING(x) string(#x)
char*newstrptr(char*s){return global.n+=(strlen(s)+1+sizeof*global.n-1)/sizeof*global.n,s;}
defun(objstr, (char*s),objptr(newobjptr(global.n),(union object){.s={.tag=STRING,.s=s}}))
defun(string, (char*s),objstr(newstrptr(strcpy((char*)global.n,s))))
defun(findstr,(s,slist,i)char*s;,!strcmp(ptrobj(caar(slist))->s.s,s)?i:
      cdr(slist)?findstr(s,cdr(slist),i+1):(rplacd(slist,list(list(string(s)))),i+1))
defun(encstr, (char*s),findstr(s,global.atoms,0))
defun(atom,   (char*s),encstr(s)<<TAGBITS|TAGATOM)

defun(  listp,(x),tag(x)==TAGCONS) 		/* predicates */
defun(  atomp,(x),tag(x)==TAGATOM)
defun(objectp,(x),tag(x)==TAGOBJ)
defun(numberp,(x),tag(x)==TAGNUM)
defun(  consp,(x),x&&listp(x))
defun(stringp,(x),tag(x)==TAGOBJ&&ptrobj(x)->tag==STRING)

defun(cons,  (x,y),*global.n++=x,*global.n++=y,(global.n-global.m)-2<<TAGBITS|TAGCONS)
defun(rplaca,(x,y),consp(x)?val(x)[global.m]=y:0)
defun(rplacd,(x,y),consp(x)?val(x)[global.m+1]=y:0)
defun(car,   (x),  consp(x)?val(x)[global.m]:0)
defun(cdr,   (x),  consp(x)?val(x)[global.m+1]:0)
defun(caar,  (x),          car(car(x)))
defun(cadr,  (x),          car(cdr(x)))
defun(cddr,  (x),          cdr(cdr(x)))
defun(cadar, (x),      car(cdr(car(x))))
defun(caddr, (x),      car(cdr(cdr(x))))
defun(cdddr, (x),      cdr(cdr(cdr(x))))
defun(caddar,(x),  car(cdr(cdr(car(x)))))
defun(cadddr,(x),  car(cdr(cdr(cdr(x)))))

defun(eq,   (x,y),x==y) 	/*auxiliary functions [^jmc]*/
defun(ff,   (x),atomp(x)?x:ff(car(x))) /* find first atom */
defun(subst,(x,y,z),atomp(z)?(eq(z,y)?x:z): cons(subst(x,y,car(z)),subst(x,y,cdr(z))))
defun(equal,(x,y),(atomp(x)&&atomp(y)&&eq(x,y))
        ||(consp(x)&&consp(y)&&equal(car(x),car(y))&&equal(cdr(x),cdr(y)))) /*lists equal?*/
defun(null, (x),listp(x)&&val(x)==0) /*list == NIL?*/
defun(subsq,(x,y,z),null(z)?nil:atomp(z)?(eq(y,z)?x:z):car(z)==QUOTE?z:
      cons(subsq(x,y,car(z)),subsq(x,y,cdr(x))))

defun(append,(x,y),null(x)?y:cons(car(x),append(cdr(x),y))) 	/*association lists [^jmc]*/
defun(among, (x,y),!null(y)&&equal(x,car(y))||among(x,cdr(y)))
defun(pair,  (x,y),null(x)&&null(y)?nil:consp(x)&&consp(y)? cons(list(car(x),car(y)),pair(cdr(x),cdr(y))):0)
defun(assoc, (x,y),eq(caar(y),x)?cadar(y):null(y)?0:assoc(x,cdr(y)))
defun(assocpair,(x,y),eq(caar(y),x)?car(y):null(y)?0:assocpair(x,cdr(y)))
defun(seta,   (a,x,y),(a?rplacd(a,list(y)):(global.env=append(list(list(x,y),global.env)))),y)
defun(set,      (x,y),seta(assocpair(x,global.env),x,y))
defun(maplist,  (x,f),null(x)?nil:cons(apply(f,x),maplist(cdr(x),f)))

defun(sub2,  (x,z),null(x)?z:eq(caar(x),z)?cadar(x):sub2(cdr(x),z))
defun(sublis,(x,y),atomp(y)?sub2(x,y):cons(sublis(x,car(y)),sublis(x,cdr(y))))
defun(apply, (f,args),eval(cons(f,appq(args)),nil))
defun(appq,  (m),null(m)?nil:cons(list(QUOTE,car(m)),appq(cdr(m))))
defun(eval,  (e,a),            /*the universal function eval() [^jmc]*/
    numberp(e)?   e:
    atomp(e)?     assoc(e,a):
    atomp(car(e))?(
	eq(car(e),QUOTE)? cadr(e):
	eq(car(e),ATOM)?  atomp(eval(cadr(e),a)):
	eq(car(e),EQ)?    eval(cadr(e),a)==eval(caddr(e),a):
	eq(car(e),COND)?  evcon(cdr(e),a):
	eq(car(e),CAR)?   car(eval(cadr(e),a)):
	eq(car(e),CDR)?   cdr(eval(cadr(e),a)):
	eq(car(e),CONS)?  cons(eval(cadr(e),a),eval(caddr(e),a)):
	eq(car(e),DEFUN)? (a=list(LABEL,cadr(e),list(LAMBDA,caddr(e),cadddr(e))),
	    			   global.env=append(global.env, list(list(cadr(e),a))), a): 
        eval(cons(assoc(car(e),a),cdr(e)),a)):
        //eval(cons(assoc(car(e),a),evlis(cdr(e),a)),a) ): /*<jmc ^rootsoflisp*/
    objectp(car(e))?    evobj(e,a):
    eq(caar(e),LABEL)?  eval(cons(caddar(e),cdr(e)),cons(list(cadar(e),car(e)),a)):
    eq(caar(e),LAMBDA)? eval(caddar(e),append(pair(cadar(e),evlis(cdr(e),a)),a)):
    0)
defun(evcon, (c,a),eval(caar(c),a)?eval(cadar(c),a):evcon(cdr(c),a))
defun(evlis, (m,a),null(m)?nil:cons(eval(car(m),a),evlis(cdr(m),a)))
defun(evobjo,(o,e,a)union object o;, o.tag== SUBR ? o.f.f(eval(cadr(e),a)):
                                     o.tag==FSUBR ? o.f.f(cdr(e)):
			             o.tag== SUBR2? o.f.f(eval(cadr(e),a), eval(caddr(e),a)):
                                     o.tag==FSUBR2? o.f.f(cadr(e),caddr(e)): 0)
defun(evobj, (e,a),evobjo(*(union object*)(global.m+val(car(e))),e,a))

defun(prn,      (x,f)FILE*f;,
      atomp(x)  ?prnatom(x,f)                : /*print with dot-notation [^stackoverflow]*/
      stringp(x)?prnstring(x,f)              :
      numberp(x)?fprintf(f,"%d ",val(x))     :
      objectp(x)?fprintf(f,"OBJ_%d ",val(x)) :
      consp(x)  ?fprintf(f,"( "),prn(car(x),f),fprintf(f,". "),prn(cdr(x),f),fprintf(f,") "):
	         fprintf(f,"NIL "))
defun(prnstring,(x,f)FILE*f;,fprintf(f,"\"%s\" ", ptrobj(x)->s.s))
defun(prnatomx, (x,atoms,f)FILE*f;,x?prnatomx(x-1,cdr(atoms),f):fprintf(f,"%s ", ptrobj(caar(atoms))->s.s))
defun(prnatom0, (x,f)FILE*f;,prnatomx(x,global.atoms,f))
defun(prnatom,  (unsigned x,FILE*f),prnatom0(x>>TAGBITS,f))
defun(prnlstn,  (x,f)FILE*f;,!listp(x)?prn(x,f):
      ((car(x)?prnlst(car(x),f):0),(cdr(x)?prnlstn(cdr(x),f):0)))
defun(prnlst,   (x,f)FILE*f;,!listp(x)?prn(x,f):
      (fprintf(f,LPAR),(car(x)?prnlst (car(x),f):0),
                       (cdr(x)?prnlstn(cdr(x),f):0),fprintf(f,RPAR)))

char*adjust_case(char*buf){ for(char*p=buf;*p;p++)*p=toupper(*p); return buf; }
char*rdatom(char**p,char*buf,int i){return memcpy(buf,*p,i),buf[i]=0,(*p)+=i,adjust_case(buf);}
defun(rdlist,(p,z,u)char**p;,u==atom(RPAR)?z:append(cons(u,nil),rdlist(p,z,rd(p))))
defun(rdnum, (p,v)char**p;,*++*p>='0'&&**p<='9'?rdnum(p,v*10+**p-'0'):v)
defun(rdbuf, (char**p,char*buf,char c),c?(c==' '        ?(++(*p),rd(p)                ):
			                  c==*RPAR      ?(++(*p),atom(RPAR)           ):
				          c==*LPAR      ?(++(*p),rdlist(p,nil,rd(p))  ):
			                  c>='0'&&c<='9'?        number(rdnum(p,c-'0')):
					  c=='-'&&(*p)[1]>='0'&&(*p)[1]<='9'? number(-rdnum(p,0)):
					        atom(rdatom(p,buf,strcspn(*p,"() \t"))) ):0)
defun(rd,    (char**p),rdbuf(p,(char[ATOMBUFSZ]){""},**p))
defun(check_input,(),!*global.inputptr?global_readline():1)
defun(readch,(),check_input()?*global.inputptr++:QUIT)
defun(read_,(),check_input()?rd(&global.inputptr):QUIT)

int prompt(){ return printf(">"), fflush(0); }
int readline(char *s,size_t sz){ return (prompt(),fgets(s,sz,stdin)&&((s[strlen(s)-1]=0),1)); }
int global_readline(){return global.inputptr=global.linebuf,readline(global.linebuf,sizeof(global.linebuf));}
int repl(x){ return (x=read_())==QUIT?0:
		    (IFDEBUG(0,prn(x,stdout),fprintf(stdout,"\n"),prnlst(x,stdout),fprintf(stdout,"\n")),
		    x=eval(x,global.env),
		    IFDEBUG(0,dump(x,stdout)),
		    prnlst(x,stdout),printf("\n"),
		    repl(0)); }

int dump(int x,FILE*f){
    IFDEBUG(1,fprintf(stderr,"env:\n"), prnlst(global.env,stderr), fprintf(stderr,"\n"));
    fprintf(f,"x: %d\n", x),
    fprintf(f,"0: %o\n", x),
    fprintf(f,"0x: %x\n", x),
    fprintf(f,"tag(x): %d\n", tag(x)),
    fprintf(f,"val(x): %d\n", val(x)),
    fprintf(f,"car(x): %d\n", car(x)),
    fprintf(f,"cdr(x): %d\n", cdr(x)),
    prn(x,f), fprintf(f,"\n");
}

int init(){
    INIT_ALL
    IFDEBUG(2,prnlst(global.atoms,stderr),
    	      prnlst(global.env,stdout), fflush(stderr));
    return 1;
}

int main(){
    assert((-1 & 3) == 3); /* that ints are 2's complement */
    assert((-1 >> 1) < 0); /* that right shift keeps sign */
    return  init() &&
            repl(0);
}


/* sexp.c - an integer-coded tiny lisp.

  $ make test
  $ make test cflags=-DDEBUGMODE=1

cf.
http://www.ioccc.org/1989/jar.2.c                             <-- memory 'cursors'
http://leon.bottou.org/projects/minilisp                      <-- compact 'C'-able cell encoding
http://www.jsoftware.com/jwiki/Essays/Incunabulum             <-- tiny APL interpreter
http://www-formal.stanford.edu/jmc/recursive/recursive.html   <-- original lisp paper
http://www.paulgraham.com/rootsoflisp.html                    <-- alternate presentation of core (with bugfix)
http://www.cse.sc.edu/~mgv/csce330f13/micromanualLISP.pdf     <-- original micro-manual for lisp
http://codegolf.stackexchange.com/questions/284/write-an-interpreter-for-the-untyped-lambda-calculus/3290#3290
http://stackoverflow.com/questions/18096456/why-wont-my-little-lisp-quote  <-- earlier version of this program
http://www.nhplace.com/kent/Papers/Special-Forms.html         <-- FEXPRs NLAMBDAs and MACROs, oh my!
https://web.archive.org/web/20070317222311/http://www.modeemi.fi/~chery/lisp500/lisp500.c  <-- similar idea
defun macro thanks to Kaz Kylheku: https://groups.google.com/d/msg/comp.lang.c/FiC6hbH1azw/-Tiuw2oQoyAJ
better asserts thx to Tim Rentsch https://groups.google.com/d/msg/comp.lang.c/FZldZaPpTT4/5g4bWdsxAwAJ

   bias the atom encoding for the code for T,  [<my own brilliant idea]
   this way, the word 1 means 30bit 0 + 2bit 01 :: the symbol T
        and, the word 0  ::   30bit 0 + 2bit 00 :: the list NIL
                 word 5  ::   30bit 1 + 2bit 01 :: the symbol NIL
                 word 9  ::   30bit 2 + 2bit 01 :: the symbol SETQ
                 word 4  ::   30bit 1 + 2bit 00 :: the list at address 1
                 word 8  ::   30bit 2 + 2bit 00 :: the list at address 2

   tag  00 : list   : val is "pointer" to 2-cell pair
        01 : atom   : val is encoded as index into atom list which holds (string) lists
        10 : object : val is "pointer" to an object union
        11 : number : val is a 30bit fixnum                [^minilisp ^lisp500]

   each word is interpreted as a 2 bit tag
   and a sizeof(int)*8-2 bit signed number. 32bit int :: 30bit + 2bit tag [^minilisp]

  manipulating lists.
  val() of course returns an int i which indexes `int *m;`
                             ^^^^^:our "pointer"  ^^^^^^:the memory
  using the commutativity of indexing in C: m[i] == *(m + i) == i[m]
 */
