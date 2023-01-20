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
#define defun(NAME,ARGS,...) \
  int NAME ARGS { IFDEBUG(2, fprintf(stderr, "%s ", __func__)); return __VA_ARGS__; }

struct state {
    int*m,*n,msz, /*memory next mem-size*/
	env,      /* global environment for REPL, modified by SET, SETQ and DEFUN */
	atoms;    /* head of atom list */
	char linebuf[BUFSIZ];
	char *inputptr;
} global = { .linebuf = { 0 }, .inputptr = global.linebuf };

#define INIT_ALL     	 INIT_MEMORY, INIT_ATOM_LIST, INIT_ENVIRONMENT
#define INIT_MEMORY  	 global.n=16+(global.m=calloc(global.msz=getpagesize(),sizeof(int)))
#define ATOM_PROPS(x)    list(TO_STRING(x))
#define INIT_ATOM_LIST   global.atoms = list(ATOMSEEDS(ATOM_PROPS))
#define INIT_ENVIRONMENT global.env = list( 	                   \
					  list(T, T),              \
					  list(NIL, nil),          \
    					  SUBR_LIST(make_subr),    \
    					  SUBR2_LIST(make_subr2),  \
					  FSUBR_LIST(make_fsubr1), \
					  FSUBR2_LIST(make_fsubr2) \
				      )
#define make_subr(X,Y)   list(atom(#X),subr1(Y))
#define make_subr2(X,Y)  list(atom(#X),subr2(Y))
#define make_fsubr1(X,Y) list(atom(#X),fsubr1(Y))
#define make_fsubr2(X,Y) list(atom(#X),fsubr2(Y))
#define SUBR_LIST(X) \
  X(CAAR,caar), X(CDAR,cdar), X(CADR,cadr), X(CDDR,cddr), \
  X(CAAAR,caaar), X(CDAAR,cdaar), X(CADAR,cadar), X(CDDAR,cddar), \
  X(CAADR,caadr), X(CDADR,cdadr), X(CADDR,caddr), X(CDDDR,cdddr), \
  X(LENGTH,length), X(PRNC,prnc)
#define SUBR2_LIST(X) X(SET,set)
#define FSUBR_LIST(X) X(READ,read_), X(READCH,readch)
#define FSUBR2_LIST(X) X(SETQ,set)

enum { TAGCONS, TAGATOM, TAGOBJ, TAGNUM,  TAGBITS = 2, TAGMASK = (1U<<TAGBITS)-1 };
defun(  val,  (x),x>>TAGBITS)
defun(  tag,  (x),x&TAGMASK)
defun(number, (x),x<<TAGBITS|TAGNUM)
defun(object, (x),x<<TAGBITS|TAGOBJ)
enum objecttag {SUBR, FSUBR, SUBR2, FSUBR2, STRING};
union object {int tag;
      struct {int tag; int funccode; } f;
      struct {int tag; int stroffset; } s;
};
#define MAX_FUNCTIONS 30
typedef int function();
function *ftab[MAX_FUNCTIONS];
int num_functions;

defun(objptr, (union object*p,union object o),*p=o,object((int*)p-global.m))
union object*newobjptr(void*p){return
    global.n+=(sizeof(union object)+sizeof*global.n-1)/sizeof*global.n,p;}
union object*ptrobj(x){return(void*)(global.m+val(x));}
defun(findfunc,(int(*f)(),int n),n==num_functions?(ftab[num_functions]=f,num_functions++):
  f==ftab[n]?n:findfunc(f,n+1))
defun(objfunc,(enum objecttag t,int(*f)()),
    objptr(newobjptr(global.n),(union object){.f={.tag=t,.funccode=findfunc(f,0)}}) )
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
defun(objstr, (char*s),
  objptr(newobjptr(global.n),
         (union object){.s={.tag=STRING,.stroffset=((int*)s)-global.m}}))
defun(string, (char*s),objstr(newstrptr(strcpy((char*)global.n,s))))
defun(findstr,(s,slist,i)char*s;,
      !strcmp((char*)(global.m+ptrobj(caar(slist))->s.stroffset),s)?i:
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
defun(rplaca,(x,y),consp(x)?(val(x)[global.m]=y),x:x)
defun(rplacd,(x,y),consp(x)?(val(x)[global.m+1]=y),x:x)
defun(car,   (x),  consp(x)?val(x)[global.m]:0)
defun(cdr,   (x),  consp(x)?val(x)[global.m+1]:0)
defun(caar,  (x),     car(car(x)))
defun(cdar,  (x),     cdr(car(x)))
defun(cadr,  (x),     car(cdr(x)))
defun(cddr,  (x),     cdr(cdr(x)))
defun(caaar, (x),    caar(car(x)))
defun(cdaar, (x),    cdar(car(x)))
defun(cadar, (x),    cadr(car(x)))
defun(cddar, (x),    cddr(car(x)))
defun(caadr, (x),    caar(cdr(x)))
defun(cdadr, (x),    cdar(cdr(x)))
defun(caddr, (x),    cadr(cdr(x)))
defun(cdddr, (x),    cddr(cdr(x)))
defun(caddar,(x),   caddr(car(x)))
defun(cadddr,(x),   caddr(cdr(x)))

defun(eq,   (x,y),x==y) 	/*auxiliary functions [^jmc]*/
defun(ff,   (x),atomp(x)?x:ff(car(x))) /* find first atom */
defun(subst,(x,y,z),atomp(z)?(eq(z,y)?x:z): cons(subst(x,y,car(z)),subst(x,y,cdr(z))))
defun(equal,(x,y),(atomp(x)&&atomp(y)&&eq(x,y))
        ||(consp(x)&&consp(y)&&equal(car(x),car(y))&&equal(cdr(x),cdr(y)))) /*lists equal?*/
defun(null, (x),listp(x)&&val(x)==0) /*list == NIL?*/
defun(subsq,(x,y,z),null(z)?nil:atomp(z)?(eq(y,z)?x:z):car(z)==QUOTE?z:
      cons(subsq(x,y,car(z)),subsq(x,y,cdr(x))))

defun(append,(x,y),null(x)?y:cons(car(x),append(cdr(x),y))) 	/*association lists [^jmc]*/
defun(among, (x,y),!null(y)&&(equal(x,car(y))||among(x,cdr(y))))
defun(pair,  (x,y),null(x)&&null(y)?nil:consp(x)&&consp(y)?
      cons(list(car(x),car(y)),pair(cdr(x),cdr(y))):0)
defun(assoc, (x,y),eq(caar(y),x)?cadar(y):null(y)?nil:assoc(x,cdr(y)))
defun(rassoc,(x,y),eq(cdar(y),x)?car(y):null(y)?nil:rassoc(x,cdr(y)))
defun(assocpair,(x,y),eq(caar(y),x)?car(y):null(y)?nil:assocpair(x,cdr(y)))
defun(seta,   (a,x,y),(a?rplacd(a,list(y)):
      (global.env=append(list(list(x,y),global.env)))),y)
defun(set,      (x,y),seta(assocpair(x,global.env),x,y))
defun(maplist,  (x,f),null(x)?nil:cons(apply(f,x,nil),maplist(cdr(x),f)))
defun(length,   (y),number(null(y)||!listp(y)?0:1+val(length(cdr(y)))))
defun(mapcar,   (x,f),null(x)?nil:cons(apply(f,car(x),nil),mapcar(cdr(x),f)))

defun(sub2,  (x,z),null(x)?z:eq(caar(x),z)?cadar(x):sub2(cdr(x),z))
defun(sublis,(x,y),atomp(y)?sub2(x,y):cons(sublis(x,car(y)),sublis(x,cdr(y))))
defun(apply, (f,x,p),eval(cons(f,appq(x)),p))
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
defun(evobjo,(o,e,a)union object o;, o.tag== SUBR ? ftab[o.f.funccode](eval(cadr(e),a)):
                                     o.tag==FSUBR ? ftab[o.f.funccode](cdr(e)):
			             o.tag== SUBR2? ftab[o.f.funccode](eval(cadr(e),a), eval(caddr(e),a)):
                                     o.tag==FSUBR2? ftab[o.f.funccode](cadr(e),caddr(e)): e)
defun(evobj, (e,a),evobjo(*ptrobj(car(e)),e,a))

defun(prn,      (x,f)FILE*f;,
      (!f?f=stdout:0),
      atomp(x)  ?prnatom(x,f)                : /*print with dot-notation [^stackoverflow]*/
      stringp(x)?prnstring(x,f)              :
      numberp(x)?fprintf(f,"%d ",val(x))     :
      objectp(x)?fprintf(f,"OBJ_%X ",val(x)*sizeof(int)) :
      consp(x)  ?fprintf(f,"( "),prn(car(x),f),fprintf(f,". "),prn(cdr(x),f),fprintf(f,") "):
	         fprintf(f,"NIL "))
defun(prnstring,(x,f)FILE*f;,(!f?f=stdout:0),fprintf(f,"\"%s\" ", (char*)(global.m+ptrobj(x)->s.stroffset)))
defun(prnatomx, (x,atoms,f)FILE*f;,
  (!f?f=stdout:0),x?prnatomx(x-1,cdr(atoms),f):fprintf(f,"%s ", (char*)(global.m+ptrobj(caar(atoms))->s.stroffset)))
defun(prnatom0, (x,f)FILE*f;,(!f?f=stdout:0),prnatomx(x,global.atoms,f))
defun(prnatom,  (unsigned x,FILE*f),(!f?f=stdout:0),prnatom0(x>>TAGBITS,f))
defun(prnlstn,  (x,f)FILE*f;,(!f?f=stdout:0),!listp(x)?prn(x,f):
      ((car(x)?prnlst(car(x),f):0),(cdr(x)?prnlstn(cdr(x),f):0)))
defun(prnlst,   (x,f)FILE*f;,(!f?f=stdout:0),!listp(x)?prn(x,f):
      (fprintf(f,LPAR),(car(x)?prnlst (car(x),f):0),
                       (cdr(x)?prnlstn(cdr(x),f):0),fprintf(f,RPAR)))
defun(prnc, (x),printf("%c",val(x)))

char*adjust_case(char*buf){ for(char*p=buf;*p;p++)*p=toupper(*p); return buf; }
char*rdatom(char**p,char*buf,int i){return
    memcpy(buf,*p,i),buf[i]=0,(*p)+=i,adjust_case(buf);}
defun(rdlist,(p,z,u)char**p;,u==atom(RPAR)?z:append(cons(u,nil),rdlist(p,z,rd(p))))
defun(rdnum, (p,v)char**p;,*++*p>='0'&&**p<='9'?rdnum(p,v*10+**p-'0'):v)
defun(rdbuf, (char**p,char*buf,char c),c?(c==' '        ?(++(*p),rd(p)                ):
			                  c==*RPAR      ?(++(*p),atom(RPAR)           ):
				          c==*LPAR      ?(++(*p),rdlist(p,nil,rd(p))  ):
			                  c>='0'&&c<='9'?        number(rdnum(p,c-'0')):
					  c=='-'&&(*p)[1]>='0'&&(*p)[1]<='9'?
					                            number(-rdnum(p,0)):
					        atom(rdatom(p,buf,strcspn(*p,"() \t"))) ):0)
defun(rd,    (char**p),rdbuf(p,(char[ATOMBUFSZ]){""},**p))
defun(check_input,(),!*global.inputptr?global_readline():1)
defun(readch,(),check_input()?number(*global.inputptr++):QUIT)
defun(read_,(),check_input()?rd(&global.inputptr):QUIT)

defun(prompt,(),printf(">"), fflush(0))
defun(readline,(char *s,size_t sz), (prompt(),fgets(s,sz,stdin)&&((s[strlen(s)-1]=0),1)))
defun(global_readline,(),
      global.inputptr=global.linebuf,readline(global.linebuf,sizeof(global.linebuf)))
defun(repl,(x), (x=read_())==QUIT?0:
		    (IFDEBUG(0,prn(x,stdout),fprintf(stdout,"\n"),
                               prnlst(x,stdout),fprintf(stdout,"\n")),
		     x=eval(x,global.env),
		     IFDEBUG(0,dump(x,stdout)),
		     prnlst(x,stdout),printf("\n"),
		     repl()))

defun(debug_global,(),
		prnlst(global.atoms,stderr),
		prnlst(global.env,stderr),
		fflush(stderr)
)
defun(init,(), INIT_ALL,
               IFDEBUG(2, debug_global()),
	       repl())

int main( int argc, char *argv[] ){
    assert((-1 & 3) == 3); /* that ints are 2's complement */
    assert((-1 >> 1) < 0); /* that right shift keeps sign */
    int r = argc == 1  ? init()  : (loadmem(),repl());
    dumpmem();
    return  r;
}

struct record { int used, size, env, atoms; };

int dumpmem(){
    struct record record = { global.n-global.m, global.msz, global.env, global.atoms };
    memcpy( global.m, &record, sizeof record );
    FILE *f = fopen( "mem.dump","w" );
    fwrite( global.m, sizeof *global.m, global.n-global.m, f );
    fclose( f );
    debug_global();
}

int loadmem(){
    FILE *f = fopen( "mem.dump", "r" );
    struct record record;
    fread( &record, sizeof record, 1, f );
    global.n = record.used + (global.m = calloc( global.msz = record.size, sizeof(int) ));
    global.env = record.env;
    global.atoms = record.atoms;
    fread( ((char*)global.m) + sizeof record, sizeof(int), record.used, f );
    fclose( f );
}

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
