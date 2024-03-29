
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

enum debugoptions {
  NONE  =  0,
  DUMP  =  1,
  ENV   =  2,
  SYMS =  4,
  FTAB  =  8,
  TRACE = 16,
  DEEP  = 32,
} debug =
#ifdef DEBUGMODE
  DEBUGMODE
#else
  NONE
#endif
  ;

#define nil   (0)
#define LPAR  "("
#define RPAR  ")"
#define SYMBUFSZ  10
#define defun_(MODE,NAME,ARGS,...) \
  int NAME ARGS { \
    if( MODE & debug )fprintf(stderr, "%s ", __func__); \
    return __VA_ARGS__; \
  }
#define defun(NAME,ARGS,...) defun_(TRACE,NAME,ARGS,__VA_ARGS__)
#define defdeep(NAME,ARGS,...) defun_(DEEP,NAME,ARGS,__VA_ARGS__)

struct state {
    int*m,*n,msz, /*memory next mem-size*/
	env,      /* global environment for REPL, modified by SET, SETQ and DEFUN */
	syms;    /* head of symbol list */
	char linebuf[BUFSIZ];
	char *inputptr;
} global = { .linebuf = { 0 }, .inputptr = global.linebuf };

#define INIT_ALL     	 INIT_MEMORY, INIT_SYMBOL_LIST, INIT_ENVIRONMENT
#define INIT_MEMORY  	 global.n=16+(global.m=calloc(global.msz=getpagesize(),sizeof(int)))
#define SYMBOL_PROPS(x)    list(TO_STRING(x))
#define INIT_SYMBOL_LIST   global.syms = list(SYMBOLSEEDS(SYMBOL_PROPS))
#define INIT_ENVIRONMENT global.env = list( list(T, T),              \
					list(NIL, nil),              \
				   EACH_FUNC(make_subr,make_subr2,make_fsubr1,make_fsubr2) \
				   )
#define EACH_SUBR(X) \
  X(CAAR,caar), X(CDAR,cdar), X(CADR,cadr), X(CDDR,cddr), \
  X(CAAAR,caaar), X(CDAAR,cdaar), X(CADAR,cadar), X(CDDAR,cddar), \
  X(CAADR,caadr), X(CDADR,cdadr), X(CADDR,caddr), X(CDDDR,cdddr), \
  X(LENGTH,length), X(PRNC,prnc)
#define EACH_SUBR2(X) X(SET,set)
#define EACH_FSUBR(X) X(READ,read_), X(READCH,readch)
#define EACH_FSUBR2(X) X(SETQ,set)
#define EACH_FUNC(X,Y,Z,W) \
  EACH_SUBR(X), \
  EACH_SUBR2(Y), \
  EACH_FSUBR(Z), \
  EACH_FSUBR2(W)

#define make_subr(X,Y)   list(symbol(#X),subr1(#X,Y))
#define make_subr2(X,Y)  list(symbol(#X),subr2(#X,Y))
#define make_fsubr1(X,Y) list(symbol(#X),fsubr1(#X,Y))
#define make_fsubr2(X,Y) list(symbol(#X),fsubr2(#X,Y))

enum { TAGCONS, TAGSYM, TAGOBJ, TAGNUM,  TAGBITS = 2, TAGMASK = (1U<<TAGBITS)-1 };
defdeep(  val,  (x),x>>TAGBITS)
defdeep(  tag,  (x),x&TAGMASK)
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
    global.n+=(sizeof(union object)+(sizeof*global.n)-1)/sizeof*global.n,p;}
union object*ptrobj(x){return(void*)(global.m+val(x));}
//defun(installfunction,(int(*f)(),int n),
//    n==num_functions?(ftab[num_functions]=f,num_functions++):
//    f==ftab[n]?n:
//    installfunction(f,n+1))
int installfunction(int(*f)(),int n){
  for( ; n<num_functions; ++n )
    if( f==ftab[n] )
      return n;
  if( n==MAX_FUNCTIONS ){
    fprintf(stderr, "error: num_functions==MAX_FUNCTIONS\n");
    exit(EXIT_FAILURE);
  }
  ftab[n] = f;
  ++num_functions;
  return n;
}
defun(objfunc,(enum objecttag t,int(*f)()),
    objptr(newobjptr(global.n), (union object){.f={.tag=t,.funccode=installfunction(f,0)}}) )
defun(newfunction,(char*n,int(*f)(),enum objecttag e,int x),
    x=objfunc(e,f),
    (debug & FTAB? fprintf(stderr, "%s=%d ", n, ptrobj(x)->f.funccode): 0),
    x)
defun( subr1,(char *n,int(*f)()),newfunction(n,f,SUBR,0))
defun(fsubr1,(char *n,int(*f)()),newfunction(n,f,FSUBR,0))
defun( subr2,(char *n,int(*f)()),newfunction(n,f,SUBR2,0))
defun(fsubr2,(char *n,int(*f)()),newfunction(n,f,FSUBR2,0))

int folda(int c,int*a,int(*f)(),int i){int z=i;for(;c;)z=f(a[--c],z); return z;}
int cons();
int lista(int c,int*a){ return folda(c,a,cons,nil); }
#define list(...) lista(PP_NARG(__VA_ARGS__),(int[]){__VA_ARGS__})

#define SYMBOLSEEDS(x) x(T),x(NIL),x(SETQ),x(QUOTE),x(ATOM),x(EQ),x(COND),\
		     x(CAR),x(CDR),x(LAMBDA),x(LABEL),x(CONS),x(DEFUN),x(QUIT)
#define symbol_enum(x) SYMBOL_##x
#define short_cut(x) x=symbol_enum(x)<<TAGBITS|TAGSYM
enum{SYMBOLSEEDS(symbol_enum),SYMBOLSEEDS(short_cut)};
#define TO_STRING(x) string(#x)
char*allocstr(char*s){return global.n+=(strlen(s)+1+(sizeof*global.n)-1)/sizeof*global.n,s;}
defun(objstr, (char*s),
  objptr(newobjptr(global.n),
         (union object){.s={.tag=STRING,.stroffset=((int*)s)-global.m}}))
defun(string, (char*s),objstr(allocstr(strcpy((char*)global.n,s))))
char*ptrstr(x){return (char*)(global.m+ptrobj(x)->s.stroffset);}
//defun(installsymbol,(s,slist,i)char*s;,
//      !strcmp((char*)(global.m+ptrobj(caar(slist))->s.stroffset),s)?i:
//      cdr(slist)?installsymbol(s,cdr(slist),i+1):(rplacd(slist,list(list(string(s)))),i+1))
int installsymbol(s,slist,i)char*s;{
  int last = slist;
  for( ; slist; ++i,last=slist,slist=cdr(slist) )
    if( !strcmp(ptrstr(caar(slist)),s) )
      return i;
  rplacd(last,list(list(string(s))));
  return i;
}
      
defun(encstr, (char*s),installsymbol(s,global.syms,0))
defun(symbol,   (char*s),encstr(s)<<TAGBITS|TAGSYM)

defun(  listp,(x),tag(x)==TAGCONS) 		/* predicates */
defun(symbolp,(x),tag(x)==TAGSYM)
defun(  atomp,(x),tag(x)!=TAGCONS)
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

defun( nthcdr,(x,i), i==0?x:nthcdr(cdr(x),i-1))
defun(    nth,(x,i), car(nthcdr(x,i)));
defun(lastcdr,(x), consp(cdr(x))?lastcdr(cdr(x)):x)
defun(   last,(x),   car(lastcdr(x)))

defun(eq,   (x,y),x==y) 	/*auxiliary functions [^jmc]*/
defun(ff,   (x),atomp(x)?x:ff(car(x))) /* find first atom */
defun(subst,(x,y,z),atomp(z)?(eq(z,y)?x:z): cons(subst(x,y,car(z)),subst(x,y,cdr(z))))
defun(equal,(x,y),(atomp(x)&&atomp(y)&&eq(x,y))
        ||(consp(x)&&consp(y)&&equal(car(x),car(y))&&equal(cdr(x),cdr(y)))) /*lists equal?*/
defun(null, (x),x==0) /*list == NIL?*/
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
    symbolp(e)?     assoc(e,a):
    symbolp(car(e))?(
	eq(car(e),QUOTE)? (debug&TRACE&&fprintf(stderr,"QUOTE ")), cadr(e):
	eq(car(e),ATOM)?  (debug&TRACE&&fprintf(stderr,"ATOM ")), atomp(eval(cadr(e),a)):
	eq(car(e),EQ)?    (debug&TRACE&&fprintf(stderr,"EQ ")), eval(cadr(e),a)==eval(caddr(e),a):
	eq(car(e),COND)?  (debug&TRACE&&fprintf(stderr,"COND ")), evcon(cdr(e),a):
	eq(car(e),CAR)?   (debug&TRACE&&fprintf(stderr,"CAR ")), car(eval(cadr(e),a)):
	eq(car(e),CDR)?   (debug&TRACE&&fprintf(stderr,"CDR ")), cdr(eval(cadr(e),a)):
	eq(car(e),CONS)?  (debug&TRACE&&fprintf(stderr,"CONS ")), cons(eval(cadr(e),a),eval(caddr(e),a)):
	eq(car(e),DEFUN)? (debug&TRACE&&fprintf(stderr,"DEFUN ")), (a=list(LABEL,cadr(e),list(LAMBDA,caddr(e),cadddr(e))),
	    			  global.env=append(global.env, list(list(cadr(e),a))), a): 
        eval(cons(assoc(car(e),a),cdr(e)),a)):
        //eval(cons(assoc(car(e),a),evlis(cdr(e),a)),a) ): /*<jmc ^rootsoflisp*/
    objectp(car(e))?    evobj(e,a):
    eq(caar(e),LABEL)?  (debug&TRACE&&fprintf(stderr,"LABEL ")), eval(cons(caddar(e),cdr(e)),cons(list(cadar(e),car(e)),a)):
    eq(caar(e),LAMBDA)? (debug&TRACE&&fprintf(stderr,"LABEL ")), eval(caddar(e),append(pair(cadar(e),evlis(cdr(e),a)),a)):
    0)
defun(evcon, (c,a),eval(caar(c),a)?eval(cadar(c),a):evcon(cdr(c),a))
defun(evlis, (m,a),null(m)?nil:cons(eval(car(m),a),evlis(cdr(m),a)))
defun(evobjo,(o,e,a)union object o;,
      o.tag== SUBR ? ftab[o.f.funccode](eval(cadr(e),a)):
      o.tag==FSUBR ? ftab[o.f.funccode](cdr(e)):
      o.tag== SUBR2? ftab[o.f.funccode](eval(cadr(e),a), eval(caddr(e),a)):
      o.tag==FSUBR2? ftab[o.f.funccode](cadr(e),caddr(e)):
      e)
defun(evobj, (e,a),evobjo(*ptrobj(car(e)),e,a))

defun(prn,      (x,f)FILE*f;, /*print with dot-notation [^stackoverflow]*/
      (!f?f=stdout:0),
      symbolp(x)  ?prnsymbol(x,f)                :
      stringp(x)?prnstring(x,f)              :
      numberp(x)?fprintf(f,"%d ",val(x))     :
      objectp(x)?prnobject(x,f) :
      consp(x)  ?fprintf(f,"( "),prn(car(x),f),fprintf(f,". "),
                                 prn(cdr(x),f),fprintf(f,") "):
	         fprintf(f,"NIL "))
//defun(prnobject,(x,f)FILE*f;,fprintf(f,"OBJ_%X ",val(x)*sizeof(int)))
int prnobject(x,f)FILE*f;{
  union object *u=ptrobj(x);
  fprintf(f,"%s:%d",
	  ((char*[]){"SUBR", "FSUBR", "SUBR2", "FSUBR2", "STRING"})[u->tag],
          u->f.funccode);
}
defun(prnstring,(x,f)FILE*f;,fprintf(f,"\"%s\" ", ptrstr(x)))
defun(prnsymbol, (x,f)FILE*f;,
  fprintf(f, "%s ", ptrstr(car(nth(global.syms,val(x))))))
defun(prnlstn,  (x,f)FILE*f;,!listp(x)?prn(x,f):
      ((car(x)?prnlst(car(x),f):0),(cdr(x)?prnlstn(cdr(x),f):0)))
defun(prnlst,   (x,f)FILE*f;,
      (!f?f=stdout:0),
      !listp(x)?prn(x,f):
      (fprintf(f,LPAR),(car(x)?prnlst (car(x),f):0),
                       (cdr(x)?prnlstn(cdr(x),f):0),fprintf(f,RPAR)))
defun(prnc, (x),printf("%c",val(x)))

char*adjust_case(char*buf){ for(char*p=buf;*p;p++)*p=toupper(*p); return buf; }
char*rdsymbol(char**p,char*buf,int i){return
    memcpy(buf,*p,i),buf[i]=0,(*p)+=i,adjust_case(buf);}
defun(rdlist,(p,z,u)char**p;,u==symbol(RPAR)?z:append(cons(u,nil),rdlist(p,z,rd(p))))
defun(rdnum, (p,v)char**p;,*++*p>='0'&&**p<='9'?rdnum(p,v*10+**p-'0'):v)
defun(rdbuf, (char**p,char*buf,char c),c?(c==' '        ?(++(*p),rd(p)                ):
					  c=='\''       ?(++(*p),list(QUOTE, rd(p))):
			                  c==*RPAR      ?(++(*p),symbol(RPAR)           ):
				          c==*LPAR      ?(++(*p),rdlist(p,nil,rd(p))  ):
			                  c>='0'&&c<='9'?        number(rdnum(p,c-'0')):
					  c=='-'&&(*p)[1]>='0'&&(*p)[1]<='9'?
					                            number(-rdnum(p,0)):
					        symbol(rdsymbol(p,buf,strcspn(*p,"() \t"))) ):0)
defun(rd,    (char**p),rdbuf(p,(char[SYMBUFSZ]){""},**p))
defun(check_input,(),!*global.inputptr?global_readline():1)
defun(readch,(),check_input()?number(*global.inputptr++):QUIT)
defun(read_,(),check_input()?rd(&global.inputptr):QUIT)

defun(prompt,(),printf(">"), fflush(0))
defun(readline,(char *s,size_t sz), (prompt(),fgets(s,sz,stdin)&&((s[strlen(s)-1]=0),1)))
defun(global_readline,(),
      global.inputptr=global.linebuf,readline(global.linebuf,sizeof(global.linebuf)))
defun(repl,(x), (x=read_())==QUIT?0:
		    ((debug & DUMP ? prn(x,stderr),fprintf(stderr,"\n"),
                               prnlst(x,stderr),fprintf(stderr,"\n"):0),
		     x=eval(x,global.env),
		     (debug & DUMP ? dump(x,stderr):0),
		     prnlst(x,stdout),printf("\n"),
		     repl()))

defun(debug_global,(),
		(debug & SYMS? fprintf(stderr,"\nsymbols: "), prnlst(global.syms,stderr):0),
		(debug & ENV? fprintf(stderr,"\nenv: "), prnlst(global.env,stderr):0),
		(debug & FTAB? fprintf(stderr,"\nftab: "), dumpftab( stderr ):0),
      		fprintf(stderr, "\n"), fflush(stderr))
defun(init,(), INIT_ALL,
               (debug & DUMP ? debug_global():0))

int main( int argc, char *argv[] ){
    char *memfile = "mem.dump";
    assert((-1 & 3) == 3); /* that ints are 2's complement */
    assert((-1 >> 1) < 0); /* that right shift keeps sign */
    int opt;
    int r,s;
    while( (opt = getopt( argc, argv, "d:rs" )) != -1 ){
      switch( opt ){
      case 'd': debug = atoi( optarg ); break;
      case 'r': r = loadmem( memfile ) && reinit_ftab(); break;
      case 's': s = 1; break;
      }
    }
    if( !r ) r = init();
    r = repl();
    if( s ) savemem( memfile );
    return  r;
}

struct record { int used, size, env, syms; };

int savemem( fn ) char *fn;{
    struct record record = { global.n-global.m, global.msz, global.env, global.syms };
    memcpy( global.m, &record, sizeof record );
    FILE *f = fopen( fn, "w" );
    fwrite( global.m, sizeof *global.m, global.n-global.m, f );
    fclose( f );
    if( debug & DUMP ) debug_global();
}

int loadmem( fn ) char *fn; {
    FILE *f = fopen( fn, "r" );
    if( !f ) return 0;
    struct record record;
    fread( &record, sizeof record, 1, f );
    global.n = record.used + (global.m = calloc( global.msz = record.size, sizeof(int) ));
    if( !global.m ) return 0;
    global.env = record.env;
    global.syms = record.syms;
    fread( ((char*)global.m) + sizeof record, sizeof(int), record.used, f );
    fclose( f );
    return 1;
}

#define reinit_func(X,Y) \
    /*ftab[num_functions++]=Y*/ \
    installfunction(Y,0), \
    (debug & FTAB? fprintf(stderr, "%s=%d ", #X, installfunction(Y,0)): 0) \
/**/

int reinit_ftab(){
  EACH_FUNC(reinit_func,reinit_func,reinit_func,reinit_func);
  return 1;
}

#define dump_func(X,Y) fprintf(fp, "%s=%d ", #Y, installfunction(Y,0))
int dumpftab(FILE*fp){
  EACH_FUNC(dump_func,dump_func,dump_func,dump_func);
}

int dump(int x,FILE*f){
    (debug & ENV ?fprintf(stderr,"env:\n"), prnlst(global.env,stderr), fprintf(stderr,"\n"):0);
    fprintf(f,"x: %d\n", x),
    //fprintf(f,"0: %o\n", x),
    fprintf(f,"0x: %x\n", x),
    fprintf(f,"tag(x): %d (%s)\n", tag(x), ((char*[]){"CONS","SYM","OBJ","NUM"})[tag(x)]),
    fprintf(f,"val(x): %d\n", val(x)),
    fprintf(f,"car(x): %d\n", car(x)),
    fprintf(f,"cdr(x): %d\n", cdr(x)),
    prn(x,f), fprintf(f,"\n");
}


/* sexp.c - an integer-coded tiny lisp.

  $ make test
  $ make test CFLAGS='-std=gnu99 -DDEBUGMODE=1 -Wno-implicit-function-declaration -Wno-implicit-int'

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
