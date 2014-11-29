/* sexp.c - an "implicit int" tiny lisp.
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
 */
#include<assert.h>
#include<math.h>
#include<signal.h>
#include<stdarg.h>
#include<stdio.h>
#include<stdlib.h>
#include<string.h>
#include<unistd.h>
#include"ppnarg.h"   /*https://github.com/luser-dr00g/sexp.c/blob/master/ppnarg.h*/
#define R return
#define defun(NAME,ARGS,...) \
    int NAME ARGS { return __VA_ARGS__; }

/* memory is organized as a large array of ints
   each int is a "word" and memory can be accessed by
       m[int]
   the int here is a cursor called herein a "pointer" (<-- always in quotes)
   [^codegolf jar2]*/
int*m,*n,msz; /*memory next mem-size*/

/* global environment for REPL and DEFUN */
int env;

/* each word is interpreted as a 2 bit tag
   and a sizeof(int)*8-2 bit signed number. 32bit int :: 30bit + 2bit tag [^minilisp]*/
enum { TAGMASK = 03, TAGBITS = 2, TAGCONS = 0, TAGATOM, TAGOBJ, TAGNUM };
defun(tag,(x),x&TAGMASK)
defun(val,(x),x>>TAGBITS)

/* bias the alphabet at the ascii code for T,  [<my own brilliant idea]
   this way, the word 1 means 30bit 0 + 2bit 01 :: the symbol T
        and, the word 0  ::   30bit 0 + 2bit 00 :: the list NIL
                 word 5  ::   30bit 1 + 2bit 01 :: the symbol U
                 word 9  ::   30bit 2 + 2bit 01 :: the symbol V
                 word 4  ::   30bit 1 + 2bit 00 :: the list at address 1
                 word 8  ::   30bit 2 + 2bit 00 :: the list at address 2

   tag  00 : list   : val is "pointer" to 2-cell pair
        01 : atom   : val is encoded as 5 6-bit codes packed low-to-high,
                                        with the first code biased at `enc('T')` (ie. 20)
        10 : object : val is "pointer" to an object union
        11 : number : val is a 30bit fixnum
   [^minilisp]
   ____________
   21111111 111_____ ___
   09876543 21098765 32101234 56
   ABCDEFGH IJKLMNOP QRSTUVWX YZ

   6bit code
   1 2 3 4  5  6
   2 4 8 16 32 64
           26 52

   0          111111 11112222 22222233 33333333 44444444 44555555 5555 6666
   01234567 89012345 67890123 45678901 23456789 01234567 89012345 6789 0123  <- general position

  " ABCDEFG HIJKLMNO PQRSTUVW XYZ_abcd efghijkl mnopqrst uvwxyz)1 2345 6789"

   -------- -------- ----
   21111111 111          0          11 11111111 22222222 22333333 3333 4444
   09876543 21098765 43210123 45678901 23456789 01234567 89012345 6789 0123  <- first char
   44444455 55555555 6666
   45678901 23456789 0123
*/
#define ENCODING " ABCDEFGHIJKLMNOPQRSTUVWXYZ_abcdefghijklmnopqrstuvwxyz)123456789"
#define ALPHA "T"
#define NIL   (0)
#define T atom(ALPHA)
defun(enc,(x),strchr(ENCODING,x)-ENCODING)
int atom(char *x){char*p=x;                  /*constructors*/
    //if (!strchr(ENCODING,*x)) R 0;
    //printf("atom(%s)=",x);
    unsigned int r;
    if (!*p) r=(enc(' ')+44)%64; /* ie. unsigned -20 (%64) but keeping everything positive. */
    else {
        r=(enc(*p)+44)%64;
        while(*++p)
            if (strchr(ENCODING,*p) && !strchr("()",*p))
                r|=(enc(*p)<<(6*(p-x)));
    }
    r= (r<<TAGBITS)|TAGATOM;
    //printf("%u\n", r);
    R r;
}
defun(number,(x),x<<TAGBITS|TAGNUM)
defun(object,(x),x<<TAGBITS|TAGOBJ)
enum { SUBR = 1, FSUBR, SUBR2, FSUBR2 };
union object { int tag;
      struct { int tag; int (*f)(); } f1;
      struct { int tag; int (*f)(); } s1;
      struct { int tag; int (*f)(); } f2;
      struct { int tag; int (*f)(); } s2;
};
subr1(int(*f)()){
    union object *o = (union object *)n; n+=(int)ceil((double)sizeof*o/sizeof*n);
    o->s1.tag = SUBR;
    o->s1.f = f;
    return object((int*)o-m);
}
fsubr1(int(*f)()){
    union object *o = (union object *)n; n+=(int)ceil((double)sizeof*o/sizeof*n);
    o->f1.tag = FSUBR;
    o->f1.f = f;
    return object((int*)o-m);
}
subr2(int(*f)()){
    union object *o = (union object *)n; n+=(int)ceil((double)sizeof*o/sizeof*n);
    o->s2.tag = SUBR2;
    o->s2.f = f;
    return object((int*)o-m);
}
fsubr2(int(*f)()){
    union object *o = (union object *)n; n+=(int)ceil((double)sizeof*o/sizeof*n);
    o->f2.tag = FSUBR2;
    o->f2.f = f;
    return object((int*)o-m);
}

defun(  listp,(x),tag(x)==TAGCONS) /* predicates */
defun(  atomp,(x),tag(x)==TAGATOM)
defun(objectp,(x),tag(x)==TAGOBJ)
defun(numberp,(x),tag(x)==TAGNUM)
defun(  consp,(x),x&&listp(x))

/*manipulating lists.
  val() of course returns an int i which indexes `int *m;`
                          our "pointer"           the memory
  using the commutativity of indexing in C: m[i] == *(m + i) == i[m] */
defun(cons,(x,y),*n++=x,*n++=y,(n-m)-2<<TAGBITS|TAGCONS)
defun(rplaca,(x,y),consp(x)?val(x)[m]=y:0)
defun(rplacd,(x,y),consp(x)?val(x)[m+1]=y:0)
defun(car,(x),consp(x)?val(x)[m]:0)
defun(cdr,(x),consp(x)?val(x)[m+1]:0)
defun(caar,(x),car(car(x)))
defun(cadr,(x),car(cdr(x)))
defun(cddr,(x),cdr(cdr(x)))
defun(cadar,(x),car(cdr(car(x))))
defun(caddr,(x),car(cdr(cdr(x))))
defun(cdddr,(x),cdr(cdr(cdr(x))))
defun(caddar,(x),car(cdr(cdr(car(x)))))
defun(cadddr,(x),car(cdr(cdr(cdr(x)))))

defun(eq,(x,y),x==y)
defun(ff,(x),atomp(x)?x:ff(car(x))) /* find first atom */
defun(subst,(x,y,z),atomp(z)?(eq(z,y)?x:z): cons(subst(x,y,car(z)),subst(x,y,cdr(z))))
defun(equal,(x,y),(atomp(x)&&atomp(y)&&eq(x,y))
        ||(consp(x)&&consp(y)&&equal(car(x),car(y))&&equal(cdr(x),cdr(y)))) /*lists equal?*/
defun(null,(x),listp(x)&&val(x)==0) /*list == NIL?*/

/*build lists
  list() variadic macro uses ppnarg.h to count the arguments and call listn
https://github.com/luser-dr00g/sexp.c/blob/master/ppnarg.h
  listn() variadic function copies n (int) arguments to memory and call lista
  lista() constructs a list of n elements from pointer to memory
 */
int lista(int c,int*a){int z=NIL;for(;c;)z=cons(a[--c],z);R z;}
int listn(int c,...){va_list a;int*z=n;
    va_start(a,c);for(;c--;)*n++=va_arg(a,int);va_end(a);
    c=n-z;R lista(c,z);}
#define list(...) listn(PP_NARG(__VA_ARGS__),__VA_ARGS__)

append(x,y){R null(x)?y:cons(car(x),append(cdr(x),y));}  /*association lists [^jmc]*/
among(x,y){R!null(y)&&equal(x,car(y))||among(x,cdr(y));}
pair(x,y){R null(x)&&null(y)?NIL:consp(x)&&consp(y)?
        cons(list(car(x),car(y)),pair(cdr(x),cdr(y))):0;}
assoc(x,y){R eq(caar(y),x)?cadar(y):null(y)?0:assoc(x,cdr(y));}

sub2(x,z){R null(x)?z:eq(caar(x),z)?cadar(x):sub2(cdr(x),z);}  /*the universal function eval() [^jmc]*/
sublis(x,y){R atomp(y)?sub2(x,y):cons(sublis(x,car(y)),sublis(x,cdr(y)));}
apply(f,args){R eval(cons(f,appq(args)),NIL);}
appq(m){R null(m)?NIL:cons(list(atom("QUOTE"),car(m)),appq(cdr(m)));}
eval(e,a){
    prnlst(e); printf("\n");
    R numberp(e)?e:
    atomp(e)?assoc(e,a):
    atomp(car(e))?(
                   eq(car(e),atom("QUOTE"))?cadr(e):
                   eq(car(e),atom("ATOM"))? atomp(eval(cadr(e),a)):
                   eq(car(e),atom("EQ"))?   eval(cadr(e),a)==eval(caddr(e),a):
                   eq(car(e),atom("COND"))? evcon(cdr(e),a):
                   eq(car(e),atom("CAR"))?  car(eval(cadr(e),a)):
                   eq(car(e),atom("CDR"))?  cdr(eval(cadr(e),a)):
                   eq(car(e),atom("CONS"))? cons(eval(cadr(e),a),eval(caddr(e),a)):
                   eq(car(e),atom("DEFUN"))?
                       (a=list(atom("LABEL"),cadr(e),list(atom("LAMBD"),caddr(e),cadddr(e))),
                       env=append(env, list(list(cadr(e),a))), a):
        eval(cons(assoc(car(e),a),cdr(e)),a)):
        //eval(cons(assoc(car(e),a),evlis(cdr(e),a)),a) ): /*^rootsoflisp*/
    objectp(car(e))?evobj(e,a):
    eq(caar(e),atom("LABEL"))? /*LABEL*/
        eval(cons(caddar(e),cdr(e)),cons(list(cadar(e),car(e)),a)):
    eq(caar(e),atom("LAMBD"))? /*LAMBDA with 5-char atoms */
        eval(caddar(e),append(pair(cadar(e),evlis(cdr(e),a)),a)):
    0;}
evcon(c,a){R eval(caar(c),a)?eval(cadar(c),a):evcon(cdr(c),a);}
evlis(m,a){R null(m)?NIL:cons(eval(car(m),a),evlis(cdr(m),a));}
evobj(e,a){
    union object o = *(union object*)(m+val(car(e)));
    switch(o.tag){
    default: R 0;
    case SUBR: R o.s1.f(eval(cadr(e),a));
    case FSUBR: R o.f1.f(cdr(e));
    case SUBR2: R o.s2.f(eval(cadr(e),a),eval(caddr(e),a));
    case FSUBR2: R o.f2.f(cadr(e),caddr(e));
    }
}
maplist(x,f){R null(x)?NIL:cons(apply(f,x),maplist(cdr(x),f));}

assocpair(x,y){R eq(caar(y),x)?car(y):null(y)?0:assocpair(x,cdr(y));}
set(x,y){
    int a=assocpair(x,env);
    if (a)
        rplacd(a,list(y));
    else
        env=append(env,list(list(x,y)));
    R y;
}

prnatom(unsigned x){
    int i;
    unsigned int a;
    x>>=2;
    a=x&0x3f;
    a=(a + 20) % 64;  /* undo the bias at 'T' */
    for(i=0;i<6;i++) {
        //printf("%u:%c ", a, ENCODING[a]);
        if (ENCODING[a]==' ') break;
        printf("%c",ENCODING[a]);
        x>>=6;
        a=x&0x3f;
    }
    printf(" ");
}
prn(x){atomp(x)?prnatom(x)/*printf("%c ",val(x)+ALPHA)*/: /*print with dot-notation [^stackoverflow]*/
    numberp(x)?printf("%d ",val(x)):
    objectp(x)?printf("OBJ %d ",val(x)):
    consp(x)?printf("( "),prn(car(x)),printf(". "),prn(cdr(x)),printf(") "):
    printf("NIL ");}

prnlst(x){x==NIL?printf("NIL"):!consp(x)?prn(x):printf("( "),prnrem(x);} /*print with list-notation [^stackoverflow]*/
prnrem(x){if(x==NIL)R;// printf(")0 ");
    if(car(x)!=NIL)prn(car(x));
    else R;
    null(cdr(x))?printf(") "):
    !listp(cdr(x))?prn(cdr(x)),printf(") "):
    prnlst(car(cdr(x))),prnrem(cdr(cdr(x)))/*,printf(") ")*/;}

#define LPAR "("
#define RPAR ")"
rd(char**p){int i,t,u,v,z; /*read a list [^stackoverflow]*/
    char boffo[6] = "";
    if(!(**p))R 0;
    if(**p==' ')R++(*p),rd(p);
    if(**p==*RPAR)R++(*p),atom(RPAR);
    if(**p==*LPAR){++(*p);
        z=NIL;
        u=rd(p);
        if (u!=atom(RPAR)){
            z=cons(u,NIL);
            while(u=rd(p),!eq(u,atom(RPAR)))u=cons(u,NIL),z=append(z,u);
        }
        R z;}
    if(**p>='0'&&**p<='9'){
        int v = **p - '0';
        while(*++*p>='0'&&**p<='9') v*=10, v+=**p-'0';
        R number(v);
        //R++*p,number((*p)[-1]-'0');
    }
    for(i=0;i<-1+sizeof boffo;i++){
        if (isspace((*p)[i]) || (*p)[i]=='\0') break;
        if (!strchr(ENCODING,(*p)[i])) break;
        if (strchr("()",(*p)[i])) break;
        boffo[i]=(*p)[i];
    }
    boffo[i]='\0';
    (*p)+=i;
    R atom(boffo);
}

void fix(x){signal(SIGSEGV,fix);sbrk(sizeof(int)*(msz*=2));} /*grow memory in response to memory-access fault*/
int main(){
    //char *s;
    char s[BUFSIZ];
    char *p;
    int x;

    assert((-1>>1)==-1);	/*require 2's-complement and right-shift must be sign-preserving */
    printf("");  /* exercise stdio so it (hopefully) malloc's what it needs before we take sbrk() */
    snprintf(NULL, 0, "%c%d%f", 'x', 42, 72.27);
    n=m=sbrk(sizeof(int)*(msz=getpagesize()));*n++=0;*n++=0; /*initialize memory and begin at cell 2*/
    //signal(SIGSEGV,fix); /*might let it run longer, obscures problems*/

    env = list(
            list(atom("CAAR"),subr1(caar)),
            list(atom("CADR"),subr1(cadr)),
            list(atom("CDDR"),subr1(cddr)),
            list(atom("CADAR"),subr1(cadar)),
            list(atom("CADDR"),subr1(caddr)),
            list(atom("CDDDR"),subr1(cdddr)),
            list(atom("SET"),subr2(set)),
            list(atom("SETQ"),fsubr2(set))
            );

    while(1) {
        printf("env:\n"); prnlst(env); printf("\n");
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

    R 0;
}
