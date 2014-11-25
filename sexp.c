/*cf.
http://www.ioccc.org/1989/jar.2.c
http://leon.bottou.org/projects/minilisp
http://www.jsoftware.com/jwiki/Essays/Incunabulum
http://www-formal.stanford.edu/jmc/recursive/recursive.html
http://www.paulgraham.com/rootsoflisp.html
http://codegolf.stackexchange.com/questions/284/write-an-interpreter-for-the-untyped-lambda-calculus/3290#3290
http://stackoverflow.com/questions/18096456/why-wont-my-little-lisp-quote
http://www.cse.sc.edu/~mgv/csce330f13/micromanualLISP.pdf
 */
#include<assert.h>
#include<signal.h>
#include<stdarg.h>
#include<stdio.h>
#include<stdlib.h>
#include<string.h>
#include<unistd.h>
#include"ppnarg.h"
#define R return

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
tag(x){R x&3;}
val(x){R x>>2;}

/* bias the alphabet at the ascii code for T,  [<my own brilliant idea]
   this way, the word 1 means 30bit 0 + 2bit 01 :: the symbol T
        and, the word 0  ::   30bit 0 + 2bit 00 :: the list NIL
                 word 5  ::   30bit 1 + 2bit 01 :: the symbol U
                 word 9  ::   30bit 2 + 2bit 01 :: the symbol V
                 word 4  ::   30bit 1 + 2bit 00 :: the list at address 1
                 word 8  ::   30bit 2 + 2bit 00 :: the list at address 2

   tag  00 : list   : val is "pointer" to 2-cell pair
        01 : atom   : val + 'T' is an ascii code
        10 : object
        11 : number
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

  " ABCDEFG HIJKLMNO PQRSTUVW XYZ_ahcd efghijkl mnopqrst uvwxyz01 2345 6789"

   -------- -------- ----
   21111111 111          0          11 11111111 22222222 22333333 3333 4444
   09876543 21098765 43210123 45678901 23456789 01234567 89012345 6789 0123  <- first char
   44444455 55555555 6666
   45678901 23456789 0123
*/
#define ENCODING " ABCDEFGHIJKLMNOPQRSTUVWXYZ_ahcdefghijklmnopqrstuvwxyz()23456789"
#define ALPHA "T"
#define NIL   (0)
#define T atom(ALPHA)
enc(x){R strchr(ENCODING,x)-ENCODING;}
atom(char *x){char*p=x;
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
    r= (r<<2)|1;
    //printf("%u\n", r);
    R r;
}  /*constructors*/
number(x){R(x<<2)|3;}
listp(x){R tag(x)==0;}       /*predicates*/
atomp(x){R tag(x)==1;}
objectp(x){R tag(x)==2;}
numberp(x){R tag(x)==3;}
consp(x){R x&&listp(x);}

/*manipulating lists.
  val() of course returns an int i which indexes `int *m;`
                          our "pointer"           the memory
  using the commutativity of indexing in C: m[i] == *(m + i) == i[m] */
car(x){R consp(x)?val(x)[m]:0;}
cdr(x){R consp(x)?val(x)[m+1]:0;}
caar(x){R car(car(x));}
cadr(x){R car(cdr(x));}
cddr(x){R cdr(cdr(x));}
cadar(x){R car(cdr(car(x)));}
caddr(x){R car(cdr(cdr(x)));}
cdddr(x){R cdr(cdr(cdr(x)));}
caddar(x){R car(cdr(cdr(car(x))));}
cadddr(x){R car(cdr(cdr(cdr(x))));}
cons(x,y){int z;R z=n-m,*n++=x,*n++=y,z<<2;} /*allocate cells for x and y and return "pointer"*/
rplaca(x,y){R consp(x)?val(x)[m]=y:0;}
rplacd(x,y){R consp(x)?val(x)[m+1]=y:0;}

eq(x,y){R atomp(x)&&atomp(y)?x==y:0;}  /*atoms eq?*/
ff(x){R atomp(x)?x:ff(car(x));} /*find first*/
subst(x,y,z){R atomp(z)?(eq(z,y)?x:z):
    cons(subst(x,y,car(z)),subst(x,y,cdr(z)));}
equal(x,y){R (atomp(x)&&atomp(y)&&eq(x,y))
    ||(consp(x)&&consp(y)&&equal(car(x),car(y))&&equal(cdr(x),cdr(y)));}  /*lists equal?*/
null(x){R listp(x)&&(val(x)==0);}  /*list == NIL?*/

/*build lists
  list() variadic macro uses ppnarg.h to count the arguments and call listn
  listn() variadic function copies n (int) arguments to memory and call lista
  lista() constructs a list of n elements from pointer to memory
 */
lista(int c,int*a){int z=NIL;for(;c;)z=cons(a[--c],z);R z;}
listn(int c,...){va_list a;int*z=n;
    va_start(a,c);for(;c--;)*n++=va_arg(a,int);va_end (a);
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
eval(e,a){R numberp(e)?e:
    atomp(e)?assoc(e,a):
    atomp(car(e))?(
    /*QUOTE*/      eq(car(e),atom("QUOTE"))?cadr(e):
    /*ATOM*/       eq(car(e),atom("ATOM"))? atomp(eval(cadr(e),a)):
    /*EQ*/         eq(car(e),atom("EQ"))?   eval(cadr(e),a)==eval(caddr(e),a):
    /*COND*/       eq(car(e),atom("COND"))? evcon(cdr(e),a):
    /*CAR*/        eq(car(e),atom("CAR"))?  car(eval(cadr(e),a)):
    /*CDR*/        eq(car(e),atom("CDR"))?  cdr(eval(cadr(e),a)):
    /*CONS*/       eq(car(e),atom("CONS"))? cons(eval(cadr(e),a),eval(caddr(e),a)):
    /*DEFUN*/      eq(car(e),atom("DEFUN"))?
               (a=list(atom("LABEL"),cadr(e),list(atom("LAMBD"),caddr(e),cadddr(e))),
               env=append(env, list(list(cadr(e),a))),
               a):
        eval(cons(assoc(car(e),a),cdr(e)),a)): /*cf. Roots of Lisp*/
        //eval(cons(assoc(car(e),a),evlis(cdr(e),a)),a) ):
    eq(caar(e),atom("LABEL"))? /*LABEL*/
        eval(cons(caddar(e),cdr(e)),cons(list(cadar(e),car(e)),a)):
    eq(caar(e),atom("LAMBD"))? /*LAMBDA*/
        eval(caddar(e),append(pair(cadar(e),evlis(cdr(e),a)),a)):
    0;}
evcon(c,a){R eval(caar(c),a)?eval(cadar(c),a):evcon(cdr(c),a);}
evlis(m,a){R null(m)?NIL:cons(eval(car(m),a),evlis(cdr(m),a));}
maplist(x,f){R null(x)?NIL:cons(apply(f,x),maplist(cdr(x),f));}

/*
    car   cadr caddr cadddr
   (DEFUN NULL (X)   (EQ X NIL))
               cddr
    [DEFUN |]
          [NULL |]
               [|    |]
               [X.0] [EQ |]
                        [X |]
                          [NIL.0]

   NULL :: (LABEL NULL (LAMBDA (X)(EQ X NIL)))
           [LABEL |]
                 [NULL |]
                      [|.0]
                      [LAMBDA |]
                             [|    |]
                             [X.0] [EQ |]
                                      [X |]
                                        [NIL.0]
                        
   cadr(e) cons(atom("LABEL"),cons(cadr(e),cons(atom("LAMBDA"),cddr(e))))
>(LABEL NULL(LAMBD(X)(EQ X NIL)))
(LABEL NULL(LAMBD(X)(EQ X NIL)))
( LABEL . ( NULL . ( ( LAMBD . ( ( X . NIL ) . ( ( EQ . ( X . ( NIL . NIL ) ) ) . NIL ) ) ) . NIL ) ) ) 

   */

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

prnlst(x){x==NIL?0:!consp(x)?prn(x):printf("( "),prnrem(x);} /*print with list-notation [^stackoverflow]*/
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
        z=cons(u,NIL);
        while(u=rd(p),!eq(u,atom(RPAR)))u=cons(u,NIL),z=append(z,u);
        R z;}
    if(**p>='0'&&**p<='9')R++(*p),number(*((*p)-1)-'0');
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

void fix(x){signal(SIGSEGV,fix);sbrk(msz);msz*=2;} /*grow memory in response to memory-access fault*/
int main(){
    //char *s;
    char s[BUFSIZ];
    char *p;
    int x;

    assert((-1>>1)==-1);	/*require 2's-complement and right-shift must be sign-preserving */
    n=m=sbrk(sizeof(int)*(msz=getpagesize()));*n++=0;*n++=0; /*initialize memory and begin at cell 2*/
    //signal(SIGSEGV,fix); /*might let it run longer, obscures problems*/

    env = NIL;
    while(1) {
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
        printf("env:\n");
        prnlst(env); printf("\n");
    }

    R 0;
}
