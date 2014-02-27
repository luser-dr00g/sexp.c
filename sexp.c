/*cf.
http://www.ioccc.org/1989/jar.2.c
http://leon.bottou.org/projects/minilisp
http://www.jsoftware.com/jwiki/Essays/Incunabulum
http://www-formal.stanford.edu/jmc/recursive/recursive.html
http://www.paulgraham.com/rootsoflisp.html
http://codegolf.stackexchange.com/questions/284/write-an-interpreter-for-the-untyped-lambda-calculus/3290#3290
 */
#include<assert.h>
#include<signal.h>
#include<stdarg.h>
#include<stdio.h>
#include<stdlib.h>
#include<unistd.h>
#include"ppnarg.h"
#define R return
int*m,*n,msz;
tag(x){R x&3;}
val(x){R x>>2;}
#define ALPHA 'T'
#define NIL   (0)
#define T atom(ALPHA)
atom(x){R((x-ALPHA)<<2)|1;}
number(x){R(x<<2)|3;}
listp(x){R tag(x)==0;}
atomp(x){R tag(x)==1;}
objectp(x){R tag(x)==2;}
numberp(x){R tag(x)==3;}
consp(x){R x&&listp(x);}
car(x){R consp(x)?val(x)[m]:0;}
cdr(x){R consp(x)?val(x)[m+1]:0;}
caar(x){R car(car(x));}
cadr(x){R car(cdr(x));}
cadar(x){R car(cdr(car(x)));}
caddr(x){R car(cdr(cdr(x)));}
caddar(x){R car(cdr(cdr(car(x))));}
cons(x,y){int z;R z=n-m,*n++=x,*n++=y,z<<2;}
rplaca(x,y){R consp(x)?val(x)[m]=y:0;}
rplacd(x,y){R consp(x)?val(x)[m+1]=y:0;}
eq(x,y){R atomp(x)&&atomp(y)?x==y:0;}
ff(x){R atomp(x)?x:ff(car(x));}
subst(x,y,z){R atomp(z)?(eq(z,y)?x:z):
    cons(subst(x,y,car(z)),subst(x,y,cdr(z)));}
equal(x,y){R (atomp(x)&&atomp(y)&&eq(x,y))
    ||(consp(x)&&consp(y)&&equal(car(x),car(y))&&equal(cdr(x),cdr(y)));}
null(x){R listp(x)&&(val(x)==0);}
lista(int c,int*a){int z=NIL;for(;c;)z=cons(a[--c],z);R z;}
listn(int c,...){va_list a;int*z=n;
    va_start(a,c);for(;c--;)*n++=va_arg(a,int);va_end (a);
    c=n-z;R lista(c,z);}
#define list(...) listn(PP_NARG(__VA_ARGS__),__VA_ARGS__)
append(x,y){R null(x)?y:cons(car(x),append(cdr(x),y));}
among(x,y){R!null(y)&&equal(x,car(y))||among(x,cdr(y));}
pair(x,y){R null(x)&&null(y)?NIL:consp(x)&&consp(y)?
        cons(list(car(x),car(y)),pair(cdr(x),cdr(y))):0;}
assoc(x,y){R eq(caar(y),x)?cadar(y):assoc(x,cdr(y));}
sub2(x,z){R null(x)?z:eq(caar(x),z)?cadar(x):sub2(cdr(x),z);}
sublis(x,y){R atom(y)?sub2(x,y):cons(sublis(x,car(y)),sublis(x,cdr(y)));}
apply(f,args){R eval(cons(f,appq(args)),NIL);}
appq(m){R null(m)?NIL:cons(list(atom('Q'),car(m)),appq(cdr(m)));}
eval(e,a){R numberp(e)?e:
    atomp(e)?assoc(e,a):
    atomp(car(e))?(
    /*QUOTE*/      eq(car(e),atom('Q'))?cadr(e):
    /*ATOM*/       eq(car(e),atom('A'))?atomp(eval(cadr(e),a)):
    /*EQ*/         eq(car(e),atom('E'))?eval(cadr(e),a)==eval(caddr(e),a):
    /*COND*/       eq(car(e),atom('D'))?evcon(cadr(e),a):
    /*CAR*/        eq(car(e),atom('H'))?car(eval(cadr(e),a)):
    /*CDR*/        eq(car(e),atom('R'))?cdr(eval(cadr(e),a)):
    /*CONS*/       eq(car(e),atom('C'))?cons(eval(cadr(e),a),eval(caddr(e),a)):
        eval(cons(assoc(car(e),a),cdr(e)),a)): /*cf. Roots of Lisp*/
        //eval(cons(assoc(car(e),a),evlis(cdr(e),a)),a) ):
    eq(caar(e),atom('M'))? /*LABEL*/
        eval(cons(caddar(e),cdr(e)),cons(list(cadar(e),car(e)),a)):
    eq(caar(e),atom('L'))? /*LAMBDA*/
        eval(caddar(e),append(pair(cadar(e),evlis(cdr(e),a)),a)):0;}
evcon(c,a){R eval(caar(c),a)?eval(cadar(c),a):evcon(cdr(c),a);}
evlis(m,a){R null(m)?NIL:cons(eval(car(m),a),evlis(cdr(m),a));}
maplist(x,f){R null(x)?NIL:cons(apply(f,x),maplist(cdr(x),f));}

prn(x){atomp(x)?printf("'%c' ",val(x)+ALPHA):
    numberp(x)?printf("%d ",val(x)):
    objectp(x)?printf("OBJ %d ",val(x)):
    consp(x)?printf("( "),prn(car(x)),printf(". "),prn(cdr(x)),printf(") "):
    printf("NIL ");}

prnlst(x){
    x==NIL?0:
    !consp(x)?prn(x):
    printf("( "),prnrem(x);
}
prnrem(x){
    if(x==NIL)R;// printf(")0 ");
    if(car(x)!=NIL)
        prn(car(x));
    else
        R;// printf(") ");
    null(cdr(x))?
        printf(") "):
    !listp(cdr(x))?
        prn(cdr(x)),printf(") "):
    prnlst(car(cdr(x))),prnrem(cdr(cdr(x))),printf(") ");
}

#define LPAR '('
#define RPAR ')'
rd(char**p){int t,u,v,z;
    if(!(**p))R 0;
    if(**p==' ')R++(*p),rd(p);
    if(**p==RPAR)R++(*p),atom(RPAR);
    if(**p==LPAR){++(*p);
        z=NIL;
        u=rd(p);
        z=cons(u,NIL);
        while(u=rd(p),!eq(u,atom(RPAR)))
            u=cons(u,NIL),
            z=append(z,u);
        R z;}
    if(**p>='0'&&**p<='9')R++(*p),number(*((*p)-1)-'0');
    R++(*p),atom(*((*p)-1));}

void fix(x){signal(SIGSEGV,fix);sbrk(msz);msz*=2;}
int main(){
    assert((-1>>1)==-1);	/*right-shift must be sign-preserving */
    n=m=sbrk(sizeof(int)*(msz=getpagesize()));*n++=0;*n++=0;
    //signal(SIGSEGV,fix); /*might let it run longer, obscures problems*/
    char *s = "(Q (A (Q X)))";
    //s = "(1 2 3 4 5)";
    //s = "(E (Q X) (Q X))";
    //s = "(C (Q X) (Q (A B C)))";
    //s = "( (L (Q X) (Q (X X X))) (Q Y) )";
    //s = "(L (X) Y)";
    s = "( (L (X) (X Z)) (Q Q) )"; // -> 'Z'
    char *p = s;
    int a = rd (&p);
    printf ("%s\n", s);

    int x, y;
    x = a;
    y = NIL;

    prn(x); printf("\n");
    prnlst(x);
    fflush(0);
    printf ("\nEVAL\n");
    x = eval(x, y);

    printf ("x: %d\n", x);
    printf ("0: %o\n", x);
    printf ("0x: %x\n", x);
    printf ("tag(x): %d\n", tag (x));
    printf ("val(x): %d\n", val (x));
    printf ("car(x): %d\n", car (x));
    printf ("cdr(x): %d\n", cdr (x));
    prn (x); printf("\n");
    prnlst(x);

    R 0;
}
