#!/bin/bash

od --endian=little -v -t x4z -A x "$1" | \
gawk -- '
function tag(x){
    switch(substr(x,8,1)){
    case "0": case "4": case "8": case "c": return "CONS";
    case "1": case "5": case "9": case "d": return "SYM";
    case "2": case "6": case "a": case "e": return "OBJ";
    case "3": case "7": case "b": case "f": return "NUM";
    }
}
function objtag(x){
    switch(x){
    case 0: return "SUBR"
    case 1: return "FSUBR"
    case 2: return "SUBR2"
    case 3: return "FSUBR2"
    case 4: return "STRING"
    }
}
function em(x){
    return tag(x) ":" x
}
function offset(addr,off){
    return tolower( sprintf("0x%08x", strtonum("0x" addr)+(off*4)) )
}
function extract_string(x,i,n,a,b,c,d){
    i = 0
    s = ""
    do{
      n = strtonum( "0x" mem[ offset("0", strtonum("0x" x) + i) ] )
      a = n % 256
      b = int(n / 256) % 256
      c = int(n / 65536) % 256
      d = int(n / 16777216) % 256
      #s = s sprintf("0x%08x ", n)
      #s = s sprintf("%02x %02x %02x %02x ", a, b, c, d)
      #s = s sprintf("%c%c%c%c ", a, b, c, d)
      if( a ) s = s sprintf("%c", a )
      if( b ) s = s sprintf("%c", b )
      if( c ) s = s sprintf("%c", c )
      if( d ) s = s sprintf("%c", d )
      i++
    } while (d)
    return s
}
function print_cell(x){
    switch(mem[x] != 0 ? tag(mem[x]) : 0){
    case "CONS":
	car = offset( mem[x], 0 )
	cdr = offset( mem[x], 1 )
	print x " " em(mem[x]) " = (" em(mem[car]) " . " em(mem[cdr]) ") "
	print_cell( offset( mem[x], 0 ) )
	print_cell( offset( mem[x], 1 ) )
	break
    case "OBJ":
	t = offset( mem[x], -0.5 )
	c = offset( mem[x], 0.5 )
	print x " " em(mem[x]) " " t " " objtag( mem[t] ) " " mem[c]
	if( objtag( mem[t] ) == "STRING" )
	  print extract_string( mem[c] )
        break
    case "SYM":
        print x " SYM #" int(strtonum("0x" mem[x]) / 4)
        break
    default:
	print x " " em(mem[x])
	break
    }
}
function print_env(){
    print "record(cells used,cells malloced,env,syms):"
    printf "%s %s %s %s\n", mem["0x00000000"], mem["0x00000004"],
                            mem["0x00000008"], mem["0x0000000c"]
    printf "used: %s*4bytes/cell = %s (address at end of data)\n",
           "0x" mem["0x00000000"],
           tolower( sprintf("0x%08x", strtonum("0x" mem["0x00000000"]) * 4) )
    print "env:"
    print_cell("0x00000008")
    print "syms:"
    print_cell("0x0000000c")
}
function print_mem(){
    print "mem:"
    used = strtonum( "0x" mem["0x00000000"] )
    print "used=" used " cells"
    for( i = 16; i < used; i++ ){
	a = offset( "0", i )
	print a " " mem[ a ]
    }
}
/([:xdigit:]+) ([:xdigit:]+) ([:xdigit:]+) ([:xdigit:]+) ([:xdigit:]+) (.+)/
{ 
    mem[offset($1,0)] = $2
    mem[offset($1,1)] = $3
    mem[offset($1,2)] = $4
    mem[offset($1,3)] = $5
    #print $1,em($2),em($3),em($4),em($5)
}
END {
    print_env()
    print_mem()
} '

