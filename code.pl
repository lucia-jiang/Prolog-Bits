:- module(_,_,[assertions,regtypes]).

:- prop author_data(A1,A2,N,M)
    #" Predicado para introducir los datos del autor.
    @var{A1} y @var{A2} son los apellidos. 
    @var{N} nombre.
    @var{M} matr@'{i}cula
    @includedef{author_data/4}".

author_data('Jiang', '', 'Lucia', 'b19m042').

:- doc(title, "BITS, NIBBLES & BYTES").
:- doc(author, "Luc@'{i}a Jiang, b19m042").

:- doc(module, "Esta pr@'{a}ctica consiste en una serie de predicados que operan a nivel de bits, nibbles y bytes.
v
Se definen una serie de datos que funcionan como constantes para la pr@'{a}ctica: bits, nibbles, bytes (binarios o hexadecimales), bytes binarios y bytes hexadecimales.

@begin{alert}
    Se asume que el primer argumento de una lista de bytes es el bit m@'{a}s significativo, mientras que el @'{u}ltimo elemento de la lista ser@'{i}a el bit menos significativo.  
@end{alert}

@begin{alert}
    De la misma manera, se entiende que en la definici@'{o}n de un byte como una lista de nibbles, el primer elemento de la lista es el nibble m@'{a}s significativo, mientras que el @'{u}ltimo elemento ser@'{i}a el nibble menos significativo.
@end{alert}

@begin{alert}
    El @'{i}ndice del bit menos significativo de un byte es el 0
@end{alert}

@section{Predicados pedidos en la pr@'{a}ctica}

@begin{itemize}
    @item Predicado 1: byte_list/1
    @item Predicado 2: byte_conversion/2
    @item Predicado 3: byte_list_conversion/2
    @item Predicado 4: get_nth_bit_from_byte/3
    @item Predicado 5: byte_list_clsh/2
    @item Predicado 6: byte_list_crsh/2
    @item Predicado 7: byte_xor/3
@end{itemize}

@begin{verbatim}
    Todos los predicados vienen explicados en el apartado siguiente.
@end{verbatim}

@section{Predicados auxiliares}
@begin{itemize}
    @item h2b/2
    @item desplazarInteriores/3
    @item unirExtremos/2
    @item unirUltimateExtremos/2
    @item byte_xor_aux/4
    @item xor/3
@end{itemize}

@begin{verbatim}
    Todos los predicados vienen explicados en el apartado siguiente.
@end{verbatim}

").

% Definiendo bits
:- pred bind(X) 
    #" Definici@'{o}n del bit. Observar que 0 y 1 no funcionan como expresiones num@'{e}ricas, sino como constantes
    @includedef{bind/1}".
bind(0).
bind(1).

% Definiendo el byte binario como lista de 8 dígitos binarios. El primer elemento de la lista es el bit m@'{a}s significativo
:- pred binary_byte(L) 
    #" Los bytes son octetos de d@'{i}gitos binarios. Los representamos como una lista @var{L} de 8 d@'{i}gitos binarios.
    @includedef{binary_byte/1}".
binary_byte([bind(B7), bind(B6), bind(B5), bind(B4), bind(B3), bind(B2), bind(B1), bind(B0)]) :-
    bind(B7),
    bind(B6),
    bind(B5),
    bind(B4),
    bind(B3),
    bind(B2), 
    bind(B1),
    bind(B0). 

% Define un dígito hexadecimal, también llamado nibble (4 bits).
:- pred hexd(X)
    #" Definici@'{o}n del nibble, un d@'{i}gito hexadecimal (4 bits)
    @includedef{hexd/1}".
hexd(0).
hexd(1).
hexd(2).
hexd(3).
hexd(4).
hexd(5).
hexd(6).
hexd(7).
hexd(8).
hexd(9).
hexd(a).
hexd(b).
hexd(c).
hexd(d).
hexd(e).
hexd(f).


% Define un byte hexadecimal como una lista de 2 nibbles.
:- pred hex_byte(B)
    #"Representamos un byte como una lista @var{B} de 2 d@'{i}gitos hexadecimales (nibbles)
    @includedef{hex_byte/1}".
hex_byte([hexd(H1), hexd(H0)]) :-
    hexd(H1),
    hexd(H0).

% Define un byte como un byte binario o hexadecimal.
:- pred byte(X)
    #" Representamos un byte @var{X} como un byte binario o un byte hexadecimal
    @includedef{hexd/1}".
byte(BB) :- binary_byte(BB).
byte(HB) :- hex_byte(HB).

%-------------------------------------------------------------PREDICADOS------------------------------------------------------------

% Predicado 1 -------------------------------------------------------------------------------
:- pred byte_list(L) 
    #"El predicado es cierto si @var{L} es una lista de bytes, bien sea en binario o en hexadecimal.
    @includedef{byte_list/1}".

% Caso base
byte_list([]). 

% Comprobamos recursivamente que cada elemento de la lista sea un byte, bien sea hexadecimal o binario
byte_list([X|Y]) :- byte(X), byte_list(Y).  

% Predicado 2 -------------------------------------------------------------------------------
:- pred byte_conversion(H,B) 
    #"El predicado es cierto si @var{H} es el byte hexadecimal que tiene como representaci@'{o}n binaria el byte binario @var{B}.
    @includedef{byte_conversion/2}".

% Separamos H en sus dos elementos, y B en los 4 primeros y el resto de la lista.
% Llamamos a la auxiliar h2b que contiene las equivalencias de hexadecimal y binario
% Un byte nunca puede ser vacío
byte_conversion([H1,H2], [B1,B2,B3,B4|BL]) :- h2b(H1, [B1,B2,B3,B4]), h2b(H2, BL). 

% Auxiliar para el predicado 2:
:- prop h2b(H,B)
#" Cierto si el d@'{i}gito hexadecimal @var{H} tiene como d@'{i}gitos binarios @var{B}
@includedef{h2b/2}".

h2b(hexd(0), [bind(0), bind(0), bind(0), bind(0)]).
h2b(hexd(1), [bind(0), bind(0), bind(0), bind(1)]).
h2b(hexd(2), [bind(0), bind(0), bind(1), bind(0)]).
h2b(hexd(3), [bind(0), bind(0), bind(1), bind(1)]).
h2b(hexd(4), [bind(0), bind(1), bind(0), bind(0)]).
h2b(hexd(5), [bind(0), bind(1), bind(0), bind(1)]).
h2b(hexd(6), [bind(0), bind(1), bind(1), bind(0)]).
h2b(hexd(7), [bind(0), bind(1), bind(1), bind(1)]).
h2b(hexd(8), [bind(1), bind(0), bind(0), bind(0)]).
h2b(hexd(9), [bind(1), bind(0), bind(0), bind(1)]).
h2b(hexd(a), [bind(1), bind(0), bind(1), bind(0)]).
h2b(hexd(b), [bind(1), bind(0), bind(1), bind(1)]).
h2b(hexd(c), [bind(1), bind(1), bind(0), bind(0)]).
h2b(hexd(d), [bind(1), bind(1), bind(0), bind(1)]).
h2b(hexd(e), [bind(1), bind(1), bind(1), bind(0)]).
h2b(hexd(f), [bind(1), bind(1), bind(1), bind(1)]).

% Predicado 3 -------------------------------------------------------------------------------
:- pred byte_list_conversion(HL,BL) 
    #"El predicado es cierto si @var{HL} es la lista de bytes hexadecimales que tiene como representaci@'{o}n binaria la lista @var{BL}
    @includedef{byte_list_conversion/2}".

% Caso base:
byte_list_conversion([],[]).
% Si HL y BL son listas de solo un byte, llamamos a la versión simplificada del predicado: byte_conversion
byte_list_conversion(HL,BL) :- byte_conversion(HL,BL).
% Si HL y BL son listas con más de un byte, llamamos recursivamente a la lista quitado el primer elemento y convertimos el primer elemento.
byte_list_conversion([H|HL], [B|BL]) :- byte_list_conversion(HL, BL), byte_conversion(H,B).


% Predicado 4 -------------------------------------------------------------------------------
:- pred get_nth_bit_from_byte(N,B,BN)
    #"Este predicado polim@'{o}rfico es cierto si @var{BN} es el bit n@'{u}mero @var{N} del byte @var{B}.
    Teniendo en cuenta que @var{N} es un n@'{u}mero peano, el @'{i}ndice del bit menos significativo de un byte es el 0 (se cuenta por la derecha).
    
    Sabiendo que un byte son 8 bits, es equivalente el bit @var{N} desde la derecha al bit 8-@var{N}-1 = 7-@var{N} desde la izquierda. 
    Una vez transformado @var{N} utilizaremos un predicado auxiliar para obtener ese bit.
    
    @includedef{get_nth_bit_from_byte/3}".

% Primer caso: X y Z son bytes binarios. Transformamos el número N a 7-N y llamamos a la auxiliar
get_nth_bit_from_byte(N,B,BN) :- binary_byte(B), mi_suma(N, Naux,s(s(s(s(s(s(s(0)))))))), get_nth_bit_from_byte_aux(Naux, B, BN).

% Segundo caso: X y Z son bytes hexadecimales. Pasamos a binario y llamamos de nuevo al predicado para volver al primer caso
get_nth_bit_from_byte(N,B,BN) :- hex_byte(B), byte_conversion(B, Y), get_nth_bit_from_byte(N, Y, BN). 


% Auxiliar para el predicado 4:
:- pred get_nth_bit_from_byte_aux(N,B,BN)
    #" Predicado auxiliar que se utiliza una vez se ha transformado el n@'{u}mero @var{N} para contar desde la izquierda.
    @var{BN} es el bit en posici@'{o}n n@'{u}mero @var{N} del byte @var{B}. 

    Vamos llamando a la auxiliar decrementando el valor de @var{N} y con la lista quitando el primer elemento hasta llegar al caso base: @var{N=0}
    
    @includedef{get_nth_bit_from_byte_aux/3}".

%caso base: N=0
get_nth_bit_from_byte_aux(0,[B|_],B).
%resto de casos: volvemos a llamar a la auxiliar, decrementando el valor de N y con la lista menos el primer elemento.
get_nth_bit_from_byte_aux(N,[_|Y],BN) :- mi_suma(s(0), N2, N), get_nth_bit_from_byte_aux(N2, Y, BN).


% Predicado 5 -------------------------------------------------------------------------------
:- pred byte_list_clsh(L, CL)
    #"Este predicado polim@'{o}rfico es cierto si @var{CLShL} es el resultado de efectuar un desplazamiento circular hacia la izquierda de la lista de bytes representada por @var{L}. 
    Este predicado funciona tanto para listas de bytes hexadecimales como binarias, aunque ambos argumentos deben estar representados en la misma notaci@'{o}n. 
    @includedef{byte_list_clsh/2}".


byte_list_clsh([L1|L2], [CL1|CL2]) :- unirExtremos([L1|L2], [CL1|CL2]), unirUltimateExtremos(L1,[CL1|CL2]).

% Auxiliares para el predicado 5 --------------------------------
% Primero, desplazaremos todos los bits salvo el más significativo al menos
:- pred unirExtremos(L,CL)
    #"Uno de los auxiliares empleados para el predicado byte_list_clsh/2.
    Es cierto si todos los bits de @var{L} salvo el m@'{a}s significativo se han desplazado a la izquierda una posici@'{o}n en @var{CL}
    @includedef{unirExtremos/2}".

% Caso base bytes binarios:
unirExtremos([L1|[]], [CL1|[]]) :-  binary_byte(L1), binary_byte(CL1), desplazarInteriores(L1, CL1, 0).
% Caso base bytes hexadecimales:
unirExtremos([L1|[]], [CL1|[]]) :- hex_byte(L1), hex_byte(CL1), desplazarInteriores(L1, CL1, 0).

% Caso recursivo bytes binarios: 
% desplazamos los bits interiores del primer byte de L con el predicado destinado a ello (desplazarInteriores)
% el último de bit del segundo byte (L2) de L pasa a ser el bit 0 del primer byte (CL2) de CL
% llamamos de nuevo al predicado, sin el primer elemento de las listas
unirExtremos([L1|[L2|L3]], [CL1|CL2]) :- binary_byte(L1), binary_byte(CL1), desplazarInteriores(L1, CL1, 0), get_nth_bit_from_byte(s(s(s(s(s(s(s(0))))))), L2, X), get_nth_bit_from_byte(0, CL1, X), unirExtremos([L2|L3], CL2).
% Caso recursivo bytes hexadecimales: igual que el binario, pero con hexadecimales
unirExtremos([L1|[L2|L3]], [CL1|CL2]) :- hex_byte(L1), hex_byte(CL1), desplazarInteriores(L1, CL1, 0), get_nth_bit_from_byte(s(s(s(s(s(s(s(0))))))), L2, X), get_nth_bit_from_byte(0, CL1, X), unirExtremos([L2|L3], CL2).


% Desplazamos los bits interiores 1-6
:- pred desplazarInteriores(L,CL,N)
    #"Uno de los auxiliares empleados para el predicado byte_list_clsh/2.
    Es cierto si los bits en las posiciones 1-6 de @var{L} son los bits 2-7 de @var{CL} respectivamente.
    @includedef{desplazarInteriores/3}".

% Caso base: N=7
desplazarInteriores(_, _, s(s(s(s(s(s(s(0)))))))).

% Recursivamente, hacemos que el bit N de L1 sea el bit N+1 de CL1.
% Guardamos el contador de bits leidos en N para llegar al caso base
desplazarInteriores(L1, CL1, N) :- get_nth_bit_from_byte(N,L1,X), get_nth_bit_from_byte(s(N),CL1, X), desplazarInteriores(L1, CL1, s(N)).


% Último desplazamiento: el bit m@'{a}s significativo a la posici@'{o}n menos significativa
:- pred unirUltimateExtremos(L, CL)
    #"Uno de los auxiliares empleados para el predicado byte_list_clsh/2.
    Es cierto si el bit m@'{a}s significativo de @var{L} es el menos significativo de @var{CL}
    @includedef{unirUltimateExtremos/2}".

% Caso base: estamos en el último byte de CL
% comprobamos que el bit 7 de L1 es el el 0 de CLs
unirUltimateExtremos(L1, [CLs|[]]) :- get_nth_bit_from_byte(s(s(s(s(s(s(s(0))))))), L1, X), get_nth_bit_from_byte(0,CLs, X).
% Vamos recorriendo los elmenetos de la lista CL para llegar al último byte
unirUltimateExtremos(L1, [_|CLs]) :- unirUltimateExtremos(L1, CLs).

% Predicado 6 -------------------------------------------------------------------------------
:- pred byte_list_crsh(L, CR)
    #"Este predicado polim@'{o}rfico es cierto si @var{CR} es el resultado de efectuar un desplazamiento circular hacia la izquierda de la lista de bytes representada por @var{L}. 
    Este predicado funciona tanto para listas de bytes hexadecimales como binarias, aunque ambos argumentos deben estar representados en la misma notaci@'{o}n. 
    @includedef{byte_list_crsh/2}".

% Aprovechamos el predicado byte_list_clsh y la llamamos de manera simétrica
byte_list_crsh(L, CR) :- byte_list_clsh(CR, L).

% Predicado 7 -------------------------------------------------------------------------------
:- pred byte_xor(H1, H2, H3)
    #"Este predicado polim@'{o}rfico es cierto si @var{H3} es el resultado de efectuar la operaci@'{o}n l@'{o}gica XOR entre los bytes @var{H1} y @var{H2}. 
    Este predicado debe funcionar tanto para bytes binarios como hexadecimales, aunque todos los argumentos deben estar representados en la misma notaci@'{o}n.
    @includedef{byte_xor/3}".

% Caso bytes hexadecimales: comprobamos que todos son del mismo tipo y llamamos a la auxiliar
byte_xor(H1, H2, H3) :- hex_byte(H1), hex_byte(H2), hex_byte(H3), byte_xor_aux(H1, H2, H3, 0).
% Caso bytes binarios: comprobamos que todos son del mismo tipo y llamamos a la auxiliar
byte_xor(B1, B2, B3) :- binary_byte(B1), binary_byte(B2), binary_byte(B3), byte_xor_aux(B1, B2, B3, 0).

% Auxiliares para el predicado 7 -----------------------------------------
:- pred byte_xor_aux(B1, B2, B3, N)
    #"Auxiliar para el predicado 7
    Recorre todos los bits de @var{B1} y @var{B2} aplicando la operaci@'{o}n xor y dejando los resultados en @var{B3} en los bits correspondientes.
    @var{N} es un contador del bit que estamos evaluando en cada momento.
    @includedef{byte_xor_aux/4}".

% Caso base: N=8
byte_xor_aux(_, _, _, s(s(s(s(s(s(s(s(0))))))))). 
% Obtenemos el bit N de B1 y B2 y le aplicamos la operación xor. El resultado se almacena en el bit N de B3. 
% Vamos incrementando el valor de N hasta operar con todos los bits
byte_xor_aux(B1, B2, B3, N) :- get_nth_bit_from_byte(N, B1, X),  get_nth_bit_from_byte(N, B2, Y), xor(X,Y,Z), get_nth_bit_from_byte(N, B3, Z), byte_xor_aux(B1, B2, B3, s(N)).

:- prop xor(B1, B2, B3) 
    #"Auxiliar para el predicado 7.
    Cierto si @var{B1} y @var{B2} con la operaci@'{o}n l@'{o}gica xor da como resultado @var{B3}
    @includedef{xor/3}".

xor(bind(0), bind(0), bind(0)).
xor(bind(0), bind(1), bind(1)).
xor(bind(1), bind(0), bind(1)).
xor(bind(1), bind(1), bind(0)).

% Otros auxiliares -----------------------------------------------------
:- prop nat(N)
    #" @var{N} es un n@'{u}mero natural
    @includedef{nat/1}".
nat(0).
nat(s(N)) :- nat(N).

:- pred mi_suma(X,Y,Z)
    #" La suma de los naturales @var{X}+@var{Y} es igual al natural @var{Z}.
    @includedef{mi_suma/3}".
mi_suma(0,X,X) :- nat(X).
mi_suma(s(X), Y, s(Z)) :- mi_suma(X,Y,Z).

%------------------------------------TESTS------------------------------------

% Predicado 1: byte_list-------------------------------
:- test byte_list(L) : (L = []) + not_fails.
:- test byte_list(L) : (L = [[bind(0), bind(1), bind(0), bind(0), bind(1), bind(0), bind(1), bind(0)]]) + not_fails.
:- test byte_list(L) : (L = [[bind(0), bind(0), bind(0), bind(0), bind(0), bind(1), bind(0), bind(0)], [bind(0), bind(1), bind(0), bind(0), bind(0), bind(0), bind(0), bind(0)]]) + not_fails.
:- test byte_list(L) : (L = [[hexd(a), hexd(f)]]) + not_fails.
:- test byte_list(L) : (L = [[hexd(a), hexd(f)], [hexd(d), hexd(3)]]) + not_fails.
%:- test byte_list(L) : => (L = [[bind(0), bind(0), bind(0), bind(0), bind(0), bind(0), bind(0), bind(0)]]) + not_fails.

:- test byte_list(L) : (L = [[bind(0), bind(1), bind(0), bind(0), bind(1), bind(0)]]) + fails #"Una lista de bytes tiene que ser de 8 bits binarios, o dos d@'{i}gitos hexadecimales".
:- test byte_list(L) : (L = [[hexd(a)]]) + fails #"Una lista de bytes tiene que ser de 8 bits binarios, o dos d@'{i}gitos hexadecimales".
:- test byte_list(L) : (L = [hexd(3), hexd(g)]) + fails #"Los d@'{i}gitos hexadecimales est@'{a}n definidos de 0-9 y a-f".
:- test byte_list(L) : (L = [[bind(0), bind(0), bind(0), bind(0), bind(1), bind(0), bind(0), bind(2)]]) + fails #"Los d@'{i}gitos binarios son bind(0) o bind(1) @'{u}nicamente".

% Predicado 2: byte_conversion-------------------------------

:- test byte_conversion(H,B) : (H = [hexd(3), hexd(5)]) => (B = [bind(0), bind(0), bind(1), bind(1), bind(0), bind(1), bind(0), bind(1)]) + not_fails.
:- test byte_conversion(H,B) : (B = [bind(0), bind(1), bind(0), bind(0), bind(1), bind(1), bind(1), bind(0)] ) => (H = [hexd(4), hexd(e)]) + not_fails.

:- test byte_conversion(H,B) : (H = [hexd(f), hexd(3)], B = [bind(1), bind(0), bind(1), bind(0), bind(1), bind(1), bind(0), bind(1)]) + fails #"Conversi@'{o}n incorrecta".
:- test byte_conversion(H,B) : (H = [bind(1), bind(0), bind(1), bind(0), bind(0), bind(0), bind(0), bind(1)], B = [hexd(a), hexd(1)]) + fails #"El primer argumento tiene que ser byte hexadecimal y el segundo binario".

% Predicado 3: byte_list_conversion-------------------------------
:- test byte_list_conversion(HL,BL) : (HL = [[hexd(a), hexd(1)], [hexd(f), hexd(0)]]) => (BL = [[bind(1), bind(0), bind(1), bind(0), bind(0), bind(0), bind(0), bind(1)], [bind(1), bind(1), bind(1), bind(1), bind(0), bind(0), bind(0), bind(0)]]) + not_fails.
:- test byte_list_conversion(HL,BL) : (BL = [[bind(1), bind(0), bind(1), bind(0), bind(0), bind(0), bind(0), bind(1)], [bind(1), bind(1), bind(1), bind(1), bind(0), bind(0), bind(0), bind(0)]]) => (HL = [[hexd(a), hexd(1)], [hexd(f), hexd(0)]]) + not_fails.

:- test byte_list_conversion(HL,BL) : (HL = [[hexd(a), hexd(1)], [hexd(f), hexd(0)]], BL = [[bind(1), bind(0), bind(1), bind(0), bind(0), bind(0), bind(1), bind(1)], [bind(1), bind(0), bind(1), bind(1), bind(0), bind(0), bind(0), bind(0)]]) + fails #"Conversi@'{o}n incorrecta".
:- test byte_list_conversion(HL,BL) : (HL = [[bind(1), bind(0), bind(1), bind(0), bind(0), bind(0), bind(0), bind(1)], [bind(1), bind(1), bind(1), bind(1), bind(0), bind(0), bind(0), bind(0)]], BL = [[hexd(a), hexd(1)], [hexd(f), hexd(0)]]) + fails #"Argumentos en el orden incorrecto".

% Predicado 4: get_nth_bit_from_byte-------------------------------
:- test get_nth_bit_from_byte(N,B,BN) : (N = s(s(s(0))), B = [bind(1), bind(0), bind(1), bind(0), bind(0), bind(1), bind(1), bind(0)], BN = bind(0)) + not_fails.
:- test get_nth_bit_from_byte(N,B,BN) : (N = s(s(s(s(0)))), B = [bind(1), bind(0), bind(1), bind(0), bind(0), bind(1), bind(1), bind(0)]) => (BN = bind(0)) + not_fails.

:- test get_nth_bit_from_byte(N,B,BN) : (N = 0, B = [hexd(a), hexd(4)], BN = bind(0))+ not_fails.
:- test get_nth_bit_from_byte(N,B,BN) : (N = s(0), B = [hexd(a), hexd(4)]) => (BN = bind(0)) + not_fails.

:- test get_nth_bit_from_byte(N,B,BN) : (N = s(s(s(0))), B = [bind(1), bind(0), bind(1), bind(0), bind(0), bind(1), bind(1), bind(0)], BN = bind(1)) + fails #"Bit incorrecto".
:- test get_nth_bit_from_byte(N,B,BN) : (N = 0, B = [hexd(a), hexd(4)], BN = bind(1))+ fails #"Bit incorrecto".

:- test get_nth_bit_from_byte(N,B,BN) : (N = 0, B = [hexd(a), hexd(4)], BN = [bind(1)])+ fails #"Tipo incorrecto".

% Predicado 5: byte_list_clsh-------------------------------
:- test byte_list_clsh(L, CLShL) : (L = [[bind(0), bind(1), bind(0), bind(0), bind(1), bind(1), bind(1), bind(0)]], CLShL = [[bind(1), bind(0), bind(0), bind(1), bind(1), bind(1), bind(0), bind(0)]]) + not_fails.
:- test byte_list_clsh(L, CLShL) : (L = [[bind(0), bind(1), bind(0), bind(0), bind(1), bind(1), bind(1), bind(0)]]) => (CLShL = [[bind(1), bind(0), bind(0), bind(1), bind(1), bind(1), bind(0), bind(0)]]) + not_fails.
:- test byte_list_clsh(L, CLShL) : (L = [[bind(1), bind(0), bind(1), bind(0), bind(0), bind(0), bind(0), bind(1)], [bind(1), bind(1), bind(1), bind(1), bind(0), bind(0), bind(0), bind(0)]]) => (CLShL = [[bind(0), bind(1), bind(0), bind(0), bind(0), bind(0), bind(1), bind(1)], [bind(1), bind(1), bind(1), bind(0), bind(0), bind(0), bind(0), bind(1)]]) + not_fails.

:- test byte_list_clsh(L, CLShL) : (L = [[hexd(0), hexd(f)]], CLShL = [[hexd(1), hexd(e)]]) + not_fails.
:- test byte_list_clsh(L, CLShL) : (L = [[hexd(0), hexd(f)]]) => (CLShL = [[hexd(1), hexd(e)]]) + not_fails.
:- test byte_list_clsh(L, CLShL) : (L = [[hexd(5), hexd(a)], [hexd(2), hexd(3)], [hexd(5), hexd(5)], [hexd(3), hexd(7)]]) => (CLShL = [[hexd(b), hexd(4)], [hexd(4), hexd(6)], [hexd(a), hexd(a)], [hexd(6), hexd(e)]]) + not_fails.

:- test byte_list_clsh(L, CLShL) : (L = [[bind(1), bind(0), bind(0), bind(1), bind(1), bind(1), bind(0), bind(0)]], CLShL = [[bind(0), bind(1), bind(0), bind(0), bind(1), bind(1), bind(1), bind(0)]]) + fails #"Cambio en el sentido contrario".
:- test byte_list_clsh(L, CLShL) : (L = [[hexd(1), hexd(e)]], CLShL = [[hexd(0), hexd(f)]]) + fails #"Cambio en el sentido contrario".
:- test byte_list_clsh(L, CLShL) : (L = [[hexd(5), hexd(a)], [hexd(2), hexd(3)], [hexd(5), hexd(5)], [hexd(3), hexd(7)]], CLShL = [[hexd(3), hexd(4)], [hexd(3), hexd(4)], [hexd(4), hexd(1)], [hexd(0), hexd(a)]]) + fails #"No es el resultado esperado".

% Predicado 6: byte_list_crsh-------------------------------
:- test byte_list_crsh(L, CRShL) : (L = [[bind(1), bind(0), bind(0), bind(1), bind(1), bind(1), bind(0), bind(0)]], CRShL = [[bind(0), bind(1), bind(0), bind(0), bind(1), bind(1), bind(1), bind(0)]]) + not_fails.
:- test byte_list_crsh(L, CRShL) : (L = [[bind(1), bind(0), bind(0), bind(1), bind(1), bind(1), bind(0), bind(0)]]) =>  (CRShL = [[bind(0), bind(1), bind(0), bind(0), bind(1), bind(1), bind(1), bind(0)]]) + not_fails.
:- test byte_list_crsh(L, CRShL) : (L = [[bind(0), bind(1), bind(0), bind(0), bind(0), bind(0), bind(1), bind(1)], [bind(1), bind(1), bind(1), bind(0), bind(0), bind(0), bind(0), bind(1)]]) => (CRShL = [[bind(1), bind(0), bind(1), bind(0), bind(0), bind(0), bind(0), bind(1)], [bind(1), bind(1), bind(1), bind(1), bind(0), bind(0), bind(0), bind(0)]]) + not_fails.

:- test byte_list_crsh(L, CRShL) : (L = [[hexd(1), hexd(e)]], CRShL = [[hexd(0), hexd(f)]]) + not_fails.
:- test byte_list_crsh(L, CRShL) : (L = [[hexd(1), hexd(e)]]) => (CRShL = [[hexd(0), hexd(f)]]) + not_fails.
:- test byte_list_crsh(L, CRShL) : (L = [[hexd(b), hexd(4)], [hexd(4), hexd(6)], [hexd(a), hexd(a)], [hexd(6), hexd(e)]]) => (CRShL = [[hexd(5), hexd(a)], [hexd(2), hexd(3)], [hexd(5), hexd(5)], [hexd(3), hexd(7)]]) + not_fails.

:- test byte_list_crsh(L, CRShL) : (L = [[bind(0), bind(1), bind(0), bind(0), bind(1), bind(1), bind(1), bind(0)]], CRShL = [[bind(1), bind(0), bind(0), bind(1), bind(1), bind(1), bind(0), bind(0)]]) + fails #"Cambio en el sentido contrario".
:- test byte_list_crsh(L, CRShL) : (L = [[hexd(0), hexd(f)]], CRShL = [[hexd(1), hexd(e)]]) + fails #"Cambio en el sentido contrario".
:- test byte_list_crsh(L, CRShL) : (L = [[hexd(b), hexd(4)], [hexd(3), hexd(4)], [hexd(f), hexd(1)], [hexd(0), hexd(a)]], CRShL = [[hexd(5), hexd(a)], [hexd(2), hexd(3)], [hexd(5), hexd(5)], [hexd(3), hexd(7)]])+ fails #"No es el resultado esperado".

% Predicado 7: byte_xor-------------------------------
:- test byte_xor(B1,B2,B3) : (B1 = [hexd(a), hexd(3)], B2 = [hexd(e), hexd(9)], B3 = [hexd(4), hexd(a)]) + not_fails.
:- test byte_xor(B1,B2,B3) : (B1 = [hexd(4), hexd(3)], B2 = [hexd(7), hexd(9)]) => (B3 = [hexd(3), hexd(a)]) + not_fails.

:- test byte_xor(B1,B2,B3) : (B2 = [hexd(3), hexd(7)], B3 = [hexd(e), hexd(e)]) => (B1 = [hexd(d), hexd(9)]) + not_fails.
:- test byte_xor(B1,B2,B3) : (B1 = [hexd(3), hexd(7)], B3 = [hexd(e), hexd(e)]) => (B2 = [hexd(d), hexd(9)]) + not_fails.

:- test byte_xor(B1,B2,B3) : (B1 = [bind(1), bind(0), bind(0), bind(1), bind(1), bind(1), bind(0), bind(0)], B2 = [bind(0), bind(1), bind(0), bind(0), bind(0), bind(0), bind(1), bind(1)], B3 = [bind(1), bind(1), bind(0), bind(1), bind(1), bind(1), bind(1), bind(1)]) + not_fails.
:- test byte_xor(B1,B2,B3) : (B1 = [bind(1), bind(0), bind(0), bind(1), bind(1), bind(1), bind(0), bind(0)], B2 = [bind(0), bind(1), bind(0), bind(0), bind(0), bind(0), bind(1), bind(1)]) => (B3 = [bind(1), bind(1), bind(0), bind(1), bind(1), bind(1), bind(1), bind(1)]) + not_fails.

:- test byte_xor(B1,B2,B3) : (B2 = [bind(1), bind(1), bind(0), bind(0), bind(0), bind(0), bind(0), bind(0)], B3 = [bind(0), bind(0), bind(0), bind(0), bind(0), bind(0), bind(1), bind(1)], B1 = [bind(1), bind(1), bind(0), bind(0), bind(0), bind(0), bind(1), bind(1)]) + not_fails.
:- test byte_xor(B1,B2,B3) : (B1 = [bind(1), bind(1), bind(0), bind(0), bind(0), bind(0), bind(0), bind(0)], B3 = [bind(0), bind(0), bind(0), bind(0), bind(0), bind(0), bind(1), bind(1)], B2 = [bind(1), bind(1), bind(0), bind(0), bind(0), bind(0), bind(1), bind(1)]) + not_fails.

:- test byte_xor(B1,B2,B3) : (B1 = [hexd(a), hexd(3)], B2 = [hexd(e), hexd(9)], B3 = [hexd(f), hexd(0)]) + fails #"Resultado equivocado".
:- test byte_xor(B1,B2,B3) : (B1 = [bind(1), bind(0), bind(0), bind(1), bind(1), bind(1), bind(0), bind(0)], B2 = [bind(0), bind(1), bind(0), bind(0), bind(0), bind(0), bind(1), bind(1)], B3 = [bind(0), bind(1), bind(1), bind(0), bind(0), bind(1), bind(1), bind(1)]) + fails #"Resultado equivocado".



