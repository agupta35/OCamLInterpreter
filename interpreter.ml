type valuesofstack = I of int | S of string | B of bool | Error | Unit | N of string  
type typesofcommands = Quit | Pushi of valuesofstack | Pushs of valuesofstack | Pushn of valuesofstack | Pushb of valuesofstack | Push of valuesofstack |
                       Pop  | Add | Sub | Mul | Div | Rem | Neg | Swap | Cat | And | Not | Or | Equal | Less | Bind | If | Let | End | Fun of (valuesofstack * valuesofstack) |
                       Funend | Call | Return

let interpreter ( (input : string), (output : string )) : unit =
  (* Here we open an input channel for first argument, inFile, 
     and bind it to a variable ic so that we can refer it 
     later in loop_read function. *)
  let ic = open_in input in

  (* Use the second argument as file name to open an output channel,
     and bind it to variable oc for later reference. *)
  let oc = open_out output in 

  (* Helper function: file input function. It reads file line by line
     and return the result as a list of string.  *)
  let rec loop_read acc =
      (* We use try with to catch the End_of_file exception. *)
      try 
          (* Read a line from ic. Build a new list with l::acc
             and pass to next recursive call. *)
          let l = input_line ic in loop_read (l::acc)
      with
        (* At the end of file, we will reverse the string since
           the list is building by keeping add new element at the 
           head of old list. *)
      | End_of_file -> List.rev acc in

  (* This variable contains the result of input file from helper 
     function, loop_read. Please remember this is a list of string. *)
  let ls_commandsstr = loop_read [] in  (*List of Strings*)
  let castbool str : bool= if (str=":true:") then true else false (*Casts str to boolean*)
  in
  let tostring valstack =
  match valstack with
  | I a -> (string_of_int a)
  | S s -> s
  | N s -> s
  | B true -> ":true:"
  | B false -> ":false:"
  | Error -> ":error:"
  | Unit -> ":unit:"
in
let file_write v = Printf.fprintf oc "%s\n" v 
in
let is_int s =
  try ignore (int_of_string s); true
  with _ -> false
 in 
 let characterlist = [ 'a';'b';'c';'d';'e';'f';'g';'h';'i';'j';'k';'l';'m';'n';'o';'p';'q';'r';'s';'t';'u';'v';'w';'x';'y';'z';'A';'B';'C';'D';'E';'F';'G';'H';'I';'J';'K';'L';'M';'N';'O';'P';'Q';'R';'S';'T';'U';'V';'W';'X';'Y';'Z'] in  

  let rec stringchecker characterlist str =
      match characterlist with
      | [] -> false
      | head::tail -> if String.contains str head then true else stringchecker tail str
    in
 let namechecker name = if((String.get name 0='_') || stringchecker characterlist name=true) then true else false

in
    let stackmaker str = (*We will get a string from convert function eg. "pushs "adv"", then we have to "adv to the list of valuesonstack"*)
      (match String.split_on_char ' ' str with
      | ["add"] -> Add
      | ["sub"] -> Sub
      | ["funEnd"] -> Funend
      | ["call"] -> Call
      | ["return"] -> Return
      | ["mul"] -> Mul
      | ["div"] -> Div
      | ["if"] -> If
      | ["rem"] -> Rem
      | ["neg"] -> Neg
      | ["swap"] -> Swap
      | ["pop"] -> Pop
      | ["quit"] -> Quit
      | ["cat"] -> Cat
      | ["and"] -> And
      | ["not"] -> Not
      | ["or"] -> Or
      | ["equal"] -> Equal
      | ["lessThan"] -> Less
      | ["bind"] -> Bind
      | ["let"] -> Let
      | ["end"] -> End
      | hd1::snd1::c::tl -> (match (hd1,snd1,c) with
                          |("fun", a,b) -> if(namechecker a && namechecker b) then Fun(N(a),N(b)) else Push Error 
                          | (_,_,_) -> Push Error    )
      | hd::snd::tl -> (match (hd,snd) with
                        | ("pushb", s) -> if(s=":true:" || s=":false:") then Pushb (B(castbool s)) else Push Error           
                        | ("pushi", s) -> if(is_int s) then Pushi (I(int_of_string s)) else Push Error
                        | ("push", ":error:") -> Push Error
                        | ("push", ":unit:") -> Push Unit
                        | ("pushs", s) -> if(String.get s 0='\"') then Pushs (S (String.sub str 7 (String.length str - 8))) else Push Error
                        | ("pushn", s) -> if((String.get s 0='_') || stringchecker characterlist s=true) then Pushn (N s) else Push Error   
                        | (_,_) ->Push Error)
      |_ -> Push Error)
  in
let rec print_stack stck = 
    (match stck with
    | [] -> ()
    | hd::tl -> (file_write (tostring hd))
    ; print_stack tl)

in
  let rec convert (ls_commandsstr : string list ) : typesofcommands list = 
          match ls_commandsstr with
          | [] -> []
          | hd::tl -> (stackmaker hd)::(convert tl)
in
  let commandList= convert ls_commandsstr                 
in 
let rec fetch1 list1 name = 
  match list1 with
   |[] -> None
   |(hd,value)::tl -> if(hd=name) then Some(value) else fetch1 tl name
in
let rec fetch listtuple name = (*Play with the const type *)
    match listtuple with
    | [] -> None
    | hd::tl1 -> (match (fetch1 hd name)  with
                | Some(value) -> Some(value)
                | None -> fetch tl1 name)

in(*Add fetch function to find bind tuples , 3 more cases in add etc*)
  let rec execute commandList (stack: valuesofstack list list) (listtuples: (string*valuesofstack) list list) =
    match (commandList, stack, listtuples) with
        | (Let::cs, (stack)::s1, listtuples) -> execute cs ([]::stack::s1) ([]::listtuples)
        | (End::cs, (s::top1)::top2::bottom1, env1::env2) -> execute cs ((s::top2)::bottom1) env2
        | (End::cs, top1::bottom1, top2::down1) -> execute cs bottom1 down1
        | (End::cs, top1::bottom1, top2::down1) -> execute cs ((top1)::bottom1) ((top2)::down1)
        | ((Fun(N(a),N(b)))::cs::funEnd::cs2, (top1)::reststacks, top2::down1) -> execute cs2 ((top1)::reststacks) ((top2)::down1)
        | (Bind::cs, (N(x)::N(y)::s)::s1, listtupleshd::tl) -> (match (fetch listtuples x) with
                                                          | (Some I(x)) -> execute cs ((Unit::s)::s1) (((y,I(x))::listtupleshd)::tl)
                                                          | (Some B(x)) -> execute cs ((Unit::s)::s1) (((y,B(x))::listtupleshd)::tl)
                                                          | (Some S(x)) -> execute cs ((Unit::s)::s1) (((y,S(x))::listtupleshd)::tl)
                                                          | (Some Unit) -> execute cs ((Unit::s)::s1) (((y,Unit)::listtupleshd)::tl)
                                                          | _ -> execute cs ((Error::N(x)::N(y)::s)::s1) ((listtupleshd)::tl))
        | (Bind::cs, (x::N(y)::s)::s1, listtupleshd::tl) -> (match x with
                                                          | I(x) -> execute cs ((Unit::s)::s1) (((y,I(x))::listtupleshd)::tl)
                                                          | B(x) -> execute cs ((Unit::s)::s1) (((y,B(x))::listtupleshd)::tl)
                                                          | S(x) -> execute cs ((Unit::s)::s1) (((y,S(x))::listtupleshd)::tl)
                                                          | Unit -> execute cs ((Unit::s)::s1) (((y,Unit)::listtupleshd)::tl)
                                                          | _ -> execute cs ((Error::x::N(y)::s)::s1) ((listtupleshd)::tl))
        | (Bind::cs, (topstack)::reststacks, listtuples) -> execute cs ((Error::topstack)::reststacks) listtuples 
        | (Add::cs, (I(x)::I(y)::s)::s1, listtuples) -> execute cs ((I(x+y)::s)::s1) listtuples
        | (Add::cs, (I(x)::N(y)::s)::s1, listtuples) -> (match (fetch listtuples y) with 
                  | (Some I(y))->execute cs ((I(y+x)::s)::s1) listtuples
                  | _-> execute cs ((Error::I(x)::N(y)::s)::s1) listtuples)
        | (Add::cs, (N(x)::I(y)::s)::s1, listtuples) -> (match (fetch listtuples x) with 
                  | (Some I(x))->execute cs ((I(x+y)::s)::s1) listtuples
                  | _-> execute cs ((Error::N(x)::I(y)::s)::s1) listtuples)
        | (Add::cs, (N(x)::N(y)::s)::s1, listtuples) -> (match (fetch listtuples x , fetch listtuples y) with 
                  | (Some I(x),Some I(y))->execute cs ((I(x+y)::s)::s1) listtuples
                  | _-> execute cs ((Error::N(x)::N(y)::s)::s1) listtuples)
        | (Add::cs, (topstack)::reststacks, listtuples) -> execute cs ((Error::topstack)::reststacks) listtuples 
        | (Sub::cs, (I(x)::I(y)::s)::s1, listtuples) -> execute cs ((I(y-x)::s)::s1) listtuples
        | (Sub::cs, (I(x)::N(y)::s)::s1, listtuples) -> (match (fetch listtuples y) with 
                  | (Some I(y))->execute cs ((I(y-x)::s)::s1) listtuples
                  | _-> execute cs ((Error::I(x)::N(y)::s)::s1) listtuples)
        | (Sub::cs, (N(x)::I(y)::s)::s1, listtuples) -> (match (fetch listtuples x) with 
                  | (Some I(x))->execute cs ((I(y-x)::s)::s1) listtuples
                  | _-> execute cs ((Error::N(x)::I(y)::s)::s1) listtuples)
        | (Sub::cs, (N(x)::N(y)::s)::s1, listtuples) -> (match (fetch listtuples x , fetch listtuples y) with 
                  | (Some I(x),Some I(y))->execute cs ((I(y-x)::s)::s1) listtuples
                  | _-> execute cs ((Error::N(x)::N(y)::s)::s1) listtuples)
        | (Sub::cs, (topstack)::reststacks, listtuples) -> execute cs ((Error::topstack)::reststacks) listtuples 
        | (Div::cs, (I(0)::I(y)::s)::s1, listtuples) -> execute cs ((Error::I(0)::I(y)::s)::s1) listtuples 
        | (Div::cs, (I(x)::I(y)::s)::s1, listtuples) -> execute cs ((I(y/x)::s)::s1) listtuples
        | (Div::cs, (N(x)::I(y)::s)::s1, listtuples) -> (match (fetch listtuples x) with 
                  | (Some I(a))-> if (a!=0) then execute cs ((I(y/a)::s)::s1) listtuples else execute cs ((Error::N(x)::I(y)::s)::s1) listtuples
                  | _-> execute cs ((Error::N(x)::I(y)::s)::s1) listtuples)
        | (Div::cs, (I(0)::N(y)::s)::s1, listtuples) -> execute cs ((Error::I(0)::N(y)::s)::s1) listtuples
        | (Div::cs, (N(x)::N(y)::s)::s1, listtuples) -> (match (fetch listtuples x , fetch listtuples y) with 
                  | (Some I(a),Some I(b))-> if(a!=0) then execute cs ((I(b/a)::s)::s1) listtuples else execute cs ((Error::N(x)::N(y)::s)::s1) listtuples
                  | _-> execute cs ((Error::N(x)::N(y)::s)::s1) listtuples)
        | (Div::cs, (I(x)::N(y)::s)::s1, listtuples) -> (match (fetch listtuples y) with 
                  | (Some I(a))->if(x!=0) then execute cs ((I(a/x)::s)::s1) listtuples else execute cs ((Error::I(x)::N(y)::s)::s1) listtuples
                  | _-> execute cs ((Error::I(x)::N(y)::s)::s1) listtuples)
        | (Div::cs, (topstack)::reststacks, listtuples) -> execute cs ((Error::topstack)::reststacks) listtuples 
        | (Mul::cs, (I(x)::I(y)::s)::s1, listtuples) -> execute cs ((I(x*y)::s)::s1) listtuples(*Basic Addition with two integers available on stack*)
        | (Mul::cs, (I(x)::N(y)::s)::s1, listtuples) -> (match (fetch listtuples y) with 
                  | (Some I(y))->execute cs ((I(y*x)::s)::s1) listtuples
                  | _-> execute cs ((Error::I(x)::N(y)::s)::s1) listtuples)
        | (Mul::cs, (N(x)::I(y)::s)::s1, listtuples) -> (match (fetch listtuples x) with 
                  | (Some I(x))->execute cs ((I(x*y)::s)::s1) listtuples
                  | _-> execute cs ((Error::N(x)::I(y)::s)::s1) listtuples)
        | (Mul::cs, (N(x)::N(y)::s)::s1, listtuples) -> (match (fetch listtuples x , fetch listtuples y) with 
                  | (Some I(x),Some I(y))->execute cs ((I(y*x)::s)::s1) listtuples
                  | _-> execute cs ((Error::N(x)::N(y)::s)::s1) listtuples)
        | (Mul::cs, (topstack)::reststacks, listtuples) -> execute cs ((Error::topstack)::reststacks) listtuples 
        | (Rem::cs, (I(0)::I(y)::s)::s1, listtuples) -> execute cs ((Error::I(0)::I(y)::s)::s1) listtuples
        | (Rem::cs, (I(x)::I(y)::s)::s1, listtuples) -> execute cs ((I(y mod x)::s)::s1) listtuples
        | (Rem::cs, (N(x)::I(y)::s)::s1, listtuples) -> (match (fetch listtuples x) with 
                  | (Some I(a))-> if (a!=0) then execute cs ((I(y/a)::s)::s1) listtuples else execute cs ((Error::N(x)::I(y)::s)::s1) listtuples
                  | _-> execute cs ((Error::N(x)::I(y)::s)::s1) listtuples)
        | (Rem::cs, (I(0)::N(y)::s)::s1, listtuples) -> execute cs ((Error::I(0)::N(y)::s)::s1) listtuples
        | (Rem::cs, (N(x)::N(y)::s)::s1, listtuples) -> (match (fetch listtuples x , fetch listtuples y) with 
                  | (Some I(a),Some I(b))-> if(a!=0) then execute cs ((I(b mod a)::s)::s1) listtuples else execute cs ((Error::N(x)::N(y)::s)::s1) listtuples
                  | _-> execute cs ((Error::N(x)::N(y)::s)::s1) listtuples)
        | (Rem::cs, (I(x)::N(y)::s)::s1, listtuples) -> (match (fetch listtuples y) with 
                  | (Some I(a))->if(x!=0) then execute cs ((I(a mod x)::s)::s1) listtuples else execute cs ((Error::I(x)::N(y)::s)::s1) listtuples
                  | _-> execute cs ((Error::I(x)::N(y)::s)::s1) listtuples)
        | (Rem::cs, (topstack)::reststacks, listtuples) -> execute cs ((Error::topstack)::reststacks) listtuples 
        | (Neg::cs, (I(0)::s)::s1, listtuples) -> execute cs ((I(0)::s)::s1) listtuples
        | (Neg::cs, (I(x)::s)::s1, listtuples) -> execute cs ((I(-x)::s)::s1) listtuples
        | (Neg::cs, (N(x)::s)::s1, listtuples) -> (match (fetch listtuples x) with 
                  | (Some I(a))-> if(a=0) then execute cs ((I(0)::s)::s1) listtuples else execute cs ((I(-a)::s)::s1) listtuples 
                  | _-> execute cs ((Error::N(x)::s)::s1) listtuples)
        | (Neg::cs, (topstack)::reststacks, listtuples) -> execute cs ((Error::topstack)::reststacks) listtuples 
        | (Swap::cs, (x::y::s)::s1, listtuples) -> execute cs ((y::x::s)::s1) listtuples
        | (Swap::cs, (topstack)::reststacks, listtuples) -> execute cs ((Error::topstack)::reststacks) listtuples 
        | (Pop::cs, (x::s)::s1, listtuples) -> execute cs ((s)::s1 )listtuples
        | (Pop::cs, (topstack)::reststacks, listtuples) -> execute cs ((Error::topstack)::reststacks) listtuples 
        | (Cat::cs, (S(x)::S(y)::s)::s1, listtuples) -> execute cs ((S(y^x)::s)::s1) listtuples(*Basic Concat with two strings available on stack*)
        | (Cat::cs, (N(x)::N(y)::s)::s1, listtuples)-> (match (fetch listtuples x , fetch listtuples y) with 
                  | (Some S(x),Some S(y))->execute cs ((S(y^x)::s)::s1) listtuples
                  | _-> execute cs ((Error::N(x)::N(y)::s)::s1) listtuples)
        | (Cat::cs, (S(x)::N(y)::s)::s1, listtuples)-> (match (fetch listtuples y) with 
                  | (Some S(y))->execute cs ((S(y^x)::s)::s1) listtuples
                  | _-> execute cs ((Error::S(x)::N(y)::s)::s1) listtuples)
        | (Cat::cs, (N(x)::S(y)::s)::s1, listtuples)-> (match (fetch listtuples x) with 
                  | (Some S(x))->execute cs ((S(y^x)::s)::s1) listtuples
                  | _-> execute cs ((Error::N(x)::S(y)::s)::s1) listtuples)
        | (Cat::cs, (topstack)::reststacks, listtuples) -> execute cs ((Error::topstack)::reststacks) listtuples 
        | (And::cs, (B(x)::B(y)::s)::s1, listtuples) -> execute cs ((B(y&&x)::s)::s1) listtuples
        | (And::cs, (N(x)::N(y)::s)::s1, listtuples)-> (match (fetch listtuples x , fetch listtuples y) with 
                  | (Some B(x),Some B(y))->execute cs ((B(y&&x)::s)::s1) listtuples
                  | _-> execute cs ((Error::N(x)::N(y)::s)::s1) listtuples)
        | (And::cs, (B(x)::N(y)::s)::s1, listtuples)-> (match (fetch listtuples y) with 
                  | (Some B(y))->execute cs ((B(y&&x)::s)::s1) listtuples
                  | _-> execute cs ((Error::B(x)::N(y)::s)::s1) listtuples)
        | (And::cs, (N(x)::B(y)::s)::s1, listtuples)-> (match (fetch listtuples x) with 
                  | (Some B(x))->execute cs ((B(y&&x)::s)::s1) listtuples
                  | _-> execute cs ((Error::N(x)::B(y)::s)::s1) listtuples)
        | (And::cs, (topstack)::reststacks, listtuples) -> execute cs ((Error::topstack)::reststacks) listtuples 
        | (Or::cs, (B(x)::B(y)::s)::s1, listtuples) -> execute cs ((B(y || x)::s)::s1) listtuples 
        | (Or::cs, (N(x)::N(y)::s)::s1, listtuples)-> (match (fetch listtuples x , fetch listtuples y) with 
                  | (Some B(x),Some B(y))->execute cs ((B(y || x)::s)::s1) listtuples
                  | _-> execute cs ((Error::N(x)::N(y)::s)::s1) listtuples)
        | (Or::cs, (B(x)::N(y)::s)::s1, listtuples)-> (match (fetch listtuples y) with 
                  | (Some B(y))->execute cs ((B(y || x)::s)::s1) listtuples
                  | _-> execute cs ((Error::B(x)::N(y)::s)::s1) listtuples)
        | (Or::cs, (N(x)::B(y)::s)::s1, listtuples)-> (match (fetch listtuples x) with 
                  | (Some B(x))->execute cs ((B(y || x)::s)::s1) listtuples
                  | _-> execute cs ((Error::N(x)::B(y)::s)::s1) listtuples)
        | (Or::cs, (topstack)::reststacks, listtuples) -> execute cs ((Error::topstack)::reststacks) listtuples 
        | (Not::cs, (B(y)::s)::s1, listtuples) -> execute cs ((B(not(y))::s)::s1) listtuples
        | (Not::cs, (N(x)::s)::s1, listtuples) -> (match (fetch listtuples x) with 
                  | (Some B(x))->execute cs ((B(not(x))::s)::s1) listtuples 
                  | _-> execute cs ((Error::N(x)::s)::s1) listtuples)
        | (Not::cs, (topstack)::reststacks, listtuples) -> execute cs ((Error::topstack)::reststacks) listtuples 
        | (Equal::cs, (I(x)::I(y)::s)::s1, listtuples) -> if(x=y) then execute cs ((B(true)::s)::s1) listtuples else execute cs ((B(false)::s)::s1) listtuples
        | (Equal::cs, (N(x)::N(y)::s)::s1, listtuples)-> (match (fetch listtuples x , fetch listtuples y) with 
                  | (Some I(x),Some I(y))->if(x=y) then execute cs ((B(true)::s)::s1) listtuples else execute cs ((B(false)::s)::s1) listtuples
                  | _-> execute cs ((Error::N(x)::N(y)::s)::s1) listtuples)
        | (Equal::cs, (N(x)::I(y)::s)::s1, listtuples)-> (match (fetch listtuples x) with 
                  | (Some I(a))->if(y=a) then execute cs ((B(true)::s)::s1) listtuples else execute cs ((B(false)::s)::s1) listtuples
                  | _-> execute cs ((Error::N(x)::I(y)::s)::s1) listtuples)
        | (Equal::cs, (I(x)::N(y)::s)::s1, listtuples)-> (match (fetch listtuples y) with 
                  | (Some I(b))->if(b=x) then execute cs ((B(true)::s)::s1) listtuples else execute cs ((B(false)::s)::s1) listtuples
                  | _-> execute cs ((Error::I(x)::N(y)::s)::s1) listtuples)
        | (Equal::cs, (topstack)::reststacks, listtuples) -> execute cs ((Error::topstack)::reststacks) listtuples 
        | (Less::cs, (I(x)::I(y)::s)::s1, listtuples) -> if(y<x) then execute cs ((B(true)::s)::s1) listtuples else execute cs ((B(false)::s)::s1) listtuples
        | (Less::cs, (N(x)::N(y)::s)::s1, listtuples)-> (match (fetch listtuples x , fetch listtuples y) with 
                  | (Some I(a),Some I(b))->if(b<a) then execute cs ((B(true)::s)::s1) listtuples else execute cs ((B(false)::s)::s1) listtuples
                  | _-> execute cs ((Error::N(x)::N(y)::s)::s1) listtuples)
        | (Less::cs, (N(x)::I(y)::s)::s1, listtuples)-> (match (fetch listtuples x) with 
                  | (Some I(a))->if(y<a) then execute cs ((B(true)::s)::s1) listtuples else execute cs ((B(false)::s)::s1) listtuples
                  | _-> execute cs ((Error::N(x)::I(y)::s)::s1) listtuples)
        | (Less::cs, (I(x)::N(y)::s)::s1, listtuples)-> (match (fetch listtuples y) with 
                  | (Some I(b))->if(b<x) then execute cs ((B(true)::s)::s1) listtuples else execute cs ((B(false)::s)::s1) listtuples
                  | _-> execute cs ((Error::I(x)::N(y)::s)::s1) listtuples)    
        | (Less::cs, (topstack)::reststacks, listtuples) -> execute cs ((Error::topstack)::reststacks) listtuples 
        | (If::cs, (x::y::B(z)::s)::s1, listtuples) -> if(z=true) then execute cs ((x::s)::s1) listtuples else execute cs ((y::s)::s1) listtuples
        | (If::cs, (x::y::N(z)::s)::s1, listtuples) -> (match (fetch listtuples z) with
                                                        |(Some B(w)) -> if(w=true) then execute cs ((x::s)::s1) listtuples else if(w=false) then execute cs ((y::s)::s1) listtuples else execute cs ((Error::x::y::N(z)::s)::s1) listtuples
                                                        | _-> execute cs ((Error::x::y::N(z)::s)::s1) listtuples)    
        | (If::cs, (x::y::z::s)::s1, listtuples) -> if(z=B(true)) then execute cs ((x::s)::s1) listtuples else if(z=B(false)) then execute cs ((y::s)::s1) listtuples else execute cs ((Error::x::y::z::s)::s1) listtuples
        | (If::cs, (x::y)::s1, listtuples) -> execute cs ((Error::x::y)::s1) listtuples
        | (If::cs, (topstack)::reststacks, listtuples) -> execute cs ((Error::topstack)::reststacks) listtuples 
        | ((Pushi I(x))::cs, (stack)::s1, listtuples) -> execute cs ((I(x)::stack)::s1) listtuples
        | ((Push Error)::cs, (stack)::s1, listtuples) -> execute cs ((Error::stack)::s1) listtuples
        | ((Push Unit)::cs, (stack)::s1, listtuples) -> execute cs ((Unit::stack)::s1) listtuples
        | ((Pushs S(x))::cs, (stack)::s1, listtuples) -> execute cs ((S(x)::stack)::s1) listtuples
        | ((Pushn N(x))::cs, (stack)::s1, listtuples) -> execute cs ((N(x)::stack)::s1) listtuples
        | ((Pushb B(x))::cs, (stack)::s1, listtuples) -> execute cs ((B(x)::stack)::s1) listtuples
        | (Quit::[] , (s)::s1, _) -> (s)::s1
        | (_::cs,(topstack)::reststacks, _)-> execute cs ((Error::topstack)::reststacks) listtuples
        | ([],(topstack)::reststacks, _)-> execute [] ((Error::topstack)::reststacks) listtuples

in let excutelist = execute commandList (([])::[]) (([])::[]) in print_stack (List.concat excutelist);;

(*interpreter("sample_input2.txt","output2.txt")*)

(*| (Bind::cs, _, listtuples) -> execute cs (Error::stack) listtuples 
if(x!=0) then execute cs ((I(y/x)::s)::s1) listtuples else execute cs ((Error::N(x)::I(y)::s)::s1) listtuples

*)