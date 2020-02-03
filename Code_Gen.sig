signature Code_Gen =
sig

 type dfa =
   {name       : string,
    src_regexp : string,
    finals     : bool list,
    table      : int list list}

 val export_dfa
   : (dfa -> TextIO.outstream -> unit)
     -> string * string
      -> Regexp_Type.regexp
       -> bool list
        -> int list list
         -> unit

 val Slang  : dfa -> TextIO.outstream -> unit

end
