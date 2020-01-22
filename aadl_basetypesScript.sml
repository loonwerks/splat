open HolKernel Parse boolLib bossLib BasicProvers intLib pred_setLib;

open arithmeticTheory integerTheory;

val _ = new_theory "aadl_basetypes";

Datatype: u8  = U8 num
End
Datatype: u16 = U16 num
End
Datatype: u32 = U32 num
End
Datatype: u64 = U64 num
End

Datatype: i8  = I8 int
End
Datatype: i16 = I16 int
End
Datatype: i32 = I32 int
End
Datatype: i64 = I64 int
End


(*---------------------------------------------------------------------------*)
(* Injections                                                                *)
(*---------------------------------------------------------------------------*)

Definition mk_i8 :
  mk_i8 i = if -128i <= i /\ i < 128 then I8 i else ARB
End

Definition mk_i16 :
  mk_i16 i = if -32768i <= i /\ i < 32768 then I16 i else ARB
End

Definition mk_i32 :
  mk_i32 i = if -2147483648i <= i /\ i < 2147483648i then I32 i else ARB
End

Definition mk_i64 :
  mk_i64 i =
    if -9223372036854775808i <= i /\ i < 9223372036854775808i then I64 i else ARB
End

Definition mk_u8 :
  mk_u8 n = if n < 256 then U8 n else ARB
End

Definition mk_u16 :
  mk_u16 n = if n < 65536 then U16 n else ARB
End

Definition mk_u32 :
  mk_u32 n = if n < 4294967296 then U32 n else ARB
End

Definition mk_u64 :
  mk_u64 n =
    if n < 18446744073709551616 then U64 n else ARB
End

(*---------------------------------------------------------------------------*)
(* Projections                                                               *)
(*---------------------------------------------------------------------------*)

Definition i8int :
  i8int (I8 i) = i
End

Definition i16int :
  i16int (I16 i) = i
End

Definition i32int :
  i32int (I32 i) = i
End

Definition i64int :
  i64int (I64 i) = i
End

Definition u8num :
  u8num (U8 n) = n
End

Definition u16num :
  u16num (U16 n) = n
End

Definition u32num :
  u32num (U32 n) = n
End

Definition u64num :
  u64num (U64 n) = n
End

Definition i8_uminus :
 i8_uminus (I8 i) = I8 (-i)
End

Definition i16_uminus :
 i16_uminus (I16 i) = I16 (-i)
End

Definition i32_uminus :
 i32_uminus (I32 i) = I32 (-i)
End

Definition i64_uminus :
 i64_uminus (I64 i) = I64 (-i)
End

Definition u8_signed :
 u8_signed (U8 n) = integer$int_of_num n
End

Definition u16_signed :
 u16_signed (U16 n) = integer$int_of_num n
End

Definition u32_signed :
 u32_signed (U32 n) = integer$int_of_num n
End

Definition u64_signed :
 u64_signed (U64 n) = integer$int_of_num n
End

Definition i8_unsigned :
 i8_unsigned (I8 i) = Num i
End

Definition i16_unsigned :
 i16_unsigned (I16 i) = Num i
End

Definition i32_unsigned :
 i32_unsigned (I32 i) = Num i
End

Definition i64_unsigned :
 i64_unsigned (I64 i) = Num i
End

(*---------------------------------------------------------------------------*)
(* Addition                                                                  *)
(*---------------------------------------------------------------------------*)

Definition u8_plus :
 u8_plus (U8 n1) (U8 n2) = U8 (n1+n2)
End
Definition u16_plus :
 u16_plus (U16 n1) (U16 n2) = U16 (n1+n2)
End
Definition u32_plus :
 u32_plus (U32 n1) (U32 n2) = U32 (n1+n2)
End
Definition u64_plus :
 u64_plus (U64 n1) (U64 n2) = U64 (n1+n2)
End

Definition i8_plus :
 i8_plus (I8 i1) (I8 i2) = I8 (i1+i2)
End
Definition i16_plus :
 i16_plus (I16 i1) (I16 i2) = I16 (i1+i2)
End
Definition i32_plus :
 i32_plus (I32 i1) (I32 i2) = I32 (i1+i2)
End
Definition i64_plus :
 i64_plus (I64 i1) (I64 i2) = I64 (i1+i2)
End

(*---------------------------------------------------------------------------*)
(* Subtraction                                                               *)
(*---------------------------------------------------------------------------*)

Definition u8_minus :
 u8_minus (U8 n1) (U8 n2) = U8 (n1-n2)
End
Definition u16_minus :
 u16_minus (U16 n1) (U16 n2) = U16 (n1-n2)
End
Definition u32_minus :
 u32_minus (U32 n1) (U32 n2) = U32 (n1-n2)
End
Definition u64_minus :
 u64_minus (U64 n1) (U64 n2) = U64 (n1-n2)
End

Definition i8_minus :
 i8_minus (I8 i1) (I8 i2) = I8 (i1-i2)
End
Definition i16_minus :
 i16_minus (I16 i1) (I16 i2) = I16 (i1-i2)
End
Definition i32_minus :
 i32_minus (I32 i1) (I32 i2) = I32 (i1-i2)
End
Definition i64_minus :
 i64_minus (I64 i1) (I64 i2) = I64 (i1-i2)
End

(*---------------------------------------------------------------------------*)
(* Multiplication                                                            *)
(*---------------------------------------------------------------------------*)

Definition u8_mult :
 u8_mult (U8 n1) (U8 n2) = U8 (n1*n2)
End
Definition u16_mult :
 u16_mult (U16 n1) (U16 n2) = U16 (n1*n2)
End
Definition u32_mult :
 u32_mult (U32 n1) (U32 n2) = U32 (n1*n2)
End
Definition u64_mult :
 u64_mult (U64 n1) (U64 n2) = U64 (n1*n2)
End

Definition i8_mult :
 i8_mult (I8 i1) (I8 i2) = I8 (i1*i2)
End
Definition i16_mult :
 i16_mult (I16 i1) (I16 i2) = I16 (i1*i2)
End
Definition i32_mult :
 i32_mult (I32 i1) (I32 i2) = I32 (i1*i2)
End
Definition i64_mult :
 i64_mult (I64 i1) (I64 i2) = I64 (i1*i2)
End

(*---------------------------------------------------------------------------*)
(* Exponentiation                                                            *)
(*---------------------------------------------------------------------------*)

Definition u8_exp :
 u8_exp (U8 n1) (U8 n2) = U8 (n1**n2)
End
Definition u16_exp :
 u16_exp (U16 n1) (U16 n2) = U16 (n1**n2)
End
Definition u32_exp :
 u32_exp (U32 n1) (U32 n2) = U32 (n1**n2)
End
Definition u64_exp :
 u64_exp (U64 n1) (U64 n2) = U64 (n1**n2)
End

Definition i8_exp :
 i8_exp (I8 i) j = I8 (i ** Num(i8int j))
End
Definition i16_exp :
 i16_exp (I16 i) j = I16 (i ** Num(i16int j))
End
Definition i32_exp :
 i32_exp (I32 i) j = I32 (i ** Num(i32int j))
End
Definition i64_exp :
 i64_exp (I64 i) j = I64 (i ** Num(i64int j))
End

(*---------------------------------------------------------------------------*)
(* Division                                                                  *)
(*---------------------------------------------------------------------------*)

Definition u8_div :
 u8_div (U8 n1) (U8 n2) = U8 (n1 DIV n2)
End
Definition u16_div :
 u16_div (U16 n1) (U16 n2) = U16 (n1 DIV n2)
End
Definition u32_div :
 u32_div (U32 n1) (U32 n2) = U32 (n1 DIV n2)
End
Definition u64_div :
 u64_div (U64 n1) (U64 n2) = U64 (n1 DIV n2)
End

Definition i8_div :
 i8_div (I8 i1) (I8 i2) = I8 (i1/i2)
End
Definition i16_div :
 i16_div (I16 i1) (I16 i2) = I16 (i1/i2)
End
Definition i32_div :
 i32_div (I32 i1) (I32 i2) = I32 (i1/i2)
End
Definition i64_div :
 i64_div (I64 i1) (I64 i2) = I64 (i1/i2)
End

(*---------------------------------------------------------------------------*)
(* Mod                                                                       *)
(*---------------------------------------------------------------------------*)

Definition u8_mod :
 u8_mod (U8 n1) (U8 n2) = U8 (n1 MOD n2)
End
Definition u16_mod :
 u16_mod (U16 n1) (U16 n2) = U16 (n1 MOD n2)
End
Definition u32_mod :
 u32_mod (U32 n1) (U32 n2) = U32 (n1 MOD n2)
End
Definition u64_mod :
 u64_mod (U64 n1) (U64 n2) = U64 (n1 MOD n2)
End

Definition i8_mod :
 i8_mod (I8 i1) (I8 i2) = I8 (i1 % i2)
End
Definition i16_mod :
 i16_mod (I16 i1) (I16 i2) = I16 (i1 % i2)
End
Definition i32_mod :
 i32_mod (I32 i1) (I32 i2) = I32 (i1 % i2)
End
Definition i64_mod :
 i64_mod (I64 i1) (I64 i2) = I64 (i1 % i2)
End

(*---------------------------------------------------------------------------*)
(* Arithmetic relations                                                      *)
(*---------------------------------------------------------------------------*)

Definition u8_less :
 u8_less (U8 n1) (U8 n2) <=> n1<n2
End
Definition u16_less :
 u16_less (U16 n1) (U16 n2) <=> n1<n2
End
Definition u32_less :
 u32_less (U32 n1) (U32 n2) <=> n1<n2
End
Definition u64_less :
 u64_less (U64 n1) (U64 n2) <=> n1<n2
End

Definition i8_less :
 i8_less (I8 i1) (I8 i2) <=> i1<i2
End
Definition i16_less :
 i16_less (I16 i1) (I16 i2) <=> i1<i2
End
Definition i32_less :
 i32_less (I32 i1) (I32 i2) <=> i1<i2
End
Definition i64_less :
 i64_less (I64 i1) (I64 i2) <=> i1<i2
End

Definition u8_leq :
 u8_leq (U8 n1) (U8 n2) <=> n1<=n2
End
Definition u16_leq :
 u16_leq (U16 n1) (U16 n2) <=> n1<=n2
End
Definition u32_leq :
 u32_leq (U32 n1) (U32 n2) <=> n1<=n2
End
Definition u64_leq :
 u64_leq (U64 n1) (U64 n2) <=> n1<=n2
End

Definition i8_leq :
 i8_leq (I8 i1) (I8 i2) <=> i1<=i2
End
Definition i16_leq :
 i16_leq (I16 i1) (I16 i2) <=> i1<=i2
End
Definition i32_leq :
 i32_leq (I32 i1) (I32 i2) <=> i1<=i2
End
Definition i64_leq :
 i64_leq (I64 i1) (I64 i2) <=> i1<i2
End

Definition u8_gtr :
 u8_gtr (U8 n1) (U8 n2) <=> n1>n2
End
Definition u16_gtr :
 u16_gtr (U16 n1) (U16 n2) <=> n1>n2
End
Definition u32_gtr :
 u32_gtr (U32 n1) (U32 n2) <=> n1>n2
End
Definition u64_gtr :
 u64_gtr (U64 n1) (U64 n2) <=> n1>n2
End

Definition i8_gtr :
 i8_gtr (I8 i1) (I8 i2) <=> i1>i2
End
Definition i16_gtr :
 i16_gtr (I16 i1) (I16 i2) <=> i1>i2
End
Definition i32_gtr :
 i32_gtr (I32 i1) (I32 i2) <=> i1>i2
End
Definition i64_gtr :
 i64_gtr (I64 i1) (I64 i2) <=> i1>i2
End

Definition u8_geq :
 u8_geq (U8 n1) (U8 n2) <=> n1>=n2
End
Definition u16_geq :
 u16_geq (U16 n1) (U16 n2) <=> n1>=n2
End
Definition u32_geq :
 u32_geq (U32 n1) (U32 n2) <=> n1>=n2
End
Definition u64_geq :
 u64_geq (U64 n1) (U64 n2) <=> n1>=n2
End

Definition i8_geq :
 i8_geq (I8 i1) (I8 i2) <=> i1>=i2
End
Definition i16_geq :
 i16_geq (I16 i1) (I16 i2) <=> i1>=i2
End
Definition i32_geq :
 i32_geq (I32 i1) (I32 i2) <=> i1>=i2
End
Definition i64_geq :
 i64_geq (I64 i1) (I64 i2) <=> i1>=i2
End

val _ = export_theory();
