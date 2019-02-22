module Language.C.Keywords

-- teh6: as per the C99 (ISO/IEC 9899:1999) standard

--------------
-- KEYWORDS --
--------------
data CKeyword : String -> Type where
  CAuto : CKeyword "auto"
  CBreak : CKeyword "break"
  CCase : CKeyword "case"
  CChar : CKeyword "char"
  CConst : CKeyword "const"
  CContinue : CKeyword "continue"
  CDefault : CKeyword "default"
  CDo : CKeyword "do"
  CDouble : CKeyword "double"
  CElse : CKeyword "else"
  CEnum : CKeyword "enum"
  CExtern : CKeyword "extern"
  CFloat : CKeyword "float"
  CFor : CKeyword "for"
  CGoto : CKeyword "goto"
  CIf : CKeyword "if"
  CInline : CKeyword "inline"
  CInt : CKeyword "int"
  CLong : CKeyword "long"
  CRegister : CKeyword "register"
  CRestrict : CKeyword "restrict"
  CReturn : CKeyword "return"
  CShort : CKeyword "short"
  CSigned : CKeyword "signed"
  CSizeof : CKeyword "sizeof"
  CStatic : CKeyword "static"
  CStruct : CKeyword "struct"
  CSwitch : CKeyword "switch"
  CTypedef : CKeyword "typedef"
  CUnion : CKeyword "union"
  CUnsigned : CKeyword "unsigned"
  CVoid : CKeyword "void"
  CVolatile : CKeyword "volatile"
  CWhile : CKeyword "while"
  CUnderBool : CKeyword "_Bool"
  CUnderComplex : CKeyword "_Complex"
  CUnderImaginary : CKeyword "_Imaginary"

