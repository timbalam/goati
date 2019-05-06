
### NUMBERLITERAL

A *NUMBERLITERAL* describes a literal numeric value.

> type NUMBERLITERAL =
>   BinLiteral [Int] |
>   OctLiteral [Int] |
>   HexLiteral [Int] |
>   DecLiteral [Int] |
>   Decimal [Int] |
>   DecimalFloatFrac [Int] [Int] |
>   DecimalFloatExp [Int] [Int] |
>   DecimalFloatFracExpr [Int] [Int] Exponent
> data Exponent = Exponent (Maybe Sign) [Int]
> data Sign = Positive | Negative

In the textual form,
*BINDIGITS*, *OCTDIGITS*,
*HEXDIGITS* and *INTEGER* describe a literal digit
(respectively *BINDIGIT*s, *OCTDIGIT*s, *HEXDIGIT*and *DIGIT*s) 
followed by a sequence of literal digits and underscores ('_').
*BINLITERAL*, *OCTLITERAL*,
*HEXLITERAL* and *DECLITERAL* describe integer values with a prefix-determined digits
(respectively prefixes '0b', '0o', '0x' and '0d',
and *BINDIGIT*, *OCTDIGIT*, *HEXIDIGIT* and *DIGIT* digits).
A *DECIMALFLOAT* can have several forms.
It can begin with an optional plus sign ('+') followed by an *INTEGER*,
and optionally followed by a *FRACTIONAL* part and/or an *EXPONENT* part.
Alternatively it can begin with a *FRACTIONAL* part,
optionally followed by an *EXPONENT* part.
A *FRACTIONAL* begins with a period ('.') followed by an *INTEGER*.
A *POSITIVE* sign is a plus character ('+').
A *NEGATIVE* sign is a minus character ('-').
*BINLITERAL*, *OCTLITERAL*, *HEXLITERAL* 

    NUMBERLITERAL :=
      BINLITERAL |
      OCTLITERAL |
      HEXLITERAL |
      DECLITERAL |
      DECIMAL [FLOAT] |
      FLOAT
    BINLITERAL := '0b' BINDIGITS
    BINDIGITS := BINDIGIT [['_'] BINDIGITS]
    BINDIGIT := '0' | '1'
    OCTLITERAL := '0o' OCTDIGITS
    OCTDIGITS := OCTDIGIT [['_'] OCTDIGITS]
    OCTDIGIT := '0' | ... | '7'
    HEXLITERAL := '0x' HEXDIGITS
    HEXDIGITS := HEXDIGIT [['_'] HEXDIGITS]
    HEXDIGIT := '0' | ... | '9' | 'a' | ... | 'f'
    DECLITERAL := '0d' INTEGER
    INTEGER := DIGIT [['_'] INTEGER]
    DIGIT := '0' | ... | '9'
    DECIMAL := ['+'] INTEGER
    FLOAT := FRACTIONAL [EXPONENT] | EXPONENT
    FRACTIONAL := '.' INTEGER
    EXPONENT := ECHAR [SIGN] INTEGER
    ECHAR := 'e' | 'E'
    SIGN := '+' | '-'
    
    