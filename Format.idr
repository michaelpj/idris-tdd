module Main

data Format = Number Format
            | Str Format
            | Lit String Format
            | End

%name Format fmt, fmt2

PrintfType: Format -> Type
PrintfType (Number fmt) = (i: Integer) -> PrintfType fmt
PrintfType (Str fmt) = (s: String) -> PrintfType fmt
PrintfType (Lit str fmt) = PrintfType fmt
PrintfType End = String

printfFmt: (fmt: Format) -> (acc: String) -> PrintfType fmt
printfFmt (Number fmt) acc = \i => printfFmt fmt (acc ++ (show i))
printfFmt (Str fmt) acc = \s => printfFmt fmt (acc ++ s)
printfFmt (Lit x fmt) acc = printfFmt fmt (acc ++ x)
printfFmt End acc = acc

toFormat: (xs : List Char) -> Format
toFormat [] = End
toFormat ('%' :: 'd' :: chars) = Number (toFormat chars)
toFormat ('%' :: 's' :: chars) = Str (toFormat chars)
toFormat ('%' :: chars) = Lit "%" (toFormat chars)
toFormat (c :: chars) = case toFormat chars of
                             Lit lit chars' => Lit (strCons c lit) chars'
                             fmt => Lit (strCons c "") fmt

printf : (fmt : String) -> PrintfType (toFormat (unpack fmt))
printf fmt = printfFmt _ ""
