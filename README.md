# eccb929
Interactive Reed Solomon ECC demo program for GF(929)

User interface - The program prompts for the number of parity elements,
then the number of data elements. It then goes into interactive
mode: "e" - enter data. "c" - change data (errors). "p" - enter erasures.
"z" - zero all data. "n" - encode. "f" - fix (correct). "q" - quit.

The program includes 3 decoders, Peterson Gorenstein Zierler (matrix),
Berlekamp Massey (discrepancy), Sugyama (extended Euclid).
