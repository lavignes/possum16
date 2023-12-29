syn clear
syn case ignore

syn match pasmIdentifier "[a-z_\.][a-z0-9_\.]*"
syn match pasmGlobalLabel "^[a-z_][a-z0-9_\.]*"
syn match pasmLocalLabel "^\.[a-z_][a-z0-9_]*"

syn keyword pasmRegister x y s *

syn match pasmOperator display "\%(+\|-\|/\|*\|\^\|\~\|&\||\|!\|>\|<\|%\)=\?"
syn match pasmOperator display "&&\|||\|<<\|>>\|\~>"

syn keyword pasmOpcode adc and asl bcc bcs beq bit bmi bne bpl bra brk brl bvc bvs
syn keyword pasmOpcode clc cld cli clv cmp cop cpx cpy dec dex dey eor inc inx iny
syn keyword pasmOpcode jml jmp jsl jsr lda ldx ldy lsr mvn mvp nop ora pea pei per
syn keyword pasmOpcode pha phb phd pjk php phx phy pla plb pld plp plx ply
syn keyword pasmOpcode rep rol ror rti rtl rts sbc sec sed sei sep sta stp stx sty stz
syn keyword pasmOpcode tax tay tcd tcs tdc trb tsb tsc tsx txa txs txy tya tyx wai wdc xba xce

syn keyword pasmDirective byt wrd dat prg pad adj put iff ifd ifn end i08 i16 a08 a16 c02 c16
syn keyword pasmDirective mac equ

syn match pasmComment ";.*" contains=pasmTodo
syn keyword pasmTodo  contained todo fixme xxx warning danger note notice bug
syn region pasmString start=+"+ end=+"+

syn match pasmNumber "[0-9]\+"
syn match pasmNumber "\$[0-9a-fA-F]\+"
syn match pasmNumber "%[01]\+"
syn match pasmNumber "'[!-~]"

syn case match

hi def link pasmComment       Comment
hi def link pasmNumber        Number
hi def link pasmString	      String
hi def link pasmIdentifier    Identifier
hi def link pasmOpcode        Keyword
hi def link pasmDirective     PreProc
hi def link pasmGlobalLabel   Function
hi def link pasmLocalLabel    Function
hi def link pasmTodo          Todo

let b:current_syntax = "pasm"
set ts=8
set sw=8
set noet
