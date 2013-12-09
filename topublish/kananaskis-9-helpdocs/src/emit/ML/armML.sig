signature armML =
sig
  type 'a itself = 'a fcpML.itself
  type 'a word = 'a wordsML.word
  type ('a,'b) cart = ('a,'b) fcpML.cart
  type ('a,'b) sum = ('a,'b) sumML.sum
  type 'a bit0 = 'a fcpML.bit0
  type 'a bit1 = 'a fcpML.bit1
  type num = numML.num
  datatype register
       = r0
       | r1
       | r2
       | r3
       | r4
       | r5
       | r6
       | r7
       | r8
       | r9
       | r10
       | r11
       | r12
       | r13
       | r14
       | r15
       | r8_fiq
       | r9_fiq
       | r10_fiq
       | r11_fiq
       | r12_fiq
       | r13_fiq
       | r14_fiq
       | r13_irq
       | r14_irq
       | r13_svc
       | r14_svc
       | r13_abt
       | r14_abt
       | r13_und
       | r14_und
  datatype psr
       = CPSR | SPSR_fiq | SPSR_irq | SPSR_svc | SPSR_abt | SPSR_und
  datatype mode = usr | fiq | irq | svc | abt | und | sys | safe
  datatype condition
       = EQ
       | CS
       | MI
       | VS
       | HI
       | GE
       | GT
       | AL
       | NE
       | CC
       | PL
       | VC
       | LS
       | LT
       | LE
       | NV
  eqtype exceptions
  eqtype iclass
  datatype ('a,'b)state_inp = state_inp of 'a * (num -> 'b)
  val state_inp_state : ('a, 'b) state_inp -> 'a
  val state_inp_inp : ('a, 'b) state_inp -> num -> 'b
  val state_inp_state_fupd
     : ('a -> 'a) -> ('a, 'b) state_inp -> ('a, 'b) state_inp
  val state_inp_inp_fupd
     : ((num -> 'b) -> num -> 'b) ->
       ('a, 'b) state_inp -> ('a, 'b) state_inp
  datatype ('a,'b)state_out = state_out of 'a * 'b
  val state_out_state : ('a, 'b) state_out -> 'a
  val state_out_out : ('a, 'b) state_out -> 'b
  val state_out_state_fupd
     : ('a -> 'a) -> ('a, 'b) state_out -> ('a, 'b) state_out
  val state_out_out_fupd
     : ('b -> 'b) -> ('a, 'b) state_out -> ('a, 'b) state_out
  type word2 = wordsML.word2
  type word3 = wordsML.word3
  type word4 = wordsML.word4
  type word5 = wordsML.word5
  type word8 = wordsML.word8
  type word12 = wordsML.word12
  type word16 = wordsML.word16
  type word24 = wordsML.word24
  type word30 = wordsML.word30
  type word32 = wordsML.word32
  type registers = register->word32
  type psrs = psr->word32
  type mem = updateML.mem
  type data = updateML.data
  datatype regs = regs of (registers) * (psrs)
  val regs_reg : regs -> registers
  val regs_psr : regs -> psrs
  val regs_reg_fupd : (registers -> registers) -> regs -> regs
  val regs_psr_fupd : (psrs -> psrs) -> regs -> regs
  datatype memop
       = MemRead of word32
       | MemWrite of word32 * data
       | CPWrite of word32
  datatype arm_state = arm_state of regs * word32 * exceptions
  val arm_state_regs : arm_state -> regs
  val arm_state_ireg : arm_state -> word32
  val arm_state_exception : arm_state -> exceptions
  val arm_state_regs_fupd : (regs -> regs) -> arm_state -> arm_state
  val arm_state_ireg_fupd : (word32 -> word32) -> arm_state -> arm_state
  val arm_state_exception_fupd
     : (exceptions -> exceptions) -> arm_state -> arm_state
  datatype arm_output = arm_output of memop list * bool * bool
  val arm_output_transfers : arm_output -> memop list
  val arm_output_cpi : arm_output -> bool
  val arm_output_user : arm_output -> bool
  val arm_output_transfers_fupd
     : (memop list -> memop list) -> arm_output -> arm_output
  val arm_output_cpi_fupd : (bool -> bool) -> arm_output -> arm_output
  val arm_output_user_fupd : (bool -> bool) -> arm_output -> arm_output
  datatype cp_output = cp_output of word32 option list * bool
  val cp_output_data : cp_output -> word32 option list
  val cp_output_absent : cp_output -> bool
  val cp_output_data_fupd
     : (word32 option list -> word32 option list) ->
       cp_output -> cp_output
  val cp_output_absent_fupd : (bool -> bool) -> cp_output -> cp_output
  datatype 'a bus = bus of word32 list * (mem) * num option * 'a
  val bus_data : 'a bus -> word32 list
  val bus_memory : 'a bus -> mem
  val bus_abort : 'a bus -> num option
  val bus_cp_state : 'a bus -> 'a
  val bus_data_fupd : (word32 list -> word32 list) -> 'a bus -> 'a bus
  val bus_memory_fupd : (mem -> mem) -> 'a bus -> 'a bus
  val bus_abort_fupd : (num option -> num option) -> 'a bus -> 'a bus
  val bus_cp_state_fupd : ('a -> 'a) -> 'a bus -> 'a bus
  datatype
  'a
  arm_sys_state = arm_sys_state of (registers) * (psrs) * (mem) * bool *
                                   'a
  val arm_sys_state_registers : 'a arm_sys_state -> registers
  val arm_sys_state_psrs : 'a arm_sys_state -> psrs
  val arm_sys_state_memory : 'a arm_sys_state -> mem
  val arm_sys_state_undefined : 'a arm_sys_state -> bool
  val arm_sys_state_cp_state : 'a arm_sys_state -> 'a
  val arm_sys_state_registers_fupd
     : (registers -> registers) -> 'a arm_sys_state -> 'a arm_sys_state
  val arm_sys_state_psrs_fupd
     : (psrs -> psrs) -> 'a arm_sys_state -> 'a arm_sys_state
  val arm_sys_state_memory_fupd
     : (mem -> mem) -> 'a arm_sys_state -> 'a arm_sys_state
  val arm_sys_state_undefined_fupd
     : (bool -> bool) -> 'a arm_sys_state -> 'a arm_sys_state
  val arm_sys_state_cp_state_fupd
     : ('a -> 'a) -> 'a arm_sys_state -> 'a arm_sys_state
  datatype interrupt
       = Reset of regs | Undef | Prefetch | Dabort of num | Fiq | Irq
  datatype
  arm_input = arm_input of word32 * word32 list * interrupt option *
                           bool
  val arm_input_ireg : arm_input -> word32
  val arm_input_data : arm_input -> word32 list
  val arm_input_interrupt : arm_input -> interrupt option
  val arm_input_no_cp : arm_input -> bool
  val arm_input_ireg_fupd : (word32 -> word32) -> arm_input -> arm_input
  val arm_input_data_fupd
     : (word32 list -> word32 list) -> arm_input -> arm_input
  val arm_input_interrupt_fupd
     : (interrupt option -> interrupt option) -> arm_input -> arm_input
  val arm_input_no_cp_fupd : (bool -> bool) -> arm_input -> arm_input
  datatype
  'a
  coproc = coproc of (bool -> word32 -> bool) *
                     ('a -> bool -> word32 -> 'a) *
                     ('a -> bool -> word32 -> word32) *
                     ('a -> bool -> word32 -> word32 -> 'a) *
                     ('a -> bool -> word32 -> word32 option list) *
                     ('a -> bool -> word32 -> word32 list -> 'a) *
                     ('a -> bool -> word32 -> num)
  val coproc_absent : 'a coproc -> bool -> word32 -> bool
  val coproc_f_cdp : 'a coproc -> 'a -> bool -> word32 -> 'a
  val coproc_f_mrc : 'a coproc -> 'a -> bool -> word32 -> word32
  val coproc_f_mcr : 'a coproc -> 'a -> bool -> word32 -> word32 -> 'a
  val coproc_f_stc
     : 'a coproc -> 'a -> bool -> word32 -> word32 option list
  val coproc_f_ldc
     : 'a coproc -> 'a -> bool -> word32 -> word32 list -> 'a
  val coproc_n_ldc : 'a coproc -> 'a -> bool -> word32 -> num
  val coproc_absent_fupd
     : ((bool -> word32 -> bool) -> bool -> word32 -> bool) ->
       'a coproc -> 'a coproc
  val coproc_f_cdp_fupd
     : (('a -> bool -> word32 -> 'a) -> 'a -> bool -> word32 -> 'a) ->
       'a coproc -> 'a coproc
  val coproc_f_mrc_fupd
     : (('a -> bool -> word32 -> word32) ->
        'a -> bool -> word32 -> word32) -> 'a coproc -> 'a coproc
  val coproc_f_mcr_fupd
     : (('a -> bool -> word32 -> word32 -> 'a) ->
        'a -> bool -> word32 -> word32 -> 'a) -> 'a coproc -> 'a coproc
  val coproc_f_stc_fupd
     : (('a -> bool -> word32 -> word32 option list) ->
        'a -> bool -> word32 -> word32 option list) ->
       'a coproc -> 'a coproc
  val coproc_f_ldc_fupd
     : (('a -> bool -> word32 -> word32 list -> 'a) ->
        'a -> bool -> word32 -> word32 list -> 'a) ->
       'a coproc -> 'a coproc
  val coproc_n_ldc_fupd
     : (('a -> bool -> word32 -> num) -> 'a -> bool -> word32 -> num) ->
       'a coproc -> 'a coproc
  val mem_updates : word30 list ref
  val DECODE_PSR
     : word32 ->
       (bool * (bool * (bool * bool))) * (bool * (bool * word5))
  val DECODE_BRANCH : word32 -> bool * word24
  val DECODE_DATAP
     : word32 -> bool * (word4 * (bool * (word4 * (word4 * word12))))
  val DECODE_MRS : word32 -> bool * word4
  val DECODE_MSR
     : word32 -> bool * (bool * (bool * (bool * (word4 * word12))))
  val DECODE_LDR_STR
     : word32 ->
       bool *
       (bool *
        (bool * (bool * (bool * (bool * (word4 * (word4 * word12)))))))
  val DECODE_MLA_MUL
     : word32 ->
       bool *
       (bool * (bool * (bool * (word4 * (word4 * (word4 * word4))))))
  val DECODE_LDM_STM
     : word32 ->
       bool * (bool * (bool * (bool * (bool * (word4 * word16)))))
  val DECODE_SWP : word32 -> bool * (word4 * (word4 * word4))
  val DECODE_LDC_STC
     : word32 ->
       bool *
       (bool *
        (bool * (bool * (bool * (word4 * (word4 * (word4 * word8)))))))
  val DECODE_LDRH_STRH
     : word32 ->
       bool *
       (bool *
        (bool *
         (bool *
          (bool *
           (word4 * (word4 * (word4 * (bool * (bool * word4)))))))))
  val DECODE_CDP
     : word32 -> word4 * (word4 * (word4 * (word4 * (word3 * word4))))
  val DECODE_MRC_MCR
     : word32 -> word3 * (word4 * (word4 * (word4 * (word3 * word4))))
  val DECODE_CPN : word32 -> word4
  val DECODE_CP : word32 -> iclass
  val USER : mode -> bool
  val mode_reg2num : mode -> word4 -> num
  val DECODE_ARM : word32 -> iclass
  val mode_num : mode -> word5
  val exceptions2num : exceptions -> num
  val register2num : register -> num
  val num2register : num -> register
  val num2condition : num -> condition
  val SET_IFMODE : bool -> bool -> mode -> word32 -> word32
  val REG_READ : registers -> mode -> word4 -> word32
  val REG_WRITE : registers -> mode -> word4 -> word32 -> registers
  val INC_PC : registers -> registers
  val FETCH_PC : registers -> word32
  val SET_NZCV : bool * (bool * (bool * bool)) -> word32 -> word32
  val SET_NZC : bool * (bool * bool) -> word32 -> word32
  val SET_NZ : bool * bool -> word32 -> word32
  val DECODE_MODE : word5 -> mode
  val NZCV : word32 -> bool * (bool * (bool * bool))
  val CARRY : 'b * ('c * ('a * 'd)) -> 'a
  val mode2psr : mode -> psr
  val SPSR_READ : psrs -> mode -> word32
  val CPSR_READ : psrs -> word32
  val CPSR_WRITE : psrs -> word32 -> psrs
  val SPSR_WRITE : psrs -> mode -> word32 -> psrs
  val exception2mode : exceptions -> mode
  val EXCEPTION : regs -> exceptions -> regs
  val BRANCH : regs -> mode -> word32 -> regs
  val LSL : word32 -> word8 -> bool -> bool * word32
  val LSR : word32 -> word8 -> bool -> bool * word32
  val ASR : word32 -> word8 -> bool -> bool * word32
  val ROR : word32 -> word8 -> bool -> bool * word32
  val IMMEDIATE : bool -> word12 -> bool * word32
  val SHIFT_IMMEDIATE2
     : word8 -> word2 -> word32 -> bool -> bool * word32
  val SHIFT_REGISTER2
     : word8 -> word2 -> word32 -> bool -> bool * word32
  val SHIFT_IMMEDIATE
     : registers -> mode -> bool -> word12 -> bool * word32
  val SHIFT_REGISTER
     : registers -> mode -> bool -> word12 -> bool * word32
  val ADDR_MODE1
     : registers -> mode -> bool -> bool -> word12 -> bool * word32
  val ALU_arith
     : (num -> num -> num) ->
       word32 -> word32 -> (bool * (bool * (bool * bool))) * word32
  val ALU_logic : word32 -> (bool * (bool * (bool * bool))) * word32
  val ADD
     : word32 ->
       word32 -> bool -> (bool * (bool * (bool * bool))) * word32
  val SUB
     : word32 ->
       word32 -> bool -> (bool * (bool * (bool * bool))) * word32
  val AND : word32 -> word32 -> (bool * (bool * (bool * bool))) * word32
  val EOR : word32 -> word32 -> (bool * (bool * (bool * bool))) * word32
  val ORR : word32 -> word32 -> (bool * (bool * (bool * bool))) * word32
  val ALU
     : word4 ->
       word32 ->
       word32 -> bool -> (bool * (bool * (bool * bool))) * word32
  val ARITHMETIC : word4 -> bool
  val TEST_OR_COMP : word4 -> bool
  val DATA_PROCESSING : regs -> bool -> mode -> word32 -> regs
  val MRS : regs -> mode -> word32 -> regs
  val MSR : regs -> mode -> word32 -> regs
  val ALU_multiply
     : bool ->
       bool ->
       bool ->
       word32 ->
       'c word ->
       'd word -> 'e word -> bool * (bool * (word32 * word32))
  val MLA_MUL : regs -> mode -> word32 -> regs
  val UP_DOWN : bool -> 'a word -> 'a word -> 'a word
  val ADDR_MODE2
     : registers ->
       mode ->
       bool ->
       bool -> bool -> bool -> word4 -> word12 -> word32 * word32
  val ==> : bool -> bool -> bool
  val LDR_STR
     : regs ->
       bool ->
       mode ->
       word32 -> (bool * word32 list) option -> (memop list, regs) sum
  val ADDR_MODE3
     : registers ->
       mode ->
       bool ->
       bool -> bool -> word4 -> 'a word -> word4 -> word32 * word32
  val LDRH_STRH
     : regs ->
       mode ->
       word32 -> (bool * word32 list) option -> (memop list, regs) sum
  val REGISTER_LIST : word16 -> word4 list
  val ADDRESS_LIST : word32 -> num -> word32 list
  val WB_ADDRESS : bool -> word32 -> num -> word32
  val FIRST_ADDRESS : bool -> bool -> word32 -> word32 -> word32
  val ADDR_MODE4
     : bool ->
       bool -> word32 -> word16 -> word4 list * (word32 list * word32)
  val LDM_LIST
     : registers -> mode -> word4 list -> word32 list -> registers
  val STM_LIST
     : registers -> mode -> (word4 * word32) list -> memop list
  val LDM_STM
     : regs ->
       mode ->
       word32 ->
       (num option * word32 list) option -> (memop list, regs) sum
  val SWP
     : regs ->
       mode ->
       word32 -> (bool * word32 list) option -> (memop list, regs) sum
  val MRC : regs -> mode -> word32 -> 'a word -> regs
  val MCR_OUT : registers -> mode -> 'a word -> memop list
  val ADDR_MODE5
     : registers ->
       mode -> bool -> bool -> word4 -> word8 -> word32 * word32
  val LDC_STC : regs -> mode -> word32 -> bool -> (memop list, regs) sum
  val CONDITION_PASSED2
     : bool * (bool * (bool * bool)) -> condition -> bool
  val CONDITION_PASSED : bool * (bool * (bool * bool)) -> word32 -> bool
  val RUN_ARM : arm_state -> num option -> word32 list -> bool -> regs
  val IS_Reset : interrupt option -> bool
  val PROJ_Dabort : interrupt option -> num option
  val PROJ_Reset : interrupt option -> regs
  val interrupt2exception
     : arm_state -> bool * bool -> interrupt option -> exceptions
  val PROJ_IF_FLAGS : psrs -> bool * bool
  val NEXT_ARM : arm_state -> arm_input -> arm_state
  val OUT_ARM : arm_state -> arm_output
  val TRANSFER
     : bool ->
       word32 option list * (word32 list * mem) ->
       memop -> word32 option list * (word32 list * mem)
  val TRANSFERS
     : arm_output -> 'a -> word32 option list -> mem -> 'a bus
  val OUT_CP : 'a coproc -> 'a -> word32 -> arm_output -> cp_output
  val RUN_CP
     : 'a coproc -> 'a -> bool -> bool -> word32 -> word32 list -> 'a
  val NEXT_ARM_MMU : 'a coproc -> 'a arm_sys_state -> 'a arm_sys_state
  val NEXT_ARM_MEM : 'a arm_sys_state -> 'a arm_sys_state
  val empty_registers : registers
end
