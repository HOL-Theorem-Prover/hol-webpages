structure armML :> armML =
struct
  nonfix empty_registers NEXT_ARM_MEM NEXT_ARM_MMU RUN_CP OUT_CP
         TRANSFERS TRANSFER OUT_ARM NEXT_ARM PROJ_IF_FLAGS
         interrupt2exception PROJ_Reset PROJ_Dabort IS_Reset RUN_ARM
         CONDITION_PASSED CONDITION_PASSED2 LDC_STC ADDR_MODE5 MCR_OUT
         MRC SWP LDM_STM STM_LIST LDM_LIST ADDR_MODE4 FIRST_ADDRESS
         WB_ADDRESS ADDRESS_LIST REGISTER_LIST LDRH_STRH ADDR_MODE3
         LDR_STR ==> ADDR_MODE2 UP_DOWN MLA_MUL ALU_multiply MSR MRS
         DATA_PROCESSING TEST_OR_COMP ARITHMETIC ALU ORR EOR AND SUB ADD
         ALU_logic ALU_arith ADDR_MODE1 SHIFT_REGISTER SHIFT_IMMEDIATE
         SHIFT_REGISTER2 SHIFT_IMMEDIATE2 IMMEDIATE ROR ASR LSR LSL
         BRANCH EXCEPTION exception2mode SPSR_WRITE CPSR_WRITE CPSR_READ
         SPSR_READ mode2psr CARRY NZCV DECODE_MODE SET_NZ SET_NZC
         SET_NZCV FETCH_PC INC_PC REG_WRITE REG_READ SET_IFMODE
         num2condition num2register register2num exceptions2num mode_num
         DECODE_ARM mode_reg2num USER DECODE_CP DECODE_CPN
         DECODE_MRC_MCR DECODE_CDP DECODE_LDRH_STRH DECODE_LDC_STC
         DECODE_SWP DECODE_LDM_STM DECODE_MLA_MUL DECODE_LDR_STR
         DECODE_MSR DECODE_MRS DECODE_DATAP DECODE_BRANCH DECODE_PSR
         coproc_n_ldc_fupd coproc_f_ldc_fupd coproc_f_stc_fupd
         coproc_f_mcr_fupd coproc_f_mrc_fupd coproc_f_cdp_fupd
         coproc_absent_fupd coproc_n_ldc coproc_f_ldc coproc_f_stc
         coproc_f_mcr coproc_f_mrc coproc_f_cdp coproc_absent coproc
         arm_input_no_cp_fupd arm_input_interrupt_fupd
         arm_input_data_fupd arm_input_ireg_fupd arm_input_no_cp
         arm_input_interrupt arm_input_data arm_input_ireg arm_input Irq
         Fiq Dabort Prefetch Undef Reset arm_sys_state_cp_state_fupd
         arm_sys_state_undefined_fupd arm_sys_state_memory_fupd
         arm_sys_state_psrs_fupd arm_sys_state_registers_fupd
         arm_sys_state_cp_state arm_sys_state_undefined
         arm_sys_state_memory arm_sys_state_psrs arm_sys_state_registers
         arm_sys_state bus_cp_state_fupd bus_abort_fupd bus_memory_fupd
         bus_data_fupd bus_cp_state bus_abort bus_memory bus_data bus
         cp_output_absent_fupd cp_output_data_fupd cp_output_absent
         cp_output_data cp_output arm_output_user_fupd
         arm_output_cpi_fupd arm_output_transfers_fupd arm_output_user
         arm_output_cpi arm_output_transfers arm_output
         arm_state_exception_fupd arm_state_ireg_fupd
         arm_state_regs_fupd arm_state_exception arm_state_ireg
         arm_state_regs arm_state CPWrite MemWrite MemRead regs_psr_fupd
         regs_reg_fupd regs_psr regs_reg regs state_out_out_fupd
         state_out_state_fupd state_out_out state_out_state state_out
         state_inp_inp_fupd state_inp_state_fupd state_inp_inp
         state_inp_state state_inp unexec ldc_stc mrc mcr cdp_und swi_ex
         br ldm_stm ldrh_strh ldr_str mla_mul data_proc msr mrs swp fast
         interrupt address dabort pabort software undefined reset NV LE
         LT LS VC PL CC NE AL GT GE HI VS MI CS EQ safe sys und abt svc
         irq fiq usr SPSR_und SPSR_abt SPSR_svc SPSR_irq SPSR_fiq CPSR
         r14_und r13_und r14_abt r13_abt r14_svc r13_svc r14_irq r13_irq
         r14_fiq r13_fiq r12_fiq r11_fiq r10_fiq r9_fiq r8_fiq r15 r14
         r13 r12 r11 r10 r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 * / div mod + - ^
         @ <> > < >= <= := o before;

  open numML
  open sumML
  open optionML
  open setML
  open fcpML
  open listML
  open rich_listML
  open bitML
  open wordsML
  open updateML

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
  datatype exceptions
       = reset
       | undefined
       | software
       | pabort
       | dabort
       | address
       | interrupt
       | fast
  datatype iclass
       = swp
       | mrs
       | msr
       | data_proc
       | mla_mul
       | ldr_str
       | ldrh_strh
       | ldm_stm
       | br
       | swi_ex
       | cdp_und
       | mcr
       | mrc
       | ldc_stc
       | unexec
  datatype ('a,'b)state_inp = state_inp of 'a * (num -> 'b)
  fun state_inp_state (state_inp(v1,v2)) = v1

  fun state_inp_inp (state_inp(v1,v2)) = v2

  fun state_inp_state_fupd f (state_inp(v1,v2)) = state_inp(f v1,v2)

  fun state_inp_inp_fupd f (state_inp(v1,v2)) = state_inp(v1,f v2)

  datatype ('a,'b)state_out = state_out of 'a * 'b
  fun state_out_state (state_out(v1,v2)) = v1

  fun state_out_out (state_out(v1,v2)) = v2

  fun state_out_state_fupd f (state_out(v1,v2)) = state_out(f v1,v2)

  fun state_out_out_fupd f (state_out(v1,v2)) = state_out(v1,f v2)

  type registers = register->word32
  type psrs = psr->word32
  type mem = updateML.mem
  type data = updateML.data
  datatype regs = regs of (registers) * (psrs)
  fun regs_reg (regs(v1,v2)) = v1

  fun regs_psr (regs(v1,v2)) = v2

  fun regs_reg_fupd f (regs(v1,v2)) = regs(f v1,v2)

  fun regs_psr_fupd f (regs(v1,v2)) = regs(v1,f v2)

  datatype memop
       = MemRead of word32
       | MemWrite of word32 * data
       | CPWrite of word32
  datatype arm_state = arm_state of regs * word32 * exceptions
  fun arm_state_regs (arm_state(v1,v2,v3)) = v1

  fun arm_state_ireg (arm_state(v1,v2,v3)) = v2

  fun arm_state_exception (arm_state(v1,v2,v3)) = v3

  fun arm_state_regs_fupd f (arm_state(v1,v2,v3)) =
        arm_state(f v1,v2,v3)

  fun arm_state_ireg_fupd f (arm_state(v1,v2,v3)) =
        arm_state(v1,f v2,v3)

  fun arm_state_exception_fupd f (arm_state(v1,v2,v3)) =
        arm_state(v1,v2,f v3)

  datatype arm_output = arm_output of memop list * bool * bool
  fun arm_output_transfers (arm_output(v1,v2,v3)) = v1

  fun arm_output_cpi (arm_output(v1,v2,v3)) = v2

  fun arm_output_user (arm_output(v1,v2,v3)) = v3

  fun arm_output_transfers_fupd f (arm_output(v1,v2,v3)) =
        arm_output(f v1,v2,v3)

  fun arm_output_cpi_fupd f (arm_output(v1,v2,v3)) =
        arm_output(v1,f v2,v3)

  fun arm_output_user_fupd f (arm_output(v1,v2,v3)) =
        arm_output(v1,v2,f v3)

  datatype cp_output = cp_output of word32 option list * bool
  fun cp_output_data (cp_output(v1,v2)) = v1

  fun cp_output_absent (cp_output(v1,v2)) = v2

  fun cp_output_data_fupd f (cp_output(v1,v2)) = cp_output(f v1,v2)

  fun cp_output_absent_fupd f (cp_output(v1,v2)) = cp_output(v1,f v2)

  datatype 'a bus = bus of word32 list * (mem) * num option * 'a
  fun bus_data (bus(v1,v2,v3,v4)) = v1

  fun bus_memory (bus(v1,v2,v3,v4)) = v2

  fun bus_abort (bus(v1,v2,v3,v4)) = v3

  fun bus_cp_state (bus(v1,v2,v3,v4)) = v4

  fun bus_data_fupd f (bus(v1,v2,v3,v4)) = bus(f v1,v2,v3,v4)

  fun bus_memory_fupd f (bus(v1,v2,v3,v4)) = bus(v1,f v2,v3,v4)

  fun bus_abort_fupd f (bus(v1,v2,v3,v4)) = bus(v1,v2,f v3,v4)

  fun bus_cp_state_fupd f (bus(v1,v2,v3,v4)) = bus(v1,v2,v3,f v4)

  datatype
  'a
  arm_sys_state = arm_sys_state of (registers) * (psrs) * (mem) * bool *
                                   'a
  fun arm_sys_state_registers (arm_sys_state(v1,v2,v3,v4,v5)) = v1

  fun arm_sys_state_psrs (arm_sys_state(v1,v2,v3,v4,v5)) = v2

  fun arm_sys_state_memory (arm_sys_state(v1,v2,v3,v4,v5)) = v3

  fun arm_sys_state_undefined (arm_sys_state(v1,v2,v3,v4,v5)) = v4

  fun arm_sys_state_cp_state (arm_sys_state(v1,v2,v3,v4,v5)) = v5

  fun arm_sys_state_registers_fupd f (arm_sys_state(v1,v2,v3,v4,v5)) =
        arm_sys_state(f v1,v2,v3,v4,v5)

  fun arm_sys_state_psrs_fupd f (arm_sys_state(v1,v2,v3,v4,v5)) =
        arm_sys_state(v1,f v2,v3,v4,v5)

  fun arm_sys_state_memory_fupd f (arm_sys_state(v1,v2,v3,v4,v5)) =
        arm_sys_state(v1,v2,f v3,v4,v5)

  fun arm_sys_state_undefined_fupd f (arm_sys_state(v1,v2,v3,v4,v5)) =
        arm_sys_state(v1,v2,v3,f v4,v5)

  fun arm_sys_state_cp_state_fupd f (arm_sys_state(v1,v2,v3,v4,v5)) =
        arm_sys_state(v1,v2,v3,v4,f v5)

  datatype interrupt
       = Reset of regs | Undef | Prefetch | Dabort of num | Fiq | Irq
  datatype
  arm_input = arm_input of word32 * word32 list * interrupt option *
                           bool
  fun arm_input_ireg (arm_input(v1,v2,v3,v4)) = v1

  fun arm_input_data (arm_input(v1,v2,v3,v4)) = v2

  fun arm_input_interrupt (arm_input(v1,v2,v3,v4)) = v3

  fun arm_input_no_cp (arm_input(v1,v2,v3,v4)) = v4

  fun arm_input_ireg_fupd f (arm_input(v1,v2,v3,v4)) =
        arm_input(f v1,v2,v3,v4)

  fun arm_input_data_fupd f (arm_input(v1,v2,v3,v4)) =
        arm_input(v1,f v2,v3,v4)

  fun arm_input_interrupt_fupd f (arm_input(v1,v2,v3,v4)) =
        arm_input(v1,v2,f v3,v4)

  fun arm_input_no_cp_fupd f (arm_input(v1,v2,v3,v4)) =
        arm_input(v1,v2,v3,f v4)

  datatype
  'a
  coproc = coproc of (bool -> word32 -> bool) *
                     ('a -> bool -> word32 -> 'a) *
                     ('a -> bool -> word32 -> word32) *
                     ('a -> bool -> word32 -> word32 -> 'a) *
                     ('a -> bool -> word32 -> word32 option list) *
                     ('a -> bool -> word32 -> word32 list -> 'a) *
                     ('a -> bool -> word32 -> num)
  fun coproc_absent (coproc(v1,v2,v3,v4,v5,v6,v7)) = v1

  fun coproc_f_cdp (coproc(v1,v2,v3,v4,v5,v6,v7)) = v2

  fun coproc_f_mrc (coproc(v1,v2,v3,v4,v5,v6,v7)) = v3

  fun coproc_f_mcr (coproc(v1,v2,v3,v4,v5,v6,v7)) = v4

  fun coproc_f_stc (coproc(v1,v2,v3,v4,v5,v6,v7)) = v5

  fun coproc_f_ldc (coproc(v1,v2,v3,v4,v5,v6,v7)) = v6

  fun coproc_n_ldc (coproc(v1,v2,v3,v4,v5,v6,v7)) = v7

  fun coproc_absent_fupd f (coproc(v1,v2,v3,v4,v5,v6,v7)) =
        coproc(f v1,v2,v3,v4,v5,v6,v7)

  fun coproc_f_cdp_fupd f (coproc(v1,v2,v3,v4,v5,v6,v7)) =
        coproc(v1,f v2,v3,v4,v5,v6,v7)

  fun coproc_f_mrc_fupd f (coproc(v1,v2,v3,v4,v5,v6,v7)) =
        coproc(v1,v2,f v3,v4,v5,v6,v7)

  fun coproc_f_mcr_fupd f (coproc(v1,v2,v3,v4,v5,v6,v7)) =
        coproc(v1,v2,v3,f v4,v5,v6,v7)

  fun coproc_f_stc_fupd f (coproc(v1,v2,v3,v4,v5,v6,v7)) =
        coproc(v1,v2,v3,v4,f v5,v6,v7)

  fun coproc_f_ldc_fupd f (coproc(v1,v2,v3,v4,v5,v6,v7)) =
        coproc(v1,v2,v3,v4,v5,f v6,v7)

  fun coproc_n_ldc_fupd f (coproc(v1,v2,v3,v4,v5,v6,v7)) =
        coproc(v1,v2,v3,v4,v5,v6,f v7)

  val mem_updates = ref ([]: word30 list)
  fun DECODE_PSR w =
        let val (q0,m) = DIVMOD_2EXP (fromString "5") (w2n w)
            val (q1,i) = DIVMOD_2EXP ONE (DIV2 q0)
            val (q2,f) = DIVMOD_2EXP ONE q1
            val (q3,V) = DIVMOD_2EXP ONE (DIV_2EXP (fromString "20") q2)
            val (q4,C) = DIVMOD_2EXP ONE q3
            val (q5,Z) = DIVMOD_2EXP ONE q4
        in
           ((ODD q5,(Z = ONE,(C = ONE,V = ONE))),
            (f = ONE,
             (i = ONE,n2w_itself (m,(ITSELF (fromString "5"))))))
        end

  fun DECODE_BRANCH w =
        let val (L,offset) = DIVMOD_2EXP (fromString "24") (w2n w)
        in
           (ODD L,n2w_itself (offset,(ITSELF (fromString "24"))))
        end

  fun DECODE_DATAP w =
        let val (q0,opnd2) = DIVMOD_2EXP (fromString "12") (w2n w)
            val (q1,Rd) = DIVMOD_2EXP (fromString "4") q0
            val (q2,Rn) = DIVMOD_2EXP (fromString "4") q1
            val (q3,S) = DIVMOD_2EXP ONE q2
            val (q4,opcode) = DIVMOD_2EXP (fromString "4") q3
        in
           (ODD q4,
            (n2w_itself (opcode,(ITSELF (fromString "4"))),
             (S = ONE,
              (n2w_itself (Rn,(ITSELF (fromString "4"))),
               (n2w_itself (Rd,(ITSELF (fromString "4"))),
                n2w_itself (opnd2,(ITSELF (fromString "12"))))))))
        end

  fun DECODE_MRS w =
        let val (q,Rd) =
                DIVMOD_2EXP (fromString "4")
                  (DIV_2EXP (fromString "12") (w2n w))
        in
           (ODD (DIV_2EXP (fromString "6") q),
            n2w_itself (Rd,(ITSELF (fromString "4"))))
        end

  fun DECODE_MSR w =
        let val (q0,opnd) = DIVMOD_2EXP (fromString "12") (w2n w)
            val (q1,bit16) =
                DIVMOD_2EXP ONE (DIV_2EXP (fromString "4") q0)
            val (q2,bit19) = DIVMOD_2EXP ONE (DIV_2EXP TWO q1)
            val (q3,R) = DIVMOD_2EXP ONE (DIV_2EXP TWO q2)
        in
           (ODD (DIV_2EXP TWO q3),
            (R = ONE,
             (bit19 = ONE,
              (bit16 = ONE,
               (n2w_itself
                  (MOD_2EXP (fromString "4") opnd,
                   (ITSELF (fromString "4"))),
                n2w_itself (opnd,(ITSELF (fromString "12"))))))))
        end

  fun DECODE_LDR_STR w =
        let val (q0,offset) = DIVMOD_2EXP (fromString "12") (w2n w)
            val (q1,Rd) = DIVMOD_2EXP (fromString "4") q0
            val (q2,Rn) = DIVMOD_2EXP (fromString "4") q1
            val (q3,L) = DIVMOD_2EXP ONE q2
            val (q4,W) = DIVMOD_2EXP ONE q3
            val (q5,B) = DIVMOD_2EXP ONE q4
            val (q6,U) = DIVMOD_2EXP ONE q5
            val (q7,P) = DIVMOD_2EXP ONE q6
        in
           (ODD q7,
            (P = ONE,
             (U = ONE,
              (B = ONE,
               (W = ONE,
                (L = ONE,
                 (n2w_itself (Rn,(ITSELF (fromString "4"))),
                  (n2w_itself (Rd,(ITSELF (fromString "4"))),
                   n2w_itself
                     (offset,(ITSELF (fromString "12")))))))))))
        end

  fun DECODE_MLA_MUL w =
        let val (q0,Rm) = DIVMOD_2EXP (fromString "4") (w2n w)
            val (q1,Rs) =
                DIVMOD_2EXP (fromString "4")
                  (DIV_2EXP (fromString "4") q0)
            val (q2,Rn) = DIVMOD_2EXP (fromString "4") q1
            val (q3,Rd) = DIVMOD_2EXP (fromString "4") q2
            val (q4,S) = DIVMOD_2EXP ONE q3
            val (q5,A) = DIVMOD_2EXP ONE q4
            val (q6,Sgn) = DIVMOD_2EXP ONE q5
        in
           (ODD q6,
            (Sgn = ONE,
             (A = ONE,
              (S = ONE,
               (n2w_itself (Rd,(ITSELF (fromString "4"))),
                (n2w_itself (Rn,(ITSELF (fromString "4"))),
                 (n2w_itself (Rs,(ITSELF (fromString "4"))),
                  n2w_itself (Rm,(ITSELF (fromString "4"))))))))))
        end

  fun DECODE_LDM_STM w =
        let val (q0,list) = DIVMOD_2EXP (fromString "16") (w2n w)
            val (q1,Rn) = DIVMOD_2EXP (fromString "4") q0
            val (q2,L) = DIVMOD_2EXP ONE q1
            val (q3,W) = DIVMOD_2EXP ONE q2
            val (q4,S) = DIVMOD_2EXP ONE q3
            val (q5,U) = DIVMOD_2EXP ONE q4
        in
           (ODD q5,
            (U = ONE,
             (S = ONE,
              (W = ONE,
               (L = ONE,
                (n2w_itself (Rn,(ITSELF (fromString "4"))),
                 n2w_itself (list,(ITSELF (fromString "16")))))))))
        end

  fun DECODE_SWP w =
        let val (q0,Rm) = DIVMOD_2EXP (fromString "4") (w2n w)
            val (q1,Rd) =
                DIVMOD_2EXP (fromString "4")
                  (DIV_2EXP (fromString "8") q0)
            val (q2,Rn) = DIVMOD_2EXP (fromString "4") q1
        in
           (ODD (DIV_2EXP TWO q2),
            (n2w_itself (Rn,(ITSELF (fromString "4"))),
             (n2w_itself (Rd,(ITSELF (fromString "4"))),
              n2w_itself (Rm,(ITSELF (fromString "4"))))))
        end

  fun DECODE_LDC_STC w =
        let val (q0,offset) = DIVMOD_2EXP (fromString "8") (w2n w)
            val (q1,CPN) = DIVMOD_2EXP (fromString "4") q0
            val (q2,CRd) = DIVMOD_2EXP (fromString "4") q1
            val (q3,Rn) = DIVMOD_2EXP (fromString "4") q2
            val (q4,L) = DIVMOD_2EXP ONE q3
            val (q5,W) = DIVMOD_2EXP ONE q4
            val (q6,N) = DIVMOD_2EXP ONE q5
            val (q7,U) = DIVMOD_2EXP ONE q6
        in
           (ODD q7,
            (U = ONE,
             (N = ONE,
              (W = ONE,
               (L = ONE,
                (n2w_itself (Rn,(ITSELF (fromString "4"))),
                 (n2w_itself (CRd,(ITSELF (fromString "4"))),
                  (n2w_itself (CPN,(ITSELF (fromString "4"))),
                   n2w_itself (offset,(ITSELF (fromString "8")))))))))))
        end

  fun DECODE_LDRH_STRH w =
        let val (q0,offsetL) = DIVMOD_2EXP (fromString "4") (w2n w)
            val (q1,H) = DIVMOD_2EXP ONE (DIV2 q0)
            val (q2,S) = DIVMOD_2EXP ONE q1
            val (q3,offsetH) = DIVMOD_2EXP (fromString "4") (DIV2 q2)
            val (q4,Rd) = DIVMOD_2EXP (fromString "4") q3
            val (q5,Rn) = DIVMOD_2EXP (fromString "4") q4
            val (q6,L) = DIVMOD_2EXP ONE q5
            val (q7,W) = DIVMOD_2EXP ONE q6
            val (q8,I) = DIVMOD_2EXP ONE q7
            val (q9,U) = DIVMOD_2EXP ONE q8
        in
           (ODD q9,
            (U = ONE,
             (I = ONE,
              (W = ONE,
               (L = ONE,
                (n2w_itself (Rn,(ITSELF (fromString "4"))),
                 (n2w_itself (Rd,(ITSELF (fromString "4"))),
                  (n2w_itself (offsetH,(ITSELF (fromString "4"))),
                   (S = ONE,
                    (H = ONE,
                     n2w_itself
                       (offsetL,(ITSELF (fromString "4")))))))))))))
        end

  fun DECODE_CDP w =
        let val (q0,CRm) = DIVMOD_2EXP (fromString "4") (w2n w)
            val (q1,Cop2) = DIVMOD_2EXP (fromString "3") (DIV2 q0)
            val (q2,CPN) = DIVMOD_2EXP (fromString "4") q1
            val (q3,CRd) = DIVMOD_2EXP (fromString "4") q2
            val (q4,CRn) = DIVMOD_2EXP (fromString "4") q3
        in
           (n2w_itself
              (MOD_2EXP (fromString "4") q4,(ITSELF (fromString "4"))),
            (n2w_itself (CRn,(ITSELF (fromString "4"))),
             (n2w_itself (CRd,(ITSELF (fromString "4"))),
              (n2w_itself (CPN,(ITSELF (fromString "4"))),
               (n2w_itself (Cop2,(ITSELF (fromString "3"))),
                n2w_itself (CRm,(ITSELF (fromString "4"))))))))
        end

  fun DECODE_MRC_MCR w =
        let val (q0,CRm) = DIVMOD_2EXP (fromString "4") (w2n w)
            val (q1,Cop2) = DIVMOD_2EXP (fromString "3") (DIV2 q0)
            val (q2,CPN) = DIVMOD_2EXP (fromString "4") q1
            val (q3,CRd) = DIVMOD_2EXP (fromString "4") q2
            val (q4,CRn) = DIVMOD_2EXP (fromString "4") q3
        in
           (n2w_itself
              (MOD_2EXP (fromString "3") (DIV2 q4),
               (ITSELF (fromString "3"))),
            (n2w_itself (CRn,(ITSELF (fromString "4"))),
             (n2w_itself (CRd,(ITSELF (fromString "4"))),
              (n2w_itself (CPN,(ITSELF (fromString "4"))),
               (n2w_itself (Cop2,(ITSELF (fromString "3"))),
                n2w_itself (CRm,(ITSELF (fromString "4"))))))))
        end

  fun DECODE_CPN w =
        word_extract_itself (ITSELF (fromString "4")) (fromString "11")
          (fromString "8") w

  fun DECODE_CP w =
        if word_index w (fromString "25") then
          (if
             word_index w (fromString "4") andalso
             word_index w (fromString "27")
           then
             (if word_index w (fromString "20") then mrc else mcr)
           else cdp_und) else ldc_stc

  fun USER m = (m = usr) orelse ((m = sys) orelse (m = safe))

  fun mode_reg2num m w =
        let val n = w2n w
        in
           if
             (n = (fromString "15")) orelse
             (USER m orelse
              ((m = fiq) andalso < n (fromString "8") orelse
               not (m = fiq) andalso < n (fromString "13")))
           then
          n
        else
          case m
           of usr => raise Fail "ARB"
            | fiq => + n (fromString "8")
            | irq => + n (fromString "10")
            | svc => + n (fromString "12")
            | abt => + n (fromString "14")
            | und => + n (fromString "16")
            | sys => raise Fail "ARB"
            | safe => raise Fail "ARB"
        end

  fun DECODE_ARM ireg =
        let fun b n = word_index ireg n
        in
           case
             (b (fromString "27"),
              (b (fromString "26"),
               (b (fromString "25"),
                (b (fromString "24"),
                 (b (fromString "23"),
                  (b (fromString "22"),
                   (b (fromString "21"),
                    (b (fromString "20"),
                     (b (fromString "7"),
                      (b (fromString "6"),
                       (b (fromString "5"),b (fromString "4"))))))))))))
            of (true,
                (true,
                 (true,
                  (true,
                   (v18,(v22,(v26,(v30,(v34,(v38,(v42,v43))))))))))) =>
                  swi_ex
             | (true,
                (true,
                 (true,
                  (false,
                   (v46,
                    (v50,(v54,(true,(v62,(v66,(v70,true))))))))))) =>
                  mrc
             | (true,
                (true,
                 (true,
                  (false,
                   (v46,
                    (v50,(v54,(true,(v62,(v66,(v70,false))))))))))) =>
                  cdp_und
             | (true,
                (true,
                 (true,
                  (false,
                   (v46,
                    (v50,(v54,(false,(v74,(v78,(v82,true))))))))))) =>
                  mcr
             | (true,
                (true,
                 (true,
                  (false,
                   (v46,
                    (v50,(v54,(false,(v74,(v78,(v82,false))))))))))) =>
                  cdp_und
             | (true,
                (true,
                 (false,
                  (v86,
                   (v90,
                    (v94,(v98,(v102,(v106,(v110,(v114,v115))))))))))) =>
                  ldc_stc
             | (true,
                (false,
                 (true,
                  (v122,
                   (v126,
                    (v130,
                     (v134,(v138,(v142,(v146,(v150,v151))))))))))) =>
                  br
             | (true,
                (false,
                 (false,
                  (v154,
                   (v158,
                    (v162,
                     (v166,(v170,(v174,(v178,(v182,v183))))))))))) =>
                  ldm_stm
             | (false,
                (true,
                 (true,
                  (v194,
                   (v198,
                    (v202,
                     (v206,(v210,(v214,(v218,(v222,true))))))))))) =>
                  cdp_und
             | (false,
                (true,
                 (true,
                  (v194,
                   (v198,
                    (v202,
                     (v206,(v210,(v214,(v218,(v222,false))))))))))) =>
                  ldr_str
             | (false,
                (true,
                 (false,
                  (v226,
                   (v230,
                    (v234,
                     (v238,(v242,(v246,(v250,(v254,v255))))))))))) =>
                  ldr_str
             | (false,
                (false,
                 (true,
                  (true,
                   (true,
                    (v270,
                     (v274,(v278,(v282,(v286,(v290,v291))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (true,
                  (true,
                   (false,
                    (v294,
                     (true,(true,(v306,(v310,(v314,v315))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (true,
                  (true,
                   (false,
                    (v294,
                     (true,(false,(v318,(v322,(v326,v327))))))))))) =>
                  msr
             | (false,
                (false,
                 (true,
                  (true,
                   (false,
                    (v294,
                     (false,(true,(v334,(v338,(v342,v343))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (true,
                  (true,
                   (false,
                    (v294,
                     (false,(false,(v346,(v350,(v354,v355))))))))))) =>
                  cdp_und
             | (false,
                (false,
                 (true,
                  (false,
                   (v358,
                    (v362,
                     (v366,(v370,(v374,(v378,(v382,v383))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (true,
                   (true,
                    (v394,
                     (v398,(true,(true,(true,(v414,true))))))))))) =>
                  ldrh_strh
             | (false,
                (false,
                 (false,
                  (true,
                   (true,
                    (v394,
                     (v398,(true,(true,(true,(v414,false))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (true,
                   (true,
                    (v394,
                     (v398,(true,(true,(false,(true,true))))))))))) =>
                  ldrh_strh
             | (false,
                (false,
                 (false,
                  (true,
                   (true,
                    (v394,
                     (v398,(true,(true,(false,(true,false))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (true,
                   (true,
                    (v394,
                     (v398,(true,(true,(false,(false,true))))))))))) =>
                  cdp_und
             | (false,
                (false,
                 (false,
                  (true,
                   (true,
                    (v394,
                     (v398,(true,(true,(false,(false,false))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (true,
                   (true,
                    (v394,
                     (v398,(true,(false,(v422,(v426,true))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (true,
                   (true,
                    (v394,
                     (v398,(true,(false,(v422,(v426,false))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (true,
                   (true,
                    (v394,
                     (v398,(false,(true,(true,(v438,true))))))))))) =>
                  cdp_und
             | (false,
                (false,
                 (false,
                  (true,
                   (true,
                    (v394,
                     (v398,(false,(true,(true,(v438,false))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (true,
                   (true,
                    (v394,
                     (v398,(false,(true,(false,(true,true))))))))))) =>
                  ldrh_strh
             | (false,
                (false,
                 (false,
                  (true,
                   (true,
                    (v394,
                     (v398,(false,(true,(false,(true,false))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (true,
                   (true,
                    (v394,
                     (v398,(false,(true,(false,(false,true))))))))))) =>
                  cdp_und
             | (false,
                (false,
                 (false,
                  (true,
                   (true,
                    (v394,
                     (v398,
                      (false,(true,(false,(false,false))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (true,
                   (true,
                    (v394,
                     (v398,(false,(false,(v446,(v450,true))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (true,
                   (true,
                    (v394,
                     (v398,(false,(false,(v446,(v450,false))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (true,
                   (false,
                    (v454,
                     (true,(true,(true,(true,(v474,true))))))))))) =>
                  ldrh_strh
             | (false,
                (false,
                 (false,
                  (true,
                   (false,
                    (v454,
                     (true,(true,(true,(true,(v474,false))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (true,
                   (false,
                    (v454,
                     (true,(true,(true,(false,(true,true))))))))))) =>
                  ldrh_strh
             | (false,
                (false,
                 (false,
                  (true,
                   (false,
                    (v454,
                     (true,(true,(true,(false,(true,false))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (true,
                   (false,
                    (v454,
                     (true,(true,(true,(false,(false,true))))))))))) =>
                  cdp_und
             | (false,
                (false,
                 (false,
                  (true,
                   (false,
                    (v454,
                     (true,(true,(true,(false,(false,false))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (true,
                   (false,
                    (v454,
                     (true,(true,(false,(v482,(v486,true))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (true,
                   (false,
                    (v454,
                     (true,(true,(false,(v482,(v486,false))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (true,
                   (false,
                    (v454,
                     (true,(false,(true,(true,(v498,true))))))))))) =>
                  cdp_und
             | (false,
                (false,
                 (false,
                  (true,
                   (false,
                    (v454,
                     (true,(false,(true,(true,(v498,false))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (true,
                   (false,
                    (v454,
                     (true,(false,(true,(false,(true,true))))))))))) =>
                  ldrh_strh
             | (false,
                (false,
                 (false,
                  (true,
                   (false,
                    (v454,
                     (true,(false,(true,(false,(true,false))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (true,
                   (false,
                    (v454,
                     (true,(false,(true,(false,(false,true))))))))))) =>
                  cdp_und
             | (false,
                (false,
                 (false,
                  (true,
                   (false,
                    (v454,
                     (true,
                      (false,(true,(false,(false,false))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (true,
                   (false,
                    (v454,
                     (true,(false,(false,(true,(v510,true))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (true,
                   (false,
                    (v454,
                     (true,(false,(false,(true,(v510,false))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (true,
                   (false,
                    (v454,
                     (true,(false,(false,(false,(true,true))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (true,
                   (false,
                    (v454,
                     (true,
                      (false,(false,(false,(true,false))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (true,
                   (false,
                    (v454,
                     (true,
                      (false,(false,(false,(false,true))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (true,
                   (false,
                    (v454,
                     (true,
                      (false,(false,(false,(false,false))))))))))) =>
                  msr
             | (false,
                (false,
                 (false,
                  (true,
                   (false,
                    (v454,
                     (false,(true,(true,(true,(v530,true))))))))))) =>
                  ldrh_strh
             | (false,
                (false,
                 (false,
                  (true,
                   (false,
                    (v454,
                     (false,(true,(true,(true,(v530,false))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (true,
                   (false,
                    (v454,
                     (false,(true,(true,(false,(true,true))))))))))) =>
                  ldrh_strh
             | (false,
                (false,
                 (false,
                  (true,
                   (false,
                    (v454,
                     (false,(true,(true,(false,(true,false))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (true,
                   (false,
                    (v454,
                     (false,(true,(true,(false,(false,true))))))))))) =>
                  cdp_und
             | (false,
                (false,
                 (false,
                  (true,
                   (false,
                    (v454,
                     (false,
                      (true,(true,(false,(false,false))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (true,
                   (false,
                    (v454,
                     (false,(true,(false,(v538,(v542,true))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (true,
                   (false,
                    (v454,
                     (false,(true,(false,(v538,(v542,false))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (true,
                   (false,
                    (v454,
                     (false,(false,(true,(true,(v554,true))))))))))) =>
                  cdp_und
             | (false,
                (false,
                 (false,
                  (true,
                   (false,
                    (v454,
                     (false,(false,(true,(true,(v554,false))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (true,
                   (false,
                    (v454,
                     (false,(false,(true,(false,(true,true))))))))))) =>
                  ldrh_strh
             | (false,
                (false,
                 (false,
                  (true,
                   (false,
                    (v454,
                     (false,
                      (false,(true,(false,(true,false))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (true,
                   (false,
                    (v454,
                     (false,
                      (false,(true,(false,(false,true))))))))))) =>
                  swp
             | (false,
                (false,
                 (false,
                  (true,
                   (false,
                    (v454,
                     (false,
                      (false,(true,(false,(false,false))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (true,
                   (false,
                    (v454,
                     (false,(false,(false,(true,(v566,true))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (true,
                   (false,
                    (v454,
                     (false,
                      (false,(false,(true,(v566,false))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (true,
                   (false,
                    (v454,
                     (false,
                      (false,(false,(false,(true,true))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (true,
                   (false,
                    (v454,
                     (false,
                      (false,(false,(false,(true,false))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (true,
                   (false,
                    (v454,
                     (false,
                      (false,(false,(false,(false,true))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (true,
                   (false,
                    (v454,
                     (false,
                      (false,(false,(false,(false,false))))))))))) =>
                  mrs
             | (false,
                (false,
                 (false,
                  (false,
                   (true,
                    (v578,
                     (v582,(true,(true,(true,(v598,true))))))))))) =>
                  ldrh_strh
             | (false,
                (false,
                 (false,
                  (false,
                   (true,
                    (v578,
                     (v582,(true,(true,(true,(v598,false))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (false,
                   (true,
                    (v578,
                     (v582,(true,(true,(false,(true,true))))))))))) =>
                  ldrh_strh
             | (false,
                (false,
                 (false,
                  (false,
                   (true,
                    (v578,
                     (v582,(true,(true,(false,(true,false))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (false,
                   (true,
                    (v578,
                     (v582,(true,(true,(false,(false,true))))))))))) =>
                  mla_mul
             | (false,
                (false,
                 (false,
                  (false,
                   (true,
                    (v578,
                     (v582,(true,(true,(false,(false,false))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (false,
                   (true,
                    (v578,
                     (v582,(true,(false,(v606,(v610,true))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (false,
                   (true,
                    (v578,
                     (v582,(true,(false,(v606,(v610,false))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (false,
                   (true,
                    (v578,
                     (v582,(false,(true,(true,(v622,true))))))))))) =>
                  cdp_und
             | (false,
                (false,
                 (false,
                  (false,
                   (true,
                    (v578,
                     (v582,(false,(true,(true,(v622,false))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (false,
                   (true,
                    (v578,
                     (v582,(false,(true,(false,(true,true))))))))))) =>
                  ldrh_strh
             | (false,
                (false,
                 (false,
                  (false,
                   (true,
                    (v578,
                     (v582,(false,(true,(false,(true,false))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (false,
                   (true,
                    (v578,
                     (v582,(false,(true,(false,(false,true))))))))))) =>
                  mla_mul
             | (false,
                (false,
                 (false,
                  (false,
                   (true,
                    (v578,
                     (v582,
                      (false,(true,(false,(false,false))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (false,
                   (true,
                    (v578,
                     (v582,(false,(false,(v630,(v634,true))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (false,
                   (true,
                    (v578,
                     (v582,(false,(false,(v630,(v634,false))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (false,
                   (false,
                    (true,
                     (v642,(true,(true,(true,(v658,true))))))))))) =>
                  ldrh_strh
             | (false,
                (false,
                 (false,
                  (false,
                   (false,
                    (true,
                     (v642,(true,(true,(true,(v658,false))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (false,
                   (false,
                    (true,
                     (v642,(true,(true,(false,(true,true))))))))))) =>
                  ldrh_strh
             | (false,
                (false,
                 (false,
                  (false,
                   (false,
                    (true,
                     (v642,(true,(true,(false,(true,false))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (false,
                   (false,
                    (true,
                     (v642,(true,(true,(false,(false,true))))))))))) =>
                  cdp_und
             | (false,
                (false,
                 (false,
                  (false,
                   (false,
                    (true,
                     (v642,(true,(true,(false,(false,false))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (false,
                   (false,
                    (true,
                     (v642,(true,(false,(v666,(v670,true))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (false,
                   (false,
                    (true,
                     (v642,(true,(false,(v666,(v670,false))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (false,
                   (false,
                    (true,
                     (v642,(false,(true,(true,(v682,true))))))))))) =>
                  cdp_und
             | (false,
                (false,
                 (false,
                  (false,
                   (false,
                    (true,
                     (v642,(false,(true,(true,(v682,false))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (false,
                   (false,
                    (true,
                     (v642,(false,(true,(false,(true,true))))))))))) =>
                  ldrh_strh
             | (false,
                (false,
                 (false,
                  (false,
                   (false,
                    (true,
                     (v642,(false,(true,(false,(true,false))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (false,
                   (false,
                    (true,
                     (v642,(false,(true,(false,(false,true))))))))))) =>
                  cdp_und
             | (false,
                (false,
                 (false,
                  (false,
                   (false,
                    (true,
                     (v642,
                      (false,(true,(false,(false,false))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (false,
                   (false,
                    (true,
                     (v642,(false,(false,(v690,(v694,true))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (false,
                   (false,
                    (true,
                     (v642,(false,(false,(v690,(v694,false))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (false,
                   (false,
                    (false,
                     (v698,(true,(true,(true,(v714,true))))))))))) =>
                  ldrh_strh
             | (false,
                (false,
                 (false,
                  (false,
                   (false,
                    (false,
                     (v698,(true,(true,(true,(v714,false))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (false,
                   (false,
                    (false,
                     (v698,(true,(true,(false,(true,true))))))))))) =>
                  ldrh_strh
             | (false,
                (false,
                 (false,
                  (false,
                   (false,
                    (false,
                     (v698,(true,(true,(false,(true,false))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (false,
                   (false,
                    (false,
                     (v698,(true,(true,(false,(false,true))))))))))) =>
                  mla_mul
             | (false,
                (false,
                 (false,
                  (false,
                   (false,
                    (false,
                     (v698,(true,(true,(false,(false,false))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (false,
                   (false,
                    (false,
                     (v698,(true,(false,(v722,(v726,true))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (false,
                   (false,
                    (false,
                     (v698,(true,(false,(v722,(v726,false))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (false,
                   (false,
                    (false,
                     (v698,(false,(true,(true,(v738,true))))))))))) =>
                  cdp_und
             | (false,
                (false,
                 (false,
                  (false,
                   (false,
                    (false,
                     (v698,(false,(true,(true,(v738,false))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (false,
                   (false,
                    (false,
                     (v698,(false,(true,(false,(true,true))))))))))) =>
                  ldrh_strh
             | (false,
                (false,
                 (false,
                  (false,
                   (false,
                    (false,
                     (v698,(false,(true,(false,(true,false))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (false,
                   (false,
                    (false,
                     (v698,(false,(true,(false,(false,true))))))))))) =>
                  mla_mul
             | (false,
                (false,
                 (false,
                  (false,
                   (false,
                    (false,
                     (v698,
                      (false,(true,(false,(false,false))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (false,
                   (false,
                    (false,
                     (v698,(false,(false,(v746,(v750,true))))))))))) =>
                  data_proc
             | (false,
                (false,
                 (false,
                  (false,
                   (false,
                    (false,
                     (v698,(false,(false,(v746,(v750,false))))))))))) =>
                  data_proc
        end

  fun mode_num mode =
        case mode
         of usr =>
               n2w_itself ((fromString "16"),(ITSELF (fromString "5")))
          | fiq =>
               n2w_itself ((fromString "17"),(ITSELF (fromString "5")))
          | irq =>
               n2w_itself ((fromString "18"),(ITSELF (fromString "5")))
          | svc =>
               n2w_itself ((fromString "19"),(ITSELF (fromString "5")))
          | abt =>
               n2w_itself ((fromString "23"),(ITSELF (fromString "5")))
          | und =>
               n2w_itself ((fromString "27"),(ITSELF (fromString "5")))
          | sys =>
               n2w_itself ((fromString "31"),(ITSELF (fromString "5")))
          | safe => n2w_itself (ZERO,(ITSELF (fromString "5")))

  fun exceptions2num reset = ZERO
    | exceptions2num undefined = ONE
    | exceptions2num software = TWO
    | exceptions2num pabort = (fromString "3")
    | exceptions2num dabort = (fromString "4")
    | exceptions2num address = (fromString "5")
    | exceptions2num interrupt = (fromString "6")
    | exceptions2num fast = (fromString "7")

  fun register2num r0 = ZERO
    | register2num r1 = ONE
    | register2num r2 = TWO
    | register2num r3 = (fromString "3")
    | register2num r4 = (fromString "4")
    | register2num r5 = (fromString "5")
    | register2num r6 = (fromString "6")
    | register2num r7 = (fromString "7")
    | register2num r8 = (fromString "8")
    | register2num r9 = (fromString "9")
    | register2num r10 = (fromString "10")
    | register2num r11 = (fromString "11")
    | register2num r12 = (fromString "12")
    | register2num r13 = (fromString "13")
    | register2num r14 = (fromString "14")
    | register2num r15 = (fromString "15")
    | register2num r8_fiq = (fromString "16")
    | register2num r9_fiq = (fromString "17")
    | register2num r10_fiq = (fromString "18")
    | register2num r11_fiq = (fromString "19")
    | register2num r12_fiq = (fromString "20")
    | register2num r13_fiq = (fromString "21")
    | register2num r14_fiq = (fromString "22")
    | register2num r13_irq = (fromString "23")
    | register2num r14_irq = (fromString "24")
    | register2num r13_svc = (fromString "25")
    | register2num r14_svc = (fromString "26")
    | register2num r13_abt = (fromString "27")
    | register2num r14_abt = (fromString "28")
    | register2num r13_und = (fromString "29")
    | register2num r14_und = (fromString "30")

  fun num2register n =
        if n = ZERO then r0
        else
          if n = ONE then
          r1
        else
          if n = TWO then
          r2
        else
          if n = (fromString "3") then
          r3
        else
          if n = (fromString "4") then
          r4
        else
          if n = (fromString "5") then
          r5
        else
          if n = (fromString "6") then
          r6
        else
          if n = (fromString "7") then
          r7
        else
          if n = (fromString "8") then
          r8
        else
          if n = (fromString "9") then
          r9
        else
          if n = (fromString "10") then
          r10
        else
          if n = (fromString "11") then
          r11
        else
          if n = (fromString "12") then
          r12
        else
          if n = (fromString "13") then
          r13
        else
          if n = (fromString "14") then
          r14
        else
          if n = (fromString "15") then
          r15
        else
          if n = (fromString "16") then
          r8_fiq
        else
          if n = (fromString "17") then
          r9_fiq
        else
          if n = (fromString "18") then
          r10_fiq
        else
          if n = (fromString "19") then
          r11_fiq
        else
          if n = (fromString "20") then
          r12_fiq
        else
          if n = (fromString "21") then
          r13_fiq
        else
          if n = (fromString "22") then
          r14_fiq
        else
          if n = (fromString "23") then
          r13_irq
        else
          if n = (fromString "24") then
          r14_irq
        else
          if n = (fromString "25") then
          r13_svc
        else
          if n = (fromString "26") then
          r14_svc
        else
          if n = (fromString "27") then
          r13_abt
        else
          if n = (fromString "28") then
          r14_abt
        else
          if n = (fromString "29") then
          r13_und
        else
          if n = (fromString "30") then
          r14_und
        else raise (Fail "num2register: 30 < n")

  fun num2condition n =
        if n = ZERO then EQ
        else
          if n = ONE then
          CS
        else
          if n = TWO then
          MI
        else
          if n = (fromString "3") then
          VS
        else
          if n = (fromString "4") then
          HI
        else
          if n = (fromString "5") then
          GE
        else
          if n = (fromString "6") then
          GT
        else
          if n = (fromString "7") then
          AL
        else
          if n = (fromString "8") then
          NE
        else
          if n = (fromString "9") then
          CC
        else
          if n = (fromString "10") then
          PL
        else
          if n = (fromString "11") then
          VC
        else
          if n = (fromString "12") then
          LS
        else
          if n = (fromString "13") then
          LT
        else
          if n = (fromString "14") then
          LE
        else
          if n = (fromString "15") then
          NV
        else raise (Fail "num2condition: 15 < n")

  fun SET_IFMODE irq' fiq' mode w =
        word_modify (fn i => fn b =>
          (< (fromString "7") i orelse (i = (fromString "5"))) andalso b
          orelse
          ((i = (fromString "7")) andalso irq' orelse
           ((i = (fromString "6")) andalso fiq' orelse
            < i (fromString "5") andalso word_index (mode_num mode) i)))
          w

  fun REG_READ reg m n =
        if
          word_eq n
            (n2w_itself ((fromString "15"),(ITSELF (fromString "4"))))
        then
          word_add (reg r15)
            (n2w_itself ((fromString "8"),(ITSELF (fromString "32"))))
        else reg (num2register (mode_reg2num m n))

  fun REG_WRITE reg m n d =
        combinML.UPDATE (num2register (mode_reg2num m n)) d reg

  fun INC_PC reg =
        combinML.UPDATE r15
          (word_add (reg r15)
             (n2w_itself ((fromString "4"),(ITSELF (fromString "32")))))
          reg

  fun FETCH_PC reg = reg r15

  fun SET_NZCV (N,(Z,(C,V))) w =
        word_modify (fn i => fn b =>
          (i = (fromString "31")) andalso N orelse
          ((i = (fromString "30")) andalso Z orelse
           ((i = (fromString "29")) andalso C orelse
            ((i = (fromString "28")) andalso V orelse
             < i (fromString "28") andalso b)))) w

  fun SET_NZC (N,(Z,C)) w =
        SET_NZCV (N,(Z,(C,word_index w (fromString "28")))) w

  fun SET_NZ (N,Z) w = SET_NZC (N,(Z,word_index w (fromString "29"))) w

  fun DECODE_MODE m =
        case
          word_eq m
            (n2w_itself ((fromString "16"),(ITSELF (fromString "5"))))
         of true => usr
          | false =>
               (case
                  word_eq m
                    (n2w_itself
                       ((fromString "17"),(ITSELF (fromString "5"))))
                of true => fiq
                 | false =>
                      (case
                         word_eq m
                           (n2w_itself
                              ((fromString "18"),
                               (ITSELF (fromString "5"))))
                       of true => irq
                        | false =>
                             (case
                                word_eq m
                                  (n2w_itself
                                     ((fromString "19"),
                                      (ITSELF (fromString "5"))))
                              of true => svc
                               | false =>
                                    (case
                                       word_eq m
                                         (n2w_itself
                                            ((fromString "23"),
                                             (ITSELF (fromString "5"))))
                                     of true => abt
                                      | false =>
                                           (case
                                              word_eq m
                                                (n2w_itself
                                                   ((fromString "27"),
                                                    (ITSELF
                                                      (fromString 
                                                      "5"))))
                                            of true => und
                                             | false =>
                                                  (case
                                                     word_eq m
                                                       (n2w_itself
                                                          ((fromString 
                                                           "31"),
                                                           (ITSELF
                                                             (fromString 
                                                             "5"))))
                                                   of true => sys
                                                    | false =>
                                                         safe))))))

  fun NZCV w =
        (word_index w (fromString "31"),
         (word_index w (fromString "30"),
          (word_index w (fromString "29"),
           word_index w (fromString "28"))))

  fun CARRY (n,(z,(c,v))) = c

  fun mode2psr mode =
        case mode
         of usr => CPSR
          | fiq => SPSR_fiq
          | irq => SPSR_irq
          | svc => SPSR_svc
          | abt => SPSR_abt
          | und => SPSR_und
          | sys => CPSR
          | safe => CPSR

  fun SPSR_READ psr mode = psr (mode2psr mode)

  fun CPSR_READ psr = psr CPSR

  fun CPSR_WRITE psr cpsr = combinML.UPDATE CPSR cpsr psr

  fun SPSR_WRITE psr mode spsr =
        if USER mode then psr
        else combinML.UPDATE (mode2psr mode) spsr psr

  fun exception2mode e =
        case e
         of reset => svc
          | undefined => und
          | software => svc
          | pabort => abt
          | dabort => abt
          | address => svc
          | interrupt => irq
          | fast => fiq

  fun EXCEPTION r e =
        let val cpsr = CPSR_READ (regs_psr r)
            val fiq' =
                ((e = reset) orelse (e = fast)) orelse
                word_index cpsr (fromString "6")
            val mode' = exception2mode e
            val pc =
                n2w_itself
                  ( *  (fromString "4") (exceptions2num e),
                   (ITSELF (fromString "32")))
            val reg' =
                REG_WRITE (regs_reg r) mode'
                  (n2w_itself
                     ((fromString "14"),(ITSELF (fromString "4"))))
                  (word_add (FETCH_PC (regs_reg r))
                     (n2w_itself
                        ((fromString "4"),(ITSELF (fromString "32")))))
        in
           regs(REG_WRITE reg' usr
                  (n2w_itself
                     ((fromString "15"),(ITSELF (fromString "4")))) pc,
                CPSR_WRITE (SPSR_WRITE (regs_psr r) mode' cpsr)
                  (SET_IFMODE true fiq' mode' cpsr))
        end

  fun BRANCH r mode ireg =
        let val (L,offset) = DECODE_BRANCH ireg
            val pc =
                REG_READ (regs_reg r) usr
                  (n2w_itself
                     ((fromString "15"),(ITSELF (fromString "4"))))
            val br_addr =
                word_add pc
                  (word_lsl
                     (sw2sw_itself (ITSELF (fromString "32")) offset)
                     TWO)
            val pc_reg =
                REG_WRITE (regs_reg r) usr
                  (n2w_itself
                     ((fromString "15"),(ITSELF (fromString "4"))))
                  br_addr
        in
           regs(if L then
                  REG_WRITE pc_reg mode
                    (n2w_itself
                       ((fromString "14"),(ITSELF (fromString "4"))))
                    (word_add (FETCH_PC (regs_reg r))
                       (n2w_itself
                          ((fromString "4"),
                           (ITSELF (fromString "32"))))) else pc_reg,
                regs_psr r)
        end

  fun LSL m n c =
        if word_eq n (n2w_itself (ZERO,(ITSELF (fromString "8")))) then
          (c,m)
        else
          (word_ls n
             (n2w_itself ((fromString "32"),(ITSELF (fromString "8"))))
           andalso word_index m (- (fromString "32") (w2n n)),
           word_lsl m (w2n n))

  fun LSR m n c =
        if word_eq n (n2w_itself (ZERO,(ITSELF (fromString "8")))) then
          LSL m (n2w_itself (ZERO,(ITSELF (fromString "8")))) c
        else
          (word_ls n
             (n2w_itself ((fromString "32"),(ITSELF (fromString "8"))))
           andalso word_index m (- (w2n n) ONE),word_lsr m (w2n n))

  fun ASR m n c =
        if word_eq n (n2w_itself (ZERO,(ITSELF (fromString "8")))) then
          LSL m (n2w_itself (ZERO,(ITSELF (fromString "8")))) c
        else
          (word_index m (MIN (fromString "31") (- (w2n n) ONE)),
           word_asr m (w2n n))

  fun ROR m n c =
        if word_eq n (n2w_itself (ZERO,(ITSELF (fromString "8")))) then
          LSL m (n2w_itself (ZERO,(ITSELF (fromString "8")))) c
        else
          (word_index m
             (- (w2n (w2w_itself (ITSELF (fromString "5")) n)) ONE),
           word_ror m (w2n n))

  fun IMMEDIATE C opnd2 =
        let val rot =
                word_extract_itself (ITSELF (fromString "8"))
                  (fromString "11") (fromString "8") opnd2
            val imm =
                word_extract_itself (ITSELF (fromString "32"))
                  (fromString "7") ZERO opnd2
        in
           ROR imm
             (word_mul (n2w_itself (TWO,(ITSELF (fromString "8")))) rot)
             C
        end

  fun SHIFT_IMMEDIATE2 shift sh rm c =
        case word_eq sh (n2w_itself (ZERO,(ITSELF TWO)))
         of true => LSL rm shift c
          | false =>
               (case word_eq sh (n2w_itself (ONE,(ITSELF TWO)))
                of true =>
                      LSR rm
                        (if
                           word_eq shift
                             (n2w_itself
                                (ZERO,(ITSELF (fromString "8"))))
                         then
                           n2w_itself
                             ((fromString "32"),
                              (ITSELF (fromString "8")))
                         else shift) c
                 | false =>
                      (case word_eq sh (n2w_itself (TWO,(ITSELF TWO)))
                       of true =>
                             ASR rm
                               (if
                                  word_eq shift
                                    (n2w_itself
                                       (ZERO,(ITSELF (fromString "8"))))
                                then
                                  n2w_itself
                                    ((fromString "32"),
                                     (ITSELF (fromString "8")))
                                else shift) c
                        | false =>
                             if
                               word_eq shift
                                 (n2w_itself
                                    (ZERO,(ITSELF (fromString "8"))))
                             then
                               word_rrx (c,rm)
                             else ROR rm shift c))

  fun SHIFT_REGISTER2 shift sh rm c =
        case word_eq sh (n2w_itself (ZERO,(ITSELF TWO)))
         of true => LSL rm shift c
          | false =>
               (case word_eq sh (n2w_itself (ONE,(ITSELF TWO)))
                of true => LSR rm shift c
                 | false =>
                      (case word_eq sh (n2w_itself (TWO,(ITSELF TWO)))
                       of true => ASR rm shift c
                        | false => ROR rm shift c))

  fun SHIFT_IMMEDIATE reg mode C w =
        let val (q0,Rm) = DIVMOD_2EXP (fromString "4") (w2n w)
            val (q1,Sh) = DIVMOD_2EXP TWO (DIV2 q0)
            val shift = MOD_2EXP (fromString "5") q1
            val rm =
                REG_READ reg mode
                  (n2w_itself (Rm,(ITSELF (fromString "4"))))
        in
           SHIFT_IMMEDIATE2
             (n2w_itself (shift,(ITSELF (fromString "8"))))
             (n2w_itself (Sh,(ITSELF TWO))) rm C
        end

  fun SHIFT_REGISTER reg mode C w =
        let val (q0,Rm) = DIVMOD_2EXP (fromString "4") (w2n w)
            val (q1,Sh) = DIVMOD_2EXP TWO (DIV2 q0)
            val Rs = MOD_2EXP (fromString "4") (DIV2 q1)
            val shift =
                MOD_2EXP (fromString "8")
                  (w2n
                     (REG_READ reg mode
                        (n2w_itself (Rs,(ITSELF (fromString "4"))))))
            val rm =
                REG_READ (INC_PC reg) mode
                  (n2w_itself (Rm,(ITSELF (fromString "4"))))
        in
           SHIFT_REGISTER2
             (n2w_itself (shift,(ITSELF (fromString "8"))))
             (n2w_itself (Sh,(ITSELF TWO))) rm C
        end

  fun ADDR_MODE1 reg mode C Im opnd2 =
        if Im then IMMEDIATE C opnd2
        else
          if word_index opnd2 (fromString "4") then
          SHIFT_REGISTER reg mode C opnd2
        else SHIFT_IMMEDIATE reg mode C opnd2

  fun ALU_arith f rn op2 =
        let val sign = word_msb rn
            val (q,r) =
                DIVMOD_2EXP (fromString "32") (f (w2n rn) (w2n op2))
            val res = n2w_itself (r,(ITSELF (fromString "32")))
        in
           ((word_msb res,
             (r = ZERO,
              (ODD q,
               (word_msb op2 = sign) andalso
               not (word_msb res = sign)))),res)
        end

  fun ALU_logic res =
        ((word_msb res,
          (word_eq res (n2w_itself (ZERO,(ITSELF (fromString "32")))),
           (false,false))),res)

  fun ADD a b c =
        ALU_arith (fn x => fn y => + (+ x y) (if c then ONE else ZERO))
          a b

  fun SUB a b c = ADD a (word_1comp b) c

  fun AND a b = ALU_logic (word_and a b)

  fun EOR a b = ALU_logic (word_xor a b)

  fun ORR a b = ALU_logic (word_or a b)

  fun ALU opc rn op2 c =
        case word_eq opc (n2w_itself (ZERO,(ITSELF (fromString "4"))))
         of true => AND rn op2
          | false =>
               (case
                  word_eq opc
                    (n2w_itself (ONE,(ITSELF (fromString "4"))))
                of true => EOR rn op2
                 | false =>
                      (case
                         word_eq opc
                           (n2w_itself (TWO,(ITSELF (fromString "4"))))
                       of true => SUB rn op2 true
                        | false =>
                             (case
                                word_eq opc
                                  (n2w_itself
                                     ((fromString "4"),
                                      (ITSELF (fromString "4"))))
                              of true => ADD rn op2 false
                               | false =>
                                    (case
                                       word_eq opc
                                         (n2w_itself
                                            ((fromString "3"),
                                             (ITSELF (fromString "4"))))
                                     of true => SUB op2 rn true
                                      | false =>
                                           (case
                                              word_eq opc
                                                (n2w_itself
                                                   ((fromString "5"),
                                                    (ITSELF
                                                      (fromString 
                                                      "4"))))
                                            of true => ADD rn op2 c
                                             | false =>
                                                  (case
                                                     word_eq opc
                                                       (n2w_itself
                                                          ((fromString 
                                                           "6"),
                                                           (ITSELF
                                                             (fromString 
                                                             "4"))))
                                                   of true =>
                                                         SUB rn op2 c
                                                    | false =>
                                                         (case
                                                            word_eq opc
                                                              (n2w_itself
                                                                 ((fromString 
                                                                  "7"),
                                                                  (ITSELF
                                                                    (fromString 
                                                                    "4"))))
                                                          of true =>
                                                                SUB op2
                                                                  rn c
                                                           | false =>
                                                                (case
                                                                   word_eq
                                                                     opc
                                                                     (n2w_itself
                                                                        ((fromString 
                                                                         "8"),
                                                                         (ITSELF
                                                                           (fromString 
                                                                           "4"))))
                                                                 of true =>
                                                                       AND
                                                                         rn
                                                                         op2
                                                                  | false =>
                                                                       (case
                                                                          word_eq
                                                                            opc
                                                                            (n2w_itself
                                                                               ((fromString 
                                                                                "9"),
                                                                                (ITSELF
                                                                                  (fromString 
                                                                                  "4"))))
                                                                        of true =>
                                                                              EOR
                                                                                rn
                                                                                op2
                                                                         | false =>
                                                                              (case
                                                                                 word_eq
                                                                                   opc
                                                                                   (n2w_itself
                                                                                      ((fromString 
                                                                                       "10"),
                                                                                       (ITSELF
                                                                                         (fromString 
                                                                                         "4"))))
                                                                               of true =>
                                                                                     SUB
                                                                                       rn
                                                                                       op2
                                                                                       true
                                                                                | false =>
                                                                                     (case
                                                                                        word_eq
                                                                                          opc
                                                                                          (n2w_itself
                                                                                             ((fromString 
                                                                                              "11"),
                                                                                              (ITSELF
                                                                                                (fromString 
                                                                                                "4"))))
                                                                                      of true =>
                                                                                            ADD
                                                                                              rn
                                                                                              op2
                                                                                              false
                                                                                       | false =>
                                                                                            (case
                                                                                               word_eq
                                                                                                 opc
                                                                                                 (n2w_itself
                                                                                                    ((fromString 
                                                                                                     "12"),
                                                                                                     (ITSELF
                                                                                                       (fromString 
                                                                                                       "4"))))
                                                                                             of true =>
                                                                                                   ORR
                                                                                                     rn
                                                                                                     op2
                                                                                              | false =>
                                                                                                   (case
                                                                                                      word_eq
                                                                                                        opc
                                                                                                        (n2w_itself
                                                                                                           ((fromString 
                                                                                                            "13"),
                                                                                                            (ITSELF
                                                                                                              (fromString 
                                                                                                              "4"))))
                                                                                                    of true =>
                                                                                                          ALU_logic
                                                                                                            op2
                                                                                                     | false =>
                                                                                                          (case
                                                                                                             word_eq
                                                                                                               opc
                                                                                                               (n2w_itself
                                                                                                                  ((fromString 
                                                                                                                   "14"),
                                                                                                                   (ITSELF
                                                                                                                     (fromString 
                                                                                                                     "4"))))
                                                                                                           of true =>
                                                                                                                 AND
                                                                                                                   rn
                                                                                                                   (word_1comp
                                                                                                                      op2)
                                                                                                            | false =>
                                                                                                                 ALU_logic
                                                                                                                   (word_1comp
                                                                                                                      op2)))))))))))))))

  fun ARITHMETIC opcode =
        (word_index opcode TWO orelse word_index opcode ONE) andalso
        (not (word_index opcode (fromString "3")) orelse
         not (word_index opcode TWO))

  fun TEST_OR_COMP opcode =
        word_eq (word_bits (fromString "3") TWO opcode)
          (n2w_itself (TWO,(ITSELF (fromString "4"))))

  fun DATA_PROCESSING r C mode ireg =
        let val (I,(opcode,(S,(Rn,(Rd,opnd2))))) = DECODE_DATAP ireg
            val (C_s,op2) = ADDR_MODE1 (regs_reg r) mode C I opnd2
            val pc_reg = INC_PC (regs_reg r)
            val rn =
                REG_READ
                  (if
                     not I andalso word_index opnd2 (fromString "4")
                   then
                     pc_reg
                   else regs_reg r) mode Rn
            val ((N,(Z,(C_alu,V))),res) = ALU opcode rn op2 C
            val tc = TEST_OR_COMP opcode
        in
           regs(if tc then pc_reg else REG_WRITE pc_reg mode Rd res,
                if S then
                  CPSR_WRITE (regs_psr r)
                    (if
                       word_eq Rd
                         (n2w_itself
                            ((fromString "15"),
                             (ITSELF (fromString "4")))) andalso not tc
                     then
                       SPSR_READ (regs_psr r) mode
                     else
                       (if ARITHMETIC opcode then
                          SET_NZCV (N,(Z,(C_alu,V)))
                        else SET_NZC (N,(Z,C_s)))
                     (CPSR_READ (regs_psr r))) else regs_psr r)
        end

  fun MRS r mode ireg =
        let val (R,Rd) = DECODE_MRS ireg
            val word =
                if R then
                  SPSR_READ (regs_psr r) mode
                else CPSR_READ (regs_psr r)
        in
           regs(REG_WRITE (INC_PC (regs_reg r)) mode Rd word,regs_psr r)
        end

  fun MSR r mode ireg =
        let val (I,(R,(bit19,(bit16,(Rm,opnd))))) = DECODE_MSR ireg
        in
           if
             USER mode andalso (R orelse not bit19 andalso bit16) orelse
             not bit19 andalso not bit16
           then
          regs(INC_PC (regs_reg r),regs_psr r)
        else
          let val psrd =
                  if R then
                    SPSR_READ (regs_psr r) mode
                  else CPSR_READ (regs_psr r)
              val src =
                  if I then
                    pairML.SND (IMMEDIATE false opnd)
                  else REG_READ (regs_reg r) mode Rm
              val psrd' =
                  word_modify (fn i => fn b =>
                    <= (fromString "28") i andalso
                    (if bit19 then word_index src i else b) orelse
                    (<= (fromString "8") i andalso
                     (<= i (fromString "27") andalso b) orelse
                     <= i (fromString "7") andalso
                     (if bit16 andalso not (USER mode) then
                        word_index src i
                      else b))) psrd
          in
             regs(INC_PC (regs_reg r),if R then
                    SPSR_WRITE (regs_psr r) mode psrd'
                  else CPSR_WRITE (regs_psr r) psrd')
          end
        end

  fun ALU_multiply L Sgn A rd rn rs rm =
        let val res =
                word_add
                  (if A then
                     (if L then
                        word_concat_itself (ITSELF (fromString "64")) rd
                          rn
                      else w2w_itself (ITSELF (fromString "64")) rn)
                   else n2w_itself (ZERO,(ITSELF (fromString "64"))))
                  (if L andalso Sgn then
                     word_mul
                       (sw2sw_itself (ITSELF (fromString "64")) rm)
                       (sw2sw_itself (ITSELF (fromString "64")) rs)
                   else
                     word_mul (w2w_itself (ITSELF (fromString "64")) rm)
                       (w2w_itself (ITSELF (fromString "64")) rs))
            val resHi =
                word_extract_itself (ITSELF (fromString "32"))
                  (fromString "63") (fromString "32") res
            val resLo =
                word_extract_itself (ITSELF (fromString "32"))
                  (fromString "31") ZERO res
        in
           if L then
          (word_msb res,
           (word_eq res (n2w_itself (ZERO,(ITSELF (fromString "64")))),
            (resHi,resLo)))
        else
          (word_msb resLo,
           (word_eq resLo
              (n2w_itself (ZERO,(ITSELF (fromString "32")))),
            (rd,resLo)))
        end

  fun MLA_MUL r mode ireg =
        let val (L,(Sgn,(A,(S,(Rd,(Rn,(Rs,Rm))))))) =
                DECODE_MLA_MUL ireg
            val pc_reg = INC_PC (regs_reg r)
            val rd = REG_READ (regs_reg r) mode Rd
            val rn = REG_READ (regs_reg r) mode Rn
            val rs = REG_READ (regs_reg r) mode Rs
            val rm = REG_READ (regs_reg r) mode Rm
            val (N,(Z,(resHi,resLo))) = ALU_multiply L Sgn A rd rn rs rm
        in
           if
             word_eq Rd
               (n2w_itself
                  ((fromString "15"),(ITSELF (fromString "4")))) orelse
             (word_eq Rd Rm orelse
              L andalso
              (word_eq Rn
                 (n2w_itself
                    ((fromString "15"),(ITSELF (fromString "4"))))
               orelse (word_eq Rn Rm orelse word_eq Rd Rn)))
           then
          regs(pc_reg,regs_psr r)
        else
          regs(if L then
                 REG_WRITE (REG_WRITE pc_reg mode Rn resLo) mode Rd
                   resHi else REG_WRITE pc_reg mode Rd resLo,if S then
                 CPSR_WRITE (regs_psr r)
                   (SET_NZ (N,Z) (CPSR_READ (regs_psr r)))
               else regs_psr r)
        end

  fun UP_DOWN u = if u then word_add else word_sub

  fun ADDR_MODE2 reg mode C Im P U Rn offset =
        let val addr = REG_READ reg mode Rn
            val wb_addr =
                UP_DOWN U addr
                  (if Im then
                     pairML.SND (SHIFT_IMMEDIATE reg mode C offset)
                   else w2w_itself (ITSELF (fromString "32")) offset)
        in
           (if P then wb_addr else addr,wb_addr)
        end

  fun ==> A B = not A orelse B

  fun LDR_STR r C mode ireg input =
        let val (I,(P,(U,(B,(W,(L,(Rn,(Rd,offset)))))))) =
                DECODE_LDR_STR ireg
            val (addr,wb_addr) =
                ADDR_MODE2 (regs_reg r) mode C I P U Rn offset
            val pc_reg = INC_PC (regs_reg r)
        in
           case input
            of NONE =>
                  INL([if L then MemRead(addr)
                       else
                         let val w = REG_READ pc_reg mode Rd
                         in
                            MemWrite(addr,if B then
                                       Byte(word_extract_itself
                                              (ITSELF (fromString "8"))
                                              (fromString "7") ZERO w)
                                     else Word(w))
                         end])
             | SOME((isdabort,data)) =>
                  let val wb_reg =
                          if ==> P W then
                            REG_WRITE pc_reg mode Rn wb_addr
                          else pc_reg
                  in
                     INR(regs(if ==> L isdabort then wb_reg
                              else
                                let val fmt =
                                        if B then
                                          UnsignedByte
                                        else UnsignedWord
                                in
                                   REG_WRITE wb_reg mode Rd
                                     (FORMAT fmt
                                        (word_extract_itself
                                           (ITSELF TWO) ONE ZERO addr)
                                        (HD data))
                                end,regs_psr r))
                  end
        end

  fun ADDR_MODE3 reg mode Im P U Rn offsetH offsetL =
        let val addr = REG_READ reg mode Rn
            val wb_addr =
                UP_DOWN U addr
                  (if Im then
                     word_concat_itself (ITSELF (fromString "32"))
                       offsetH offsetL
                   else REG_READ reg mode offsetL)
        in
           (if P then wb_addr else addr,wb_addr)
        end

  fun LDRH_STRH r mode ireg input =
        let val (P,(U,(I,(W,(L,(Rn,(Rd,(offsetH,(S,(H,offsetL))))))))))
                = DECODE_LDRH_STRH ireg
            val (addr,wb_addr) =
                ADDR_MODE3 (regs_reg r) mode I P U Rn offsetH offsetL
            val pc_reg = INC_PC (regs_reg r)
        in
           case input
            of NONE =>
                  INL([if L then MemRead(addr)
                       else
                         MemWrite(addr,
                                  Half(word_extract_itself
                                         (ITSELF (fromString "16"))
                                         (fromString "15") ZERO
                                         (REG_READ pc_reg mode Rd)))])
             | SOME((isdabort,data)) =>
                  let val wb_reg =
                          if ==> P W then
                            REG_WRITE pc_reg mode Rn wb_addr
                          else pc_reg
                  in
                     INR(regs(if ==> L isdabort then wb_reg
                              else
                                let val fmt =
                                        case (S,H)
                                         of (true,true) =>
                                               SignedHalfWord
                                          | (true,false) => SignedByte
                                          | (false,true) =>
                                               UnsignedHalfWord
                                          | (false,false) =>
                                               raise Fail "ARB"
                                in
                                   REG_WRITE wb_reg mode Rd
                                     (FORMAT fmt
                                        (word_extract_itself
                                           (ITSELF TWO) ONE ZERO addr)
                                        (HD data))
                                end,regs_psr r))
                  end
        end

  fun REGISTER_LIST w =
        let val (q0,b0) = DIVMOD_2EXP ONE (w2n w)
            val (q1,b1) = DIVMOD_2EXP ONE q0
            val (q2,b2) = DIVMOD_2EXP ONE q1
            val (q3,b3) = DIVMOD_2EXP ONE q2
            val (q4,b4) = DIVMOD_2EXP ONE q3
            val (q5,b5) = DIVMOD_2EXP ONE q4
            val (q6,b6) = DIVMOD_2EXP ONE q5
            val (q7,b7) = DIVMOD_2EXP ONE q6
            val (q8,b8) = DIVMOD_2EXP ONE q7
            val (q9,b9) = DIVMOD_2EXP ONE q8
            val (q10,b10) = DIVMOD_2EXP ONE q9
            val (q11,b11) = DIVMOD_2EXP ONE q10
            val (q12,b12) = DIVMOD_2EXP ONE q11
            val (q13,b13) = DIVMOD_2EXP ONE q12
            val (q14,b14) = DIVMOD_2EXP ONE q13
        in
           MAP pairML.SND
             (FILTER pairML.FST
                [(b0 = ONE,n2w_itself (ZERO,(ITSELF (fromString "4")))),
                 (b1 = ONE,n2w_itself (ONE,(ITSELF (fromString "4")))),
                 (b2 = ONE,n2w_itself (TWO,(ITSELF (fromString "4")))),
                 (b3 = ONE,
                  n2w_itself
                    ((fromString "3"),(ITSELF (fromString "4")))),
                 (b4 = ONE,
                  n2w_itself
                    ((fromString "4"),(ITSELF (fromString "4")))),
                 (b5 = ONE,
                  n2w_itself
                    ((fromString "5"),(ITSELF (fromString "4")))),
                 (b6 = ONE,
                  n2w_itself
                    ((fromString "6"),(ITSELF (fromString "4")))),
                 (b7 = ONE,
                  n2w_itself
                    ((fromString "7"),(ITSELF (fromString "4")))),
                 (b8 = ONE,
                  n2w_itself
                    ((fromString "8"),(ITSELF (fromString "4")))),
                 (b9 = ONE,
                  n2w_itself
                    ((fromString "9"),(ITSELF (fromString "4")))),
                 (b10 = ONE,
                  n2w_itself
                    ((fromString "10"),(ITSELF (fromString "4")))),
                 (b11 = ONE,
                  n2w_itself
                    ((fromString "11"),(ITSELF (fromString "4")))),
                 (b12 = ONE,
                  n2w_itself
                    ((fromString "12"),(ITSELF (fromString "4")))),
                 (b13 = ONE,
                  n2w_itself
                    ((fromString "13"),(ITSELF (fromString "4")))),
                 (b14 = ONE,
                  n2w_itself
                    ((fromString "14"),(ITSELF (fromString "4")))),
                 (ODD q14,
                  n2w_itself
                    ((fromString "15"),(ITSELF (fromString "4"))))])
        end

  fun ADDRESS_LIST start n =
        GENLIST (fn i =>
          word_add start
            (word_mul
               (n2w_itself
                  ((fromString "4"),(ITSELF (fromString "32"))))
               (n2w_itself (i,(ITSELF (fromString "32")))))) n

  fun WB_ADDRESS U base len =
        UP_DOWN U base
          (n2w_itself
             ( *  (fromString "4") len,(ITSELF (fromString "32"))))

  fun FIRST_ADDRESS P U base wb =
        if U then
          (if P then
             word_add base
               (n2w_itself
                  ((fromString "4"),(ITSELF (fromString "32"))))
           else base)
        else
          if P then
          wb
        else
          word_add wb
            (n2w_itself ((fromString "4"),(ITSELF (fromString "32"))))

  fun ADDR_MODE4 P U base list =
        let val rp_list = REGISTER_LIST list
            val len = LENGTH rp_list
            val wb = WB_ADDRESS U base len
            val addr_list = ADDRESS_LIST (FIRST_ADDRESS P U base wb) len
        in
           (rp_list,(addr_list,wb))
        end

  fun LDM_LIST reg mode rp_list data =
        FOLDL (fn reg' => fn (rp,rd) => REG_WRITE reg' mode rp rd) reg
          (ZIP (rp_list,data))

  fun STM_LIST reg mode bl_list =
        MAP (fn (rp,addr) => MemWrite(addr,Word(REG_READ reg mode rp)))
          bl_list

  fun LDM_STM r mode ireg input =
        let val (P,(U,(S,(W,(L,(Rn,list)))))) = DECODE_LDM_STM ireg
            val pc_in_list = word_index list (fromString "15")
            val rn = REG_READ (regs_reg r) mode Rn
            val (rp_list,(addr_list,rn')) = ADDR_MODE4 P U rn list
            val mode' =
                if S andalso ==> L (not pc_in_list) then usr else mode
            val pc_reg = INC_PC (regs_reg r)
            val wb_reg =
                if
                  W andalso
                  not
                    (word_eq Rn
                       (n2w_itself
                          ((fromString "15"),
                           (ITSELF (fromString "4")))))
                then
                  REG_WRITE pc_reg (if L then mode else mode') Rn rn'
                else pc_reg
        in
           case input
            of NONE =>
                  INL(if L then MAP MemRead addr_list
                      else
                        STM_LIST
                          (if word_eq (HD rp_list) Rn then
                             pc_reg
                           else wb_reg) mode' (ZIP (rp_list,addr_list)))
             | SOME((dabort_t,data)) =>
                  INR(if L then
                        regs(let val t =
                                     if IS_SOME dabort_t then
                                       THE dabort_t
                                     else LENGTH rp_list
                                 val ldm_reg =
                                     LDM_LIST wb_reg mode'
                                       (TAKE t rp_list) (TAKE t data)
                             in
                                if
                                  IS_SOME dabort_t andalso
                                  not
                                    (word_eq Rn
                                       (n2w_itself
                                          ((fromString "15"),
                                           (ITSELF (fromString "4")))))
                                then
                               REG_WRITE ldm_reg mode' Rn
                                 (REG_READ wb_reg mode' Rn)
                             else ldm_reg
                             end,
                             if
                               S andalso
                               (pc_in_list andalso IS_NONE dabort_t)
                             then
                               CPSR_WRITE (regs_psr r)
                                 (SPSR_READ (regs_psr r) mode)
                             else regs_psr r)
                      else regs(wb_reg,regs_psr r))
        end

  fun SWP r mode ireg input =
        let val (B,(Rn,(Rd,Rm))) = DECODE_SWP ireg
            val rn = REG_READ (regs_reg r) mode Rn
            val pc_reg = INC_PC (regs_reg r)
            val rm = REG_READ pc_reg mode Rm
        in
           case input
            of NONE =>
                  INL([MemRead(rn),
                       MemWrite(rn,if B then
                                  Byte(word_extract_itself
                                         (ITSELF (fromString "8"))
                                         (fromString "7") ZERO rm)
                                else Word(rm))])
             | SOME((isdabort,data)) =>
                  INR(regs(if isdabort then pc_reg
                           else
                             let val fmt =
                                     if B then
                                       UnsignedByte
                                     else UnsignedWord
                             in
                                REG_WRITE pc_reg mode Rd
                                  (FORMAT fmt
                                     (word_extract_itself (ITSELF TWO)
                                        ONE ZERO rn) (HD data))
                             end,regs_psr r))
        end

  fun MRC r mode data ireg =
        let val Rd =
                word_extract_itself (ITSELF (fromString "4"))
                  (fromString "15") (fromString "12") ireg
            val pc_reg = INC_PC (regs_reg r)
        in
           if
             word_eq Rd
               (n2w_itself
                  ((fromString "15"),(ITSELF (fromString "4"))))
           then
          regs(pc_reg,
               CPSR_WRITE (regs_psr r)
                 (SET_NZCV (NZCV data) (CPSR_READ (regs_psr r))))
        else regs(REG_WRITE pc_reg mode Rd data,regs_psr r)
        end

  fun MCR_OUT reg mode ireg =
        let val Rd =
                word_extract_itself (ITSELF (fromString "4"))
                  (fromString "15") (fromString "12") ireg
        in
           [CPWrite(REG_READ (INC_PC reg) mode Rd)]
        end

  fun ADDR_MODE5 reg mode P U Rn offset =
        let val addr = REG_READ reg mode Rn
            val wb_addr =
                UP_DOWN U addr
                  (word_lsl
                     (w2w_itself (ITSELF (fromString "32")) offset) TWO)
        in
           (if P then wb_addr else addr,wb_addr)
        end

  fun LDC_STC r mode ireg input =
        let val (P,(U,(N,(W,(L,(Rn,(CRd,(CPN,offset)))))))) =
                DECODE_LDC_STC ireg
            val (addr,wb_addr) =
                ADDR_MODE5 (regs_reg r) mode P U Rn offset
        in
           if input then
          let val pc_reg = INC_PC (regs_reg r)
              val wb_reg =
                  if
                    W andalso
                    not
                      (word_eq Rn
                         (n2w_itself
                            ((fromString "15"),
                             (ITSELF (fromString "4")))))
                  then
                    REG_WRITE pc_reg mode Rn wb_addr
                  else pc_reg
          in
             INR(regs(wb_reg,regs_psr r))
          end
        else
          INL([if L then MemRead(addr)
               else MemWrite(addr,raise Fail "ARB")])
        end

  fun CONDITION_PASSED2 (N,(Z,(C,V))) cond =
        case cond
         of EQ => Z
          | CS => C
          | MI => N
          | VS => V
          | HI => C andalso not Z
          | GE => N = V
          | GT => not Z andalso (N = V)
          | AL => true
          | NE => not Z
          | CC => not C
          | PL => not N
          | VC => not V
          | LS => not C orelse Z
          | LT => not (N = V)
          | LE => Z orelse not (N = V)
          | NV => false

  fun CONDITION_PASSED flags ireg =
        let val pass =
                CONDITION_PASSED2 flags
                  (num2condition
                     (w2n
                        (word_bits (fromString "31") (fromString "29")
                           ireg)))
        in
           if word_index ireg (fromString "28") then
          not pass
        else pass
        end

  fun RUN_ARM state dabt data no_cp =
        let val ireg = arm_state_ireg state
            val r = arm_state_regs state
            fun inc_pc x = regs(INC_PC (regs_reg x),regs_psr x)
        in
           if not (arm_state_exception state = software) then
          EXCEPTION r (arm_state_exception state)
        else
          let val (nzcv,(i,(f,m))) = DECODE_PSR (CPSR_READ (regs_psr r))
          in
             if not (CONDITION_PASSED nzcv ireg) then
            inc_pc r
          else
            let val mode = DECODE_MODE m
                fun coproc f = if no_cp then r else f r
            in
               case DECODE_ARM ireg
                of swp =>
                      OUTR (SWP r mode ireg (SOME((IS_SOME dabt,data))))
                 | mrs => MRS r mode ireg
                 | msr => MSR r mode ireg
                 | data_proc => DATA_PROCESSING r (CARRY nzcv) mode ireg
                 | mla_mul => MLA_MUL r mode ireg
                 | ldr_str =>
                      OUTR
                        (LDR_STR r (CARRY nzcv) mode ireg
                           (SOME((IS_SOME dabt,data))))
                 | ldrh_strh =>
                      OUTR
                        (LDRH_STRH r mode ireg
                           (SOME((IS_SOME dabt,data))))
                 | ldm_stm =>
                      OUTR (LDM_STM r mode ireg (SOME((dabt,data))))
                 | br => BRANCH r mode ireg
                 | swi_ex => EXCEPTION r software
                 | cdp_und => coproc inc_pc
                 | mcr => coproc inc_pc
                 | mrc =>
                      coproc (fn x => MRC x mode (ELL ONE data) ireg)
                 | ldc_stc =>
                      coproc (fn x => OUTR (LDC_STC x mode ireg true))
                 | unexec => r
            end
          end
        end

  fun IS_Reset (SOME(Reset(x))) = true
    | IS_Reset NONE = false
    | IS_Reset (SOME(Undef)) = false
    | IS_Reset (SOME(Prefetch)) = false
    | IS_Reset (SOME(Dabort(v3))) = false
    | IS_Reset (SOME(Fiq)) = false
    | IS_Reset (SOME(Irq)) = false

  fun PROJ_Dabort (SOME(Dabort(x))) = SOME(x)
    | PROJ_Dabort NONE = NONE
    | PROJ_Dabort (SOME(Reset(v2))) = NONE
    | PROJ_Dabort (SOME(Undef)) = NONE
    | PROJ_Dabort (SOME(Prefetch)) = NONE
    | PROJ_Dabort (SOME(Fiq)) = NONE
    | PROJ_Dabort (SOME(Irq)) = NONE

  fun PROJ_Reset (SOME(Reset(x))) = x

  fun interrupt2exception state (i',f') irpt =
        let val ireg = arm_state_ireg state
            val (flags,(i,(f,m))) =
                DECODE_PSR (CPSR_READ (regs_psr (arm_state_regs state)))
            val pass =
                (arm_state_exception state = software) andalso
                CONDITION_PASSED flags ireg
            val ic = DECODE_ARM ireg
            val old_flags = pass andalso ((ic = mrs) orelse (ic = msr))
        in
           case irpt
            of NONE => software
             | SOME(Reset(x)) => reset
             | SOME(Undef) =>
                  if
                    pass andalso
                    IN ic
                      (INSERT
                         (cdp_und,
                          INSERT
                            (mrc,INSERT (mcr,INSERT (ldc_stc,EMPTY)))))
                  then
                    undefined
                  else software
             | SOME(Prefetch) => pabort
             | SOME(Dabort(t)) => dabort
             | SOME(Fiq) =>
                  if (if old_flags then f else f') then
                    software
                  else fast
             | SOME(Irq) =>
                  if (if old_flags then i else i') then
                    software
                  else interrupt
        end

  fun PROJ_IF_FLAGS psr =
        let val (flags,(i,(f,m))) = DECODE_PSR (CPSR_READ psr)
        in
           (i,f)
        end

  fun NEXT_ARM state inp =
        let val r =
                if IS_Reset (arm_input_interrupt inp) then
                  PROJ_Reset (arm_input_interrupt inp)
                else
                  RUN_ARM state (PROJ_Dabort (arm_input_interrupt inp))
                    (arm_input_data inp) (arm_input_no_cp inp)
        in
           arm_state(r,arm_input_ireg inp,
                     interrupt2exception state
                       (PROJ_IF_FLAGS (regs_psr r))
                       (arm_input_interrupt inp))
        end

  fun OUT_ARM state =
        let val ireg = arm_state_ireg state
            val r = arm_state_regs state
            val (nzcv,(i,(f,m))) = DECODE_PSR (CPSR_READ (regs_psr r))
            val mode = DECODE_MODE m
        in
           if
             (arm_state_exception state = software) andalso
             CONDITION_PASSED nzcv ireg
           then
          let val ic = DECODE_ARM ireg
          in
             arm_output(case ic
                         of swp => OUTL (SWP r mode ireg NONE)
                          | mrs => []
                          | msr => []
                          | data_proc => []
                          | mla_mul => []
                          | ldr_str =>
                               OUTL
                                 (LDR_STR r (CARRY nzcv) mode ireg NONE)
                          | ldrh_strh =>
                               OUTL (LDRH_STRH r mode ireg NONE)
                          | ldm_stm => OUTL (LDM_STM r mode ireg NONE)
                          | br => []
                          | swi_ex => []
                          | cdp_und => []
                          | mcr => MCR_OUT (regs_reg r) mode ireg
                          | mrc => []
                          | ldc_stc => OUTL (LDC_STC r mode ireg false)
                          | unexec => [],
                        IN ic
                          (INSERT
                             (cdp_und,
                              INSERT
                                (mcr,
                                 INSERT (mrc,INSERT (ldc_stc,EMPTY))))),
                        USER mode)
          end
        else arm_output([],false,USER mode)
        end

  fun TRANSFER cpi (cp_data,(data,mem)) t =
        case t
         of MemRead(a) =>
               if cpi then
                 let val (f,b) = SPLITP IS_SOME cp_data
                 in
                    (b,
                     (APPEND data
                        (MAP (fn addr => mem_read (mem,addr30 addr))
                           (ADDRESS_LIST a (LENGTH f))),mem))
                 end
               else
                 (cp_data,(APPEND data [mem_read (mem,addr30 a)],mem))
          | MemWrite(a',d) =>
               if cpi then
                 let val (f,b) = SPLITP IS_NONE cp_data
                 in
                    (b,
                     (data,
                      FOLDL (fn m => fn (addr,cpd) =>
                        MEM_WRITE mem addr (Word(THE cpd))) mem
                        (ZIP (ADDRESS_LIST a' (LENGTH f),f))))
                 end
               else (cp_data,(data,MEM_WRITE mem a' d))
          | CPWrite(w) =>
               (cp_data,(if cpi then APPEND data [w] else data,mem))

  fun TRANSFERS arm_out cp_state cp_data mem =
        let val (data,mem) =
                if
                  arm_output_cpi arm_out andalso
                  NULL (arm_output_transfers arm_out)
                then
                  (MAP THE cp_data,mem)
                else
                  pairML.SND
                    (FOLDL (TRANSFER (arm_output_cpi arm_out))
                       (cp_data,([],mem))
                       (arm_output_transfers arm_out))
        in
           bus(data,mem,NONE,cp_state)
        end

  fun OUT_CP cp state ireg arm_out =
        let val is_usr = arm_output_user arm_out
        in
           if
             arm_output_cpi arm_out andalso
             (word_index ireg (fromString "27") andalso
              not (coproc_absent cp is_usr ireg))
           then
          cp_output(let val ic = DECODE_CP ireg
                    in
                       if ic = mrc then
                      [SOME(coproc_f_mrc cp state is_usr ireg),NONE]
                    else
                      if
                        (ic = ldc_stc) andalso
                        not (word_index ireg (fromString "20"))
                      then
                      coproc_f_stc cp state is_usr ireg
                    else
                      GENLIST (combinML.K NONE)
                        (coproc_n_ldc cp state is_usr ireg)
                    end,false)
        else cp_output([],true)
        end

  fun RUN_CP cp state absent is_usr ireg data =
        if not absent then
          let val ic = DECODE_CP ireg
          in
             if ic = mcr then
            coproc_f_mcr cp state is_usr ireg (HD data)
          else
            if
              (ic = ldc_stc) andalso word_index ireg (fromString "20")
            then
            coproc_f_ldc cp state is_usr ireg data
          else
            if ic = cdp_und then
            coproc_f_cdp cp state is_usr ireg
          else state
          end else state

  fun NEXT_ARM_MMU cp state =
        let val ireg =
                mem_read
                  (arm_sys_state_memory state,
                   addr30 (FETCH_PC (arm_sys_state_registers state)))
            val s =
                arm_state(regs(arm_sys_state_registers state,
                               arm_sys_state_psrs state),ireg,
                          if arm_sys_state_undefined state then
                            undefined else software)
            val arm_out = OUT_ARM s
            val cp_out =
                OUT_CP cp (arm_sys_state_cp_state state) ireg arm_out
            val b =
                TRANSFERS arm_out (arm_sys_state_cp_state state)
                  (cp_output_data cp_out) (arm_sys_state_memory state)
            val r =
                RUN_ARM s NONE (bus_data b) (cp_output_absent cp_out)
            val p =
                RUN_CP cp (arm_sys_state_cp_state state)
                  (cp_output_absent cp_out) (arm_output_user arm_out)
                  ireg (bus_data b)
        in
           arm_sys_state(regs_reg r,regs_psr r,bus_memory b,
                         not (arm_sys_state_undefined state) andalso
                         (arm_output_cpi arm_out andalso
                          cp_output_absent cp_out),p)
        end

  fun NEXT_ARM_MEM state =
        let val ireg =
                mem_read
                  (arm_sys_state_memory state,
                   addr30 (FETCH_PC (arm_sys_state_registers state)))
            val s =
                arm_state(regs(arm_sys_state_registers state,
                               arm_sys_state_psrs state),ireg,
                          if arm_sys_state_undefined state then
                            undefined else software)
            val arm_out = OUT_ARM s
            val mmu_out =
                TRANSFERS arm_out (arm_sys_state_cp_state state) []
                  (arm_sys_state_memory state)
            val r = RUN_ARM s NONE (bus_data mmu_out) true
        in
           arm_sys_state(regs_reg r,regs_psr r,bus_memory mmu_out,
                         not (arm_sys_state_undefined state) andalso
                         arm_output_cpi arm_out,
                         arm_sys_state_cp_state state)
        end

  val empty_registers =
        fn n => n2w_itself (ZERO,(ITSELF (fromString "32")))

end
