structure updateML :> updateML =
struct
  nonfix MEM_WRITE MEM_WRITE_WORD MEM_WRITE_HALF MEM_WRITE_BYTE SET_HALF
         SET_BYTE FORMAT GET_BYTE GET_HALF addr30 mem_items empty_memory
         mem_write_block mem_write mem_read |: Word Half Byte
         UnsignedWord UnsignedHalfWord SignedHalfWord UnsignedByte
         SignedByte * / div mod + - ^ @ <> > < >= <= := o before;
  
  open numML
  open sumML
  open fcpML
  open wordsML
  
  type mem = word30->word32
  val mem_updates = ref ([]: word30 list)
  datatype formats
       = SignedByte
       | UnsignedByte
       | SignedHalfWord
       | UnsignedHalfWord
       | UnsignedWord
  datatype data = Byte of word8 | Half of word16 | Word of word32
  fun |: a l =
        fn m => fn b =>
        if
          word_ls a b andalso < (- (w2n b) (w2n a)) (listML.LENGTH l)
        then listML.EL (- (w2n b) (w2n a)) l else m b
    
  fun mem_read (m,a) = m a
    
  fun mem_write m a d = combinML.UPDATE a d m
    
  fun mem_write_block m a cr = |: a cr m
    
  val empty_memory =
        fn a =>
        n2w_itself
          ((fromString "3858759696"),(ITSELF (fromString "32")))
    
  fun mem_items m = []
    
  fun addr30 x =
        word_extract_itself (ITSELF (fromString "30")) (fromString "31")
          TWO x
    
  fun GET_HALF oareg data =
        if word_index oareg ONE then
          word_extract_itself (ITSELF (fromString "16"))
            (fromString "31") (fromString "16") data
        else
          word_extract_itself (ITSELF (fromString "16"))
            (fromString "15") ZERO data
    
  fun GET_BYTE oareg data =
        case word_eq oareg (n2w_itself (ZERO,(ITSELF TWO)))
         of true =>
               word_extract_itself (ITSELF (fromString "8"))
                 (fromString "7") ZERO data
          | false =>
               (case word_eq oareg (n2w_itself (ONE,(ITSELF TWO)))
                of true =>
                      word_extract_itself (ITSELF (fromString "8"))
                        (fromString "15") (fromString "8") data
                 | false =>
                      (case
                         word_eq oareg (n2w_itself (TWO,(ITSELF TWO)))
                       of true =>
                             word_extract_itself
                               (ITSELF (fromString "8"))
                               (fromString "23") (fromString "16") data
                        | false =>
                             word_extract_itself
                               (ITSELF (fromString "8"))
                               (fromString "31") (fromString "24")
                               data))
    
  fun FORMAT fmt oareg data =
        case fmt
         of SignedByte =>
               sw2sw_itself (ITSELF (fromString "32"))
                 (GET_BYTE oareg data)
          | UnsignedByte =>
               w2w_itself (ITSELF (fromString "32"))
                 (GET_BYTE oareg data)
          | SignedHalfWord =>
               sw2sw_itself (ITSELF (fromString "32"))
                 (GET_HALF oareg data)
          | UnsignedHalfWord =>
               w2w_itself (ITSELF (fromString "32"))
                 (GET_HALF oareg data)
          | UnsignedWord =>
               word_ror data ( *  (fromString "8") (w2n oareg))
    
  fun SET_BYTE oareg b w =
        word_modify (fn i => fn x =>
          < i (fromString "8") andalso
          (if word_eq oareg (n2w_itself (ZERO,(ITSELF TWO))) then
             word_index b i
           else x) orelse
          ((<= (fromString "8") i andalso < i (fromString "16")) andalso
           (if word_eq oareg (n2w_itself (ONE,(ITSELF TWO))) then
              word_index b (- i (fromString "8"))
            else x) orelse
           ((<= (fromString "16") i andalso < i (fromString "24"))
            andalso
            (if word_eq oareg (n2w_itself (TWO,(ITSELF TWO))) then
               word_index b (- i (fromString "16"))
             else x) orelse
            (<= (fromString "24") i andalso < i (fromString "32"))
            andalso
            (if
               word_eq oareg
                 (n2w_itself ((fromString "3"),(ITSELF TWO)))
             then
               word_index b (- i (fromString "24"))
             else x)))) w
    
  fun SET_HALF oareg hw w =
        word_modify (fn i => fn x =>
          < i (fromString "16") andalso
          (if not oareg then word_index hw i else x) orelse
          (<= (fromString "16") i andalso < i (fromString "32")) andalso
          (if oareg then word_index hw (- i (fromString "16")) else x))
          w
    
  fun MEM_WRITE_BYTE mem addr word =
        let val a30 = addr30 addr
        in
           mem_write mem a30
             (SET_BYTE (word_extract_itself (ITSELF TWO) ONE ZERO addr)
                word (mem_read (mem,a30)))
        end
    
  fun MEM_WRITE_HALF mem addr word =
        let val a30 = addr30 addr
        in
           mem_write mem a30
             (SET_HALF (word_index addr ONE) word (mem_read (mem,a30)))
        end
    
  fun MEM_WRITE_WORD mem addr word = mem_write mem (addr30 addr) word
    
  fun MEM_WRITE mem addr d =
        case d
         of Byte(b) => MEM_WRITE_BYTE mem addr b
          | Half(hw) => MEM_WRITE_HALF mem addr hw
          | Word(w) => MEM_WRITE_WORD mem addr w
    
end
