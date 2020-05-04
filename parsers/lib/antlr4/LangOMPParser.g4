// Based on the OpenMP API Specification 5.0, November 2018.
parser grammar LangOMPParser;

ompBlockPragma
    : OMP_PARALLEL ompOption*
    | OMP_SECTION
    | OMP_SECTIONS
    ;

ompLoopPragma
    : OMP_FOR ompOption*
    | OMP_PARALLEL OMP_FOR ompOption*
    | OMP_FOR OMP_SIMD ompOption*
    ;

ompOption
    : OMP_NOWAIT
    | OMP_PRIVATE OMP_PAREN_OPEN ompIdList OMP_PAREN_CLOSE
    | OMP_SHARED OMP_PAREN_OPEN ompIdList OMP_PAREN_CLOSE
    | OMP_SCHEDULE OMP_PAREN_OPEN OMP_STATIC OMP_PAREN_CLOSE
    | OMP_SIMDLEN OMP_PAREN_OPEN POSITIVE_INTEGER OMP_PAREN_CLOSE
    | OMP_NUM_THREADS OMP_PAREN_OPEN POSITIVE_INTEGER OMP_PAREN_CLOSE
    | OMP_REDUCTION OMP_PAREN_OPEN ompReductionIdentifier OMP_COLON ompIdList OMP_PAREN_CLOSE
    ;

ompReductionIdentifier: OMP_IDENTIFIER | OMP_REDUCTION_OP;

ompIdList
    : OMP_IDENTIFIER
    | OMP_IDENTIFIER OMP_COMMA ompIdList;