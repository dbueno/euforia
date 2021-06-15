find_program(LLVM_EXTERNAL_LIT lit)

add_lit_testsuite(check "Run all the tests"
    -v
    ${CMAKE_CURRENT_SOURCE_DIR}
    ARGS
    --path=${CMAKE_BINARY_DIR}/bin
    DEPENDS euforia
    )
