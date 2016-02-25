    .globl add_1
add_1:
    pushq   %rbp
    movq    %rsp, %rbp
    pushq   %r15
    pushq   %r14
    pushq   %r13
    pushq   %r12
    pushq   %rbx
    subq    $16, %rsp
    movq    %rdi, %rbx
    movq    %rsi, %rcx
    addq    %rcx, %rbx
    movq    %rbx, %rax
    addq    $16, %rsp
    popq    %rbx
    popq    %r12
    popq    %r13
    popq    %r14
    popq    %r15
    popq    %rbp
    retq
    .globl main
main:
    pushq   %rbp
    movq    %rsp, %rbp
    subq    $16, %rsp
    leaq    add_1(%rip), %rbx
    movq    $40, %rdi
    movq    $2, %rsi
    callq   *%rbx
    movq    %rax, %rbx
    movq    %rbx, %rax
    addq    $16, %rsp
    popq    %rbp
    retq
