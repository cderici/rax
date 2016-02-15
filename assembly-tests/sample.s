    .globl main
main:
    pushq   %rbp
    movq    %rsp, %rbp
    pushq   %r15
    pushq   %r14
    pushq   %r13
    pushq   %r12
    pushq   %rbx
    subq    $8, %rsp

    movq    $8192, %rdi
    movq    $65536, %rsi
    callq   initialize
    movq    rootstack_begin(%rip), %rbx
    movq    free_ptr(%rip), %rcx
    addq    $16, %rcx
    cmpq    %rcx, fromspace_end(%rip)
    setl    %al
    movzbq  %al, %rcx
    cmpq    $0, %rcx
    je then1504
    movq    %rbx, %rdi
    movq    $16, %rsi
    callq   collect
    jmp if_end1505
then1504:
if_end1505:
    movq    free_ptr(%rip), %rcx
    addq    $16, free_ptr(%rip)
    movq    $3, 0(%rcx)
    movq    $42, 8(%rcx)
    movq    free_ptr(%rip), %rdx
    addq    $16, %rdx
    cmpq    %rdx, fromspace_end(%rip)
    setl    %al
    movzbq  %al, %rdx
    cmpq    $0, %rdx
    je then1506
    movq    %rcx, 0(%rbx)
    movq    %rbx, %rcx
    addq    $8, %rcx
    movq    %rcx, %rdi
    movq    $16, %rsi
    callq   collect
    movq    0(%rbx), %rcx
    jmp if_end1507
then1506:
if_end1507:
    movq    free_ptr(%rip), %rbx
    addq    $16, free_ptr(%rip)
    movq    $131, 0(%rbx)
    movq    %rcx, 8(%rbx)
    movq    8(%rbx), %rbx
    movq    8(%rbx), %rbx
    movq    %rbx, %rax

    movq    %rax, %rdi
    callq   print_int
    movq    $0, %rax
    addq    $8, %rsp
    popq    %rbx
    popq    %r12
    popq    %r13
    popq    %r14
    popq    %r15
    popq    %rbp
    retq
