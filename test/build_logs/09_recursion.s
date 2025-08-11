

.text
 .global main
fact:
	addi sp, sp, -1600
	sw a0, 4(sp)
	sw ra, 8(sp)
	lw t1, 4(sp)
	li t2, 1
	sgt t0, t1, t2
	xori t0, t0, 1
	sw t0, 12(sp)
	lw t0, 12(sp)
	bne t0, x0, L0
	j L1
L0:
	li a0, 1
	lw ra, 8(sp)
	addi sp, sp, 800
	addi sp,sp,800
	ret
L1:
	lw t1, 4(sp)
	li t2, 1
	sub t0, t1, t2
	sw t0, 16(sp)
	lw a0, 16(sp)
	call fact
	sw a0, 20(sp)
	lw t1, 4(sp)
	lw t2, 20(sp)
	mul t0, t1, t2
	sw t0, 24(sp)
	lw a0, 24(sp)
	lw ra, 8(sp)
	addi sp, sp, 800
	addi sp,sp,800
	ret

main:
	addi sp, sp, -1600
	sw ra, 4(sp)
	li a0, 5
	call fact
	sw a0, 8(sp)
	lw a0, 8(sp)
	lw ra, 4(sp)
	addi sp, sp, 800
	addi sp,sp,800
	ret

