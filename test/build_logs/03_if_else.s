

.text
 .global main
main:
	addi sp, sp, -1600
	sw ra, 4(sp)
	li t0, 3
	sw t0, 8(sp)
	li t0, 1
	sw t0, 12(sp)
	li t0, 1
	bne t0, x0, L0
	j L1
L0:
	li t0, 4
	sw t0, 16(sp)
	li t0, 4
	sw t0, 8(sp)
	j L2
L1:
	li t0, 2
	sw t0, 20(sp)
	li t0, 2
	sw t0, 8(sp)
	j L2
L2:
	lw a0, 8(sp)
	lw ra, 4(sp)
	addi sp, sp, 800
	addi sp,sp,800
	ret

