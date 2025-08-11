

.text
 .global main
main:
	addi sp, sp, -1600
	sw ra, 4(sp)
	li t0, 5
	sw t0, 8(sp)
	li t0, 1
	sw t0, 12(sp)
	li t0, 1
	bne t0, x0, L0
	j L1
L0:
	li a0, 1
	lw ra, 4(sp)
	addi sp, sp, 800
	addi sp,sp,800
	ret
L1:
	li a0, 0
	lw ra, 4(sp)
	addi sp, sp, 800
	addi sp,sp,800
	ret

