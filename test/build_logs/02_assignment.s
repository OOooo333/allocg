

.text
 .global main
main:
	addi sp, sp, -1600
	sw ra, 4(sp)
	li t0, 1
	sw t0, 8(sp)
	li t0, 3
	sw t0, 12(sp)
	li t0, 3
	sw t0, 8(sp)
	li a0, 3
	lw ra, 4(sp)
	addi sp, sp, 800
	addi sp,sp,800
	ret

