

.text
 .global main
main:
	addi sp, sp, -1600
	sw ra, 4(sp)
	li t0, 14
	sw t0, 8(sp)
	li a0, 14
	lw ra, 4(sp)
	addi sp, sp, 800
	addi sp,sp,800
	ret

