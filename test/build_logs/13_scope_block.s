

.text
 .global main
main:
	addi sp, sp, -1600
	sw ra, 4(sp)
	li t0, 5
	sw t0, 8(sp)
	li t0, 3
	sw t0, 12(sp)
	li t0, 8
	sw t0, 16(sp)
	li t0, 8
	sw t0, 8(sp)
	li a0, 8
	lw ra, 4(sp)
	addi sp, sp, 800
	addi sp,sp,800
	ret

