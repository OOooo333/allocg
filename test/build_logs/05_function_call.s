

.text
 .global main
add:
	addi sp, sp, -1600
	sw a0, 4(sp)
	sw a1, 8(sp)
	sw ra, 12(sp)
	lw t1, 4(sp)
	lw t2, 8(sp)
	add t0, t1, t2
	sw t0, 16(sp)
	lw a0, 16(sp)
	lw ra, 12(sp)
	addi sp, sp, 800
	addi sp,sp,800
	ret

main:
	addi sp, sp, -1600
	sw ra, 4(sp)
	li a0, 3
	li a1, 4
	call add
	sw a0, 8(sp)
	lw t0, 8(sp)
	sw t0, 12(sp)
	lw a0, 12(sp)
	lw ra, 4(sp)
	addi sp, sp, 800
	addi sp,sp,800
	ret

