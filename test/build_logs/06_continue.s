

.text
 .global main
main:
	addi sp, sp, -1600
	sw ra, 4(sp)
	li t0, 0
	sw t0, 8(sp)
	li t0, 0
	sw t0, 12(sp)
	j L0
L0:
	lw t1, 8(sp)
	li t2, 5
	slt t0, t1, t2
	sw t0, 16(sp)
	lw t0, 16(sp)
	bne t0, x0, L1
	j L2
L1:
	lw t1, 8(sp)
	li t2, 1
	add t0, t1, t2
	sw t0, 20(sp)
	lw t0, 20(sp)
	sw t0, 8(sp)
	lw t1, 8(sp)
	li t2, 3
	sub t0, t1, t2
	seqz t0, t0
	sw t0, 24(sp)
	lw t0, 24(sp)
	bne t0, x0, L3
	j L4
L3:
	j L0
L4:
	lw t1, 12(sp)
	li t2, 1
	add t0, t1, t2
	sw t0, 28(sp)
	lw t0, 28(sp)
	sw t0, 12(sp)
	j L0
L2:
	lw a0, 12(sp)
	lw ra, 4(sp)
	addi sp, sp, 800
	addi sp,sp,800
	ret

