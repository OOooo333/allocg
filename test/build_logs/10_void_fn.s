

.text
 .global main
print:
	addi sp, sp, -1600
	sw ra, 4(sp)
	lw ra, 4(sp)
	addi sp, sp, 800
	addi sp,sp,800
	ret

main:
	addi sp, sp, -1600
	sw ra, 4(sp)
	call print
	sw a0, 8(sp)
	li a0, 0
	lw ra, 4(sp)
	addi sp, sp, 800
	addi sp,sp,800
	ret

