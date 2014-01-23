LIB "primdec.lib";

ring R = 0,(x(0..2)),dp;
ideal I = x(0)^2 + x(1)^2 + x(2)^2 - 1, x(1)^2 + x(0) - x(2), 2*x(2) - 1;
print(radical(std(I)));
exit;
