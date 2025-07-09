// examples/input.c
int val_one = 1;
int val_five = 5;
int sum_ab = val_one + val_five;
int val_ten = 10;
int product = sum_ab * val_ten; 
int final_result = product - val_five;
int unused_var = 7;
// This line will be skipped by transpiler and a warning printed:
// complex_expr = (val_one + val_five) * val_ten; 