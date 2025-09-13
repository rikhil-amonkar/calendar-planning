# Z3 array for allowed transitions
allowed_z3 = z3.Array('allowed', z3.IntSort(), z3.ArraySort(z3.IntSort(), z3.BoolSort()))
for i in range(7):
    for j in range(7):
        s.add(allowed_z3[i][j] == allowed[i][j])

# Ensure direct flight between consecutive cities
for i in range(6):
    curr = order[i]
    next_c = order[i + 1]
    s.add(allowed_z3[curr][next_c])