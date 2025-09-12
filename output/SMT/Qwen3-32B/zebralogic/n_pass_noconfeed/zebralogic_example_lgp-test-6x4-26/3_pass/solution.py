import z3

# Initialize solver
s = z3.Solver()

# Create 6 integer variables for pets and styles
pets = [z3.Int(f'pet_{i}') for i in range(6)]
styles = [z3.Int(f'style_{i}') for i in range(6)]

# Clue 16: Bird and Modern are two apart
clue16 = z3.Or()
for i in range(6):
    for j in range(6):
        if abs(i - j) == 2:
            clue16 = z3.Or(clue16, z3.And(pets[i] == 0, styles[j] == 2))

s.add(clue16)

# Check satisfiability
print(s.check())