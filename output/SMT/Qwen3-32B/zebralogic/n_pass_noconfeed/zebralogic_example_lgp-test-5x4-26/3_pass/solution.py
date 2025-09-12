from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define variables
# Assuming 5 people (indices 0 to 4) and hair colors 0 to 4
hair_color = Ints('hair_color_0 hair_color_1 hair_color_2 hair_color_3 hair_color_4')
mother = Ints('mother_0 mother_1 mother_2 mother_3 mother_4')

# Add constraints that each hair_color and mother is unique and in range [0, 4]
for var in hair_color + mother:
    solver.add(And(0 <= var, var <= 4))

# Add clue constraint
# Clue 12: brown hair (4) is left of mother Janelle (0)
# That is, if hair_color[i] == 4, then mother[j] == 0 for some j > i
solver.add(Or(
    And(hair_color[0] == 4, mother[1] == 0),
    And(hair_color[0] == 4, mother[2] == 0),
    And(hair_color[0] == 4, mother[3] == 0),
    And(hair_color[0] == 4, mother[4] == 0),
    And(hair_color[1] == 4, mother[2] == 0),
    And(hair_color[1] == 4, mother[3] == 0),
    And(hair_color[1] == 4, mother[4] == 0),
    And(hair_color[2] == 4, mother[3] == 0),
    And(hair_color[2] == 4, mother[4] == 0),
    And(hair_color[3] == 4, mother[4] == 0)
))

# Solve and print results
if solver.check() == sat:
    model = solver.model()
    print("Solution found:")
    for i in range(5):
        print(f"Person {i}: Hair Color = {model[hair_color[i]]}, Mother = {model[mother[i]]}")
else:
    print("No solution found.")