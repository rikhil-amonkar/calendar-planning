from z3 import IntVector, Solver, And, Distinct

# Define the number of houses
houses = 5

# Create variables for each attribute (nationality, drink, color, pet, etc.)
n = IntVector('n', houses)  # Nationalities
s = IntVector('s', houses)  # Drinks
c = IntVector('c', houses)  # Colors
h = IntVector('h', houses)  # Hobbies or pets
p = IntVector('p', houses)  # Pets or other attributes

# Initialize the solver
solver = Solver()

# Add bounds and distinct constraints for each attribute
for var in [n, s, c, h, p]:
    for i in range(houses):
        solver.add(And(var[i] >= 0, var[i] <= 4))  # Ensure values are in range
    solver.add(Distinct(*[var[i] for i in range(houses)]))  # Unpack the list