from z3 import *

# Create variables
houses = [1, 2, 3]
names = ['Arnold', 'Peter', 'Eric']
heights = ['short', 'average', 'very short']

# Declare variables for the solver
name_vars = {house: Int(f'name_{house}') for house in houses}
height_vars = {house: Int(f'height_{house}') for house in houses}

# Create a solver instance
solver = Solver()

# Add constraints for names
for house in houses:
    solver.add(name_vars[house] >= 0)
    solver.add(name_vars[house] < len(names))

# Add constraints for heights
for house in houses:
    solver.add(height_vars[house] >= 0)
    solver.add(height_vars[house] < len(heights))

# All names must be unique
solver.add(Distinct([name_vars[house] for house in houses]))

# All heights must be unique
solver.add(Distinct([height_vars[house] for house in houses]))

# Clue 1: Peter is somewhere to the right of Eric.
solver.add(Or(name_vars[2] == names.index('Peter') & name_vars[1] == names.index('Eric'),
              name_vars[3] == names.index('Peter') & name_vars[1] == names.index('Eric'),
              name_vars[3] == names.index('Peter') & name_vars[2] == names.index('Eric')))

# Clue 2: The person who is short is in the first house.
solver.add(height_vars[1] == heights.index('short'))

# Clue 3: There is one house between the person who is short and the person who is very short.
solver.add(Or(height_vars[3] == heights.index('very short'),
              height_vars[2] == heights.index('very short')))

# Clue 4: Arnold and the person who is very short are next to each other.
solver.add(Or((name_vars[1] == names.index('Arnold') & height_vars[2] == heights.index('very short')),
              (name_vars[2] == names.index('Arnold') & height_vars[1] == heights.index('very short')),
              (name_vars[2] == names.index('Arnold') & height_vars[3] == heights.index('very short')),
              (name_vars[3] == names.index('Arnold') & height_vars[2] == heights.index('very short'))))

# Check if the solution exists
if solver.check() == sat:
    model = solver.model()
    solution = []
    for house in houses:
        name_index = model[name_vars[house]].as_long()
        height_index = model[height_vars[house]].as_long()
        solution.append([str(house), names[name_index], heights[height_index]])
    
    print({
        "solution": {
            "header": ["House", "Name", "Height"],
            "rows": solution
        }
    })
else:
    print("No solution found")