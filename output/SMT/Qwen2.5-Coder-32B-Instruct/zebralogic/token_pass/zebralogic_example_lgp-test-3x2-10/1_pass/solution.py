from z3 import *

# Define the variables
house = [Int(f'house_{i}') for i in range(1, 4)]
name = [Int(f'name_{i}') for i in range(1, 4)]
height = [Int(f'height_{i}') for i in range(1, 4)]

# Define the domains
names = {'Eric': 0, 'Arnold': 1, 'Peter': 2}
heights = {'short': 0, 'very short': 1, 'average': 2}

# Create the solver
solver = Solver()

# Add constraints for unique names and heights
solver.add(Distinct(name))
solver.add(Distinct(height))

# Add the clues as constraints
# Clue 1: Eric is not in the first house.
solver.add(name[0] != names['Eric'])

# Clue 2: The person who is very short is somewhere to the left of the person who is short.
solver.add(Or(And(height[0] == heights['very short'], height[1] == heights['short']),
              And(height[0] == heights['very short'], height[2] == heights['short']),
              And(height[1] == heights['very short'], height[2] == heights['short'])))

# Clue 3: The person who is very short is Eric.
solver.add(name[i] == names['Eric'] for i in range(3) if height[i] == heights['very short'])

# Clue 4: Arnold is not in the first house.
solver.add(name[0] != names['Arnold'])

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    solution = []
    for i in range(3):
        house_num = i + 1
        person_name = [k for k, v in names.items() if v == model.evaluate(name[i]).as_long()][0]
        person_height = [k for k, v in heights.items() if v == model.evaluate(height[i]).as_long()][0]
        solution.append([str(house_num), person_name, person_height])
    
    result = {
        "solution": {
            "header": ["House", "Name", "Height"],
            "rows": solution
        }
    }
    print(result)
else:
    print("No solution found")