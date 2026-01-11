from z3 import *

# Define the variables
house = [Int(f'house_{i}') for i in range(1, 5)]
name = [Int(f'name_{i}') for i in range(1, 5)]
color = [Int(f'color_{i}') for i in range(1, 5)]

# Define the domains
names = {'Peter': 1, 'Arnold': 2, 'Alice': 3, 'Eric': 4}
colors = {'yellow': 1, 'green': 2, 'red': 3, 'white': 4}

# Create the solver
solver = Solver()

# Add constraints
solver.add(Distinct(house))
solver.add(Distinct(name))
solver.add(Distinct(color))

# Clue 1: The person whose favorite color is green is in the third house.
solver.add(color[2] == colors['green'])

# Clue 2: Peter is in the first house.
solver.add(name[0] == names['Peter'])

# Clue 3: There is one house between the person whose favorite color is red and the person who loves yellow.
solver.add(Or(Abs(house[color.index(colors['red'])] - house[color.index(colors['yellow'])]) == 2))

# Clue 4: Arnold is directly left of Eric.
solver.add(house[name.index(names['Arnold'])] + 1 == house[name.index(names['Eric'])])

# Clue 5: Eric is the person who loves yellow.
solver.add(name[color.index(colors['yellow'])] == names['Eric'])

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = []
    for i in range(4):
        house_num = i + 1
        person_name = [k for k, v in names.items() if v == model.evaluate(name[i]).as_long()][0]
        person_color = [k for k, v in colors.items() if v == model.evaluate(color[i]).as_long()][0]
        solution.append([str(house_num), person_name, person_color])
    
    result = {
        "solution": {
            "header": ["House", "Name", "Color"],
            "rows": solution
        }
    }
    print(result)
else:
    print("No solution found")