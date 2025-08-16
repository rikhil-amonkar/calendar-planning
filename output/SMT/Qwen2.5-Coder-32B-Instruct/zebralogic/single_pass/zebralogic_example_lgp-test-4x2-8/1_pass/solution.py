from z3 import *

# Define variables
house = [Int(f'house_{i}') for i in range(1, 5)]
name = [String(f'name_{i}') for i in range(1, 5)]
color = [String(f'color_{i}') for i in range(1, 5)]

# Create solver instance
solver = Solver()

# Define domains for each variable
names = ['Peter', 'Arnold', 'Alice', 'Eric']
colors = ['yellow', 'green', 'red', 'white']

for i in range(4):
    solver.add(name[i] == Or([StringVal(n) for n in names]))
    solver.add(color[i] == Or([StringVal(c) for c in colors]))

# Add constraints based on clues
# Clue 1: The person whose favorite color is green is in the third house.
solver.add(color[2] == StringVal('green'))

# Clue 2: Peter is in the first house.
solver.add(name[0] == StringVal('Peter'))

# Clue 3: There is one house between the person whose favorite color is red and the person who loves yellow.
# This means if red is in house i, yellow must be in house i-2 or i+2, and vice versa.
solver.add(Or(And(color[0] == StringVal('red'), color[2] == StringVal('yellow')),
              And(color[2] == StringVal('red'), color[0] == StringVal('yellow')),
              And(color[1] == StringVal('red'), color[3] == StringVal('yellow')),
              And(color[3] == StringVal('red'), color[1] == StringVal('yellow'))))

# Clue 4: Arnold is directly left of Eric.
solver.add(Or(And(name[0] == StringVal('Arnold'), name[1] == StringVal('Eric')),
              And(name[1] == StringVal('Arnold'), name[2] == StringVal('Eric')),
              And(name[2] == StringVal('Arnold'), name[3] == StringVal('Eric'))))

# Clue 5: Eric is the person who loves yellow.
solver.add(name[i] == StringVal('Eric') for i in range(4)).only_if(color[i] == StringVal('yellow'))

# Ensure all names and colors are unique
solver.add(Distinct(name))
solver.add(Distinct(color))

# Check if the solution exists
if solver.check() == sat:
    model = solver.model()
    solution = []
    for i in range(4):
        h = i + 1
        n = model.evaluate(name[i]).as_string()[1:-1]  # Remove quotes
        c = model.evaluate(color[i]).as_string()[1:-1]  # Remove quotes
        solution.append([str(h), n, c])
    
    result = {
        "solution": {
            "header": ["House", "Name", "Color"],
            "rows": solution
        }
    }
    print(result)
else:
    print("No solution found")