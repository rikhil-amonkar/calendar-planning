from z3 import *
import json

solver = Solver()

# Variables for house 1
name1 = String('name1')
style1 = String('style1')
smoothie1 = String('smoothie1')
pet1 = String('pet1')

# Variables for house 2
name2 = String('name2')
style2 = String('style2')
smoothie2 = String('smoothie2')
pet2 = String('pet2')

# Domain constraints
solver.add(Or(name1 == 'Eric', name1 == 'Arnold'))
solver.add(Or(name2 == 'Eric', name2 == 'Arnold'))

solver.add(Or(style1 == 'victorian', style1 == 'colonial'))
solver.add(Or(style2 == 'victorian', style2 == 'colonial'))

solver.add(Or(smoothie1 == 'cherry', smoothie1 == 'desert'))
solver.add(Or(smoothie2 == 'cherry', smoothie2 == 'desert'))

solver.add(Or(pet1 == 'dog', pet1 == 'cat'))
solver.add(Or(pet2 == 'dog', pet2 == 'cat'))

# Uniqueness constraints
solver.add(name1 != name2)
solver.add(style1 != style2)
solver.add(smoothie1 != smoothie2)
solver.add(pet1 != pet2)

# Clue 1: Cherry smoothie owner has dog
solver.add(If(smoothie1 == 'cherry', pet1 == 'dog', True))
solver.add(If(smoothie2 == 'cherry', pet2 == 'dog', True))

# Clue 2: Victorian house owner has dog
solver.add(If(style1 == 'victorian', pet1 == 'dog', True))
solver.add(If(style2 == 'victorian', pet2 == 'dog', True))

# Clue 3: Victorian is left of Eric
solver.add(Implies(style1 == 'victorian', name2 == 'Eric'))
solver.add(Implies(style2 == 'victorian', False))  # Victorian can't be in house 2

if solver.check() == sat:
    model = solver.model()
    # Extract values for each house
    h1_name = str(model[name1])
    h1_style = str(model[style1])
    h1_smoothie = str(model[smoothie1])
    h1_pet = str(model[pet1])

    h2_name = str(model[name2])
    h2_style = str(model[style2])
    h2_smoothie = str(model[smoothie2])
    h2_pet = str(model[pet2])

    solution = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "Smoothie", "Pet"],
            "rows": [
                ["1", h1_name, h1_style, h1_smoothie, h1_pet],
                ["2", h2_name, h2_style, h2_smoothie, h2_pet]
            ]
        }
    }

    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")