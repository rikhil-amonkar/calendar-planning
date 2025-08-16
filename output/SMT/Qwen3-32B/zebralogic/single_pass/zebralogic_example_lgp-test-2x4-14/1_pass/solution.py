import json
from z3 import *

solver = Solver()

# Variables for house 1 and 2
name1 = String('name1')
style1 = String('style1')
smoothie1 = String('smoothie1')
pet1 = String('pet1')

name2 = String('name2')
style2 = String('style2')
smoothie2 = String('smoothie2')
pet2 = String('pet2')

# Add possible value constraints
solver.add(Or(name1 == 'Eric', name1 == 'Arnold'))
solver.add(Or(style1 == 'victorian', style1 == 'colonial'))
solver.add(Or(smoothie1 == 'cherry', smoothie1 == 'desert'))
solver.add(Or(pet1 == 'dog', pet1 == 'cat'))

solver.add(Or(name2 == 'Eric', name2 == 'Arnold'))
solver.add(Or(style2 == 'victorian', style2 == 'colonial'))
solver.add(Or(smoothie2 == 'cherry', smoothie2 == 'desert'))
solver.add(Or(pet2 == 'dog', pet2 == 'cat'))

# Uniqueness constraints
solver.add(name1 != name2)
solver.add(style1 != style2)
solver.add(smoothie1 != smoothie2)
solver.add(pet1 != pet2)

# Clue 1: Cherry implies dog
solver.add(Implies(smoothie1 == 'cherry', pet1 == 'dog'))
solver.add(Implies(smoothie2 == 'cherry', pet2 == 'dog'))

# Clue 2: Victorian implies dog
solver.add(Implies(style1 == 'victorian', pet1 == 'dog'))
solver.add(Implies(style2 == 'victorian', pet2 == 'dog'))

# Clue 3: Victorian house is left of Eric
victorian_house_num = If(style1 == 'victorian', 1, 2)
eric_house_num = If(name1 == 'Eric', 1, 2)
solver.add(victorian_house_num < eric_house_num)

if solver.check() == sat:
    model = solver.model()
    def get_val(var):
        return model.eval(var).as_string()

    h1_name = get_val(name1)
    h1_style = get_val(style1)
    h1_smoothie = get_val(smoothie1)
    h1_pet = get_val(pet1)

    h2_name = get_val(name2)
    h2_style = get_val(style2)
    h2_smoothie = get_val(smoothie2)
    h2_pet = get_val(pet2)

    solution = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "Smoothie", "Pet"],
            "rows": [
                ["1", h1_name, h1_style, h1_smoothie, h1_pet],
                ["2", h2_name, h2_style, h2_smoothie, h2_pet]
            ]
        }
    }

    print(json.dumps(solution))
else:
    print("No solution found.")