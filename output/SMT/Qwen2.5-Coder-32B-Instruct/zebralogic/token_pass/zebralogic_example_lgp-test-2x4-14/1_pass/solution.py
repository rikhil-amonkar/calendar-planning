from z3 import *

# Define variables
house = [Int(f'house_{i}') for i in range(1, 3)]
name = [Int(f'name_{i}') for i in range(1, 3)]
house_style = [Int(f'house_style_{i}') for i in range(1, 3)]
smoothie = [Int(f'smoothie_{i}') for i in range(1, 3)]
pet = [Int(f'pet_{i}') for i in range(1, 3)]

# Constants for names, house styles, smoothies, and pets
ERIC = 0
ARNOLD = 1
VICTORIAN = 0
COLONIAL = 1
CHERRY = 0
DESERT = 1
DOG = 0
CAT = 1

# Create solver instance
solver = Solver()

# Constraints for unique values in each category
solver.add(Distinct(name))
solver.add(Distinct(house_style))
solver.add(Distinct(smoothie))
solver.add(Distinct(pet))

# Constraint for names
solver.add(name[0] == ARNOLD)
solver.add(name[1] == ERIC)

# Constraint for house styles
solver.add(house_style[0] == VICTORIAN)
solver.add(house_style[1] == COLONIAL)

# Constraint for smoothies
solver.add(smoothie[0] == CHERRY)
solver.add(smoothie[1] == DESERT)

# Constraint for pets
solver.add(pet[0] == DOG)
solver.add(pet[1] == CAT)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "Smoothie", "Pet"],
            "rows": [
                ["1", "Arnold" if model.evaluate(name[0]) == ARNOLD else "Eric",
                 "Victorian" if model.evaluate(house_style[0]) == VICTORIAN else "Colonial",
                 "Cherry" if model.evaluate(smoothie[0]) == CHERRY else "Desert",
                 "Dog" if model.evaluate(pet[0]) == DOG else "Cat"],
                ["2", "Arnold" if model.evaluate(name[1]) == ARNOLD else "Eric",
                 "Victorian" if model.evaluate(house_style[1]) == VICTORIAN else "Colonial",
                 "Cherry" if model.evaluate(smoothie[1]) == CHERRY else "Desert",
                 "Dog" if model.evaluate(pet[1]) == DOG else "Cat"]
            ]
        }
    }
    print(solution)
else:
    print("No solution found")