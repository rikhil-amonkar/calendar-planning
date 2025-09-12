from z3 import *
import json

# Define the solver
solver = Solver()

# Define variables
names = ['Eric', 'Arnold']
hobbies = ['gardening', 'photography']
pets = ['cat', 'dog']
heights = ['short', 'very short']
houses = [1, 2]

# Create dictionaries to map variables to Z3 variables
name_vars = {house: Int(f'name_{house}') for house in houses}
hobby_vars = {house: Int(f'hobby_{house}') for house in houses}
pet_vars = {house: Int(f'pet_{house}') for house in houses}
height_vars = {house: Int(f'height_{house}') for house in houses}

# Add constraints for unique values within each category
solver.add(Distinct([name_vars[house] for house in houses]))
solver.add(Distinct([hobby_vars[house] for house in houses]))
solver.add(Distinct([pet_vars[house] for house in houses]))
solver.add(Distinct([height_vars[house] for house in houses]))

# Map string values to integers
name_map = {name: i for i, name in enumerate(names)}
hobby_map = {hobby: i for i, hobby in enumerate(hobbies)}
pet_map = {pet: i for i, pet in enumerate(pets)}
height_map = {height: i for i, height in enumerate(heights)}

# Add constraints based on clues
# Clue 1: The person who is very short is the photography enthusiast.
solver.add(Implies(height_vars[1] == height_map['very short'], hobby_vars[1] == hobby_map['photography']))
solver.add(Implies(height_vars[2] == height_map['very short'], hobby_vars[2] == hobby_map['photography']))

# Clue 2: Eric is the person who is very short.
solver.add(name_vars[1] == name_map['Eric'] if height_vars[1] == height_map['very short'] else True)
solver.add(name_vars[2] == name_map['Eric'] if height_vars[2] == height_map['very short'] else True)

# Clue 3: The person who has a cat is somewhere to the right of the person who is very short.
solver.add(Or(
    And(height_vars[1] == height_map['very short'], pet_vars[2] == pet_map['cat']),
    And(height_vars[2] == height_map['very short'], pet_vars[2] == pet_map['cat'])
))

# Solve the constraints
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Hobby", "Pet", "Height"],
            "rows": []
        }
    }
    for house in houses:
        name = names[model.evaluate(name_vars[house]).as_long()]
        hobby = hobbies[model.evaluate(hobby_vars[house]).as_long()]
        pet = pets[model.evaluate(pet_vars[house]).as_long()]
        height = heights[model.evaluate(height_vars[house]).as_long()]
        solution["solution"]["rows"].append([str(house), name, hobby, pet, height])
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")