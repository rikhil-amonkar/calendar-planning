from z3 import *

# Create the solver
solver = Solver()

# Define variables
names = ['Peter', 'Arnold', 'Alice', 'Eric']
flowers = ['roses', 'daffodils', 'carnations', 'lilies']
hobbies = ['photography', 'painting', 'cooking', 'gardening']
pets = ['dog', 'fish', 'bird', 'cat']
colors = ['red', 'yellow', 'green', 'white']
house_styles = ['craftsman', 'colonial', 'ranch', 'victorian']

# Create variables for each house
name_vars = [String(f'name_{i}') for i in range(4)]
flower_vars = [String(f'flower_{i}') for i in range(4)]
hobby_vars = [String(f'hobby_{i}') for i in range(4)]
pet_vars = [String(f'pet_{i}') for i in range(4)]
color_vars = [String(f'color_{i}') for i in range(4)]
house_style_vars = [String(f'house_style_{i}') for i in range(4)]

# Add constraints for unique values
solver.add(Distinct(name_vars))
solver.add(Distinct(flower_vars))
solver.add(Distinct(hobby_vars))
solver.add(Distinct(pet_vars))
solver.add(Distinct(color_vars))
solver.add(Distinct(house_style_vars))

# Add constraints based on clues
# Clue 1 & 6: The person in a Craftsman-style house is Arnold and is in the second house.
solver.add(house_style_vars[1] == 'craftsman')
solver.add(name_vars[1] == 'Arnold')

# Clue 2: The person who loves the rose bouquet is somewhere to the right of Peter.
# Clue 5: The person who loves the rose bouquet is the person whose favorite color is red.
# Clue 13: The person living in a colonial-style house is the person whose favorite color is red.
for i in range(4):
    if i != 1:  # Arnold is in the second house
        solver.add(Or(name_vars[i] != 'Peter', flower_vars[i] == 'roses'))
        solver.add(Or(flower_vars[i] != 'roses', color_vars[i] == 'red'))
        solver.add(Or(color_vars[i] != 'red', house_style_vars[i] == 'colonial'))

# Clue 3: The photography enthusiast is the person who owns a dog.
solver.add(Or([And(hobby_vars[i] == 'photography', pet_vars[i] == 'dog') for i in range(4)]))

# Clue 4: The person who loves a bouquet of daffodils is not in the fourth house.
solver.add(flower_vars[3] != 'daffodils')

# Clue 7: Eric is the person residing in a Victorian house.
# Clue 14: The person who has a cat is Eric.
solver.add(house_style_vars[3] == 'victorian')
solver.add(name_vars[3] == 'Eric')
solver.add(pet_vars[3] == 'cat')

# Clue 8: The person with an aquarium of fish is the person who loves white.
# Clue 10: The person who loves white is the person who loves a carnations arrangement.
solver.add(Or([And(pet_vars[i] == 'fish', color_vars[i] == 'white', flower_vars[i] == 'carnations') for i in range(4)]))

# Clue 9: The person who loves cooking is somewhere to the right of the person whose favorite color is red.
for i in range(4):
    for j in range(i+1, 4):
        solver.add(Or(color_vars[i] != 'red', hobby_vars[j] == 'cooking'))

# Clue 11: The person who loves white is somewhere to the right of the person who enjoys gardening.
for i in range(4):
    for j in range(i+1, 4):
        solver.add(Or(color_vars[j] != 'white', hobby_vars[i] == 'gardening'))

# Clue 12: The person who loves a bouquet of daffodils is the person who loves yellow.
solver.add(Or([And(flower_vars[i] == 'daffodils', color_vars[i] == 'yellow') for i in range(4)]))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = []
    for i in range(4):
        house_info = [
            str(i + 1),
            model[name_vars[i]].as_string()[1:-1],  # Remove quotes
            model[flower_vars[i]].as_string()[1:-1],
            model[hobby_vars[i]].as_string()[1:-1],
            model[pet_vars[i]].as_string()[1:-1],
            model[color_vars[i]].as_string()[1:-1],
            model[house_style_vars[i]].as_string()[1:-1]
        ]
        solution.append(house_info)
    
    result = {
        "solution": {
            "header": ["House", "Name", "Flower", "Hobby", "Pet", "Color", "HouseStyle"],
            "rows": solution
        }
    }
    print(result)
else:
    print("No solution found")