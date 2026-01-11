from z3 import *

# Define the variables
names = ['Arnold', 'Eric', 'Peter']
flowers = ['carnations', 'lilies', 'daffodils']
hair_colors = ['black', 'brown', 'blonde']
favorite_sports = ['soccer', 'basketball', 'tennis']
house_styles = ['colonial', 'ranch', 'victorian']
pets = ['fish', 'dog', 'cat']

# Create variables for each house
house1 = [String('house1_' + attr) for attr in ['name', 'flower', 'hair_color', 'favorite_sport', 'house_style', 'pet']]
house2 = [String('house2_' + attr) for attr in ['name', 'flower', 'hair_color', 'favorite_sport', 'house_style', 'pet']]
house3 = [String('house3_' + attr) for attr in ['name', 'flower', 'hair_color', 'favorite_sport', 'house_style', 'pet']]

# Create a solver instance
solver = Solver()

# Add constraints for each house
for house in [house1, house2, house3]:
    solver.add(Or([house[i] == val for val in eval(vars()[i])])) for i in range(6))

# Add constraints based on clues
solver.add(house2[2] == 'blonde')  # Clue 2
solver.add(house2[1] == 'daffodils')  # Clue 3
solver.add(house2[0] == 'Peter')  # Clue 4
solver.add(house2[5] == 'dog')  # Clue 6
solver.add(house3[3] == 'soccer')  # Clue 8
solver.add(house3[5] == 'cat')  # Clue 1
solver.add(house3[4] == 'colonial')  # Clue 10
solver.add(house1[0] == 'Arnold')  # Clue 5
solver.add(house1[1] == 'carnations')  # Clue 7
solver.add(house1[2] == 'brown')  # By elimination
solver.add(house1[3] == 'tennis')  # By elimination
solver.add(house1[4] == 'victorian')  # By elimination
solver.add(house1[5] == 'fish')  # By elimination
solver.add(house3[0] == 'Eric')  # By elimination

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    result = {
        "solution": {
            "header": ["House", "Name", "Flower", "HairColor", "FavoriteSport", "HouseStyle", "Pet"],
            "rows": [
                ["1", model[house1[0]].as_string(), model[house1[1]].as_string(), model[house1[2]].as_string(), model[house1[3]].as_string(), model[house1[4]].as_string(), model[house1[5]].as_string()],
                ["2", model[house2[0]].as_string(), model[house2[1]].as_string(), model[house2[2]].as_string(), model[house2[3]].as_string(), model[house2[4]].as_string(), model[house2[5]].as_string()],
                ["3", model[house3[0]].as_string(), model[house3[1]].as_string(), model[house3[2]].as_string(), model[house3[3]].as_string(), model[house3[4]].as_string(), model[house3[5]].as_string()]
            ]
        }
    }
    print(result)
else:
    print("No solution found")