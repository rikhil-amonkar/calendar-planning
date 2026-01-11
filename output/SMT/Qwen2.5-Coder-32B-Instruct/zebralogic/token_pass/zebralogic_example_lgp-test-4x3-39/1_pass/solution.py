from z3 import *

# Define the solver
solver = Solver()

# Define variables
names = ['Eric', 'Alice', 'Peter', 'Arnold']
hair_colors = ['blonde', 'black', 'red', 'brown']
favorite_sports = ['swimming', 'soccer', 'basketball', 'tennis']

# Create arrays for each attribute
house_names = [String(f'name_{i}') for i in range(1, 5)]
house_hair_colors = [String(f'hair_color_{i}') for i in range(1, 5)]
house_favorite_sports = [String(f'favorite_sport_{i}') for i in range(1, 5)]

# Add constraints for unique values in each attribute
solver.add(Distinct(house_names))
solver.add(Distinct(house_hair_colors))
solver.add(Distinct(house_favorite_sports))

# Add constraints based on the clues
# Clue 1: The person who loves soccer is not in the second house.
solver.add(house_favorite_sports[1] != 'soccer')

# Clue 2: Eric is the person who has blonde hair.
solver.add(Or([And(house_names[i] == 'Eric', house_hair_colors[i] == 'blonde') for i in range(4)]))

# Clue 3: The person who has blonde hair is somewhere to the right of the person who loves basketball.
solver.add(Or([And(house_hair_colors[j] == 'blonde', house_favorite_sports[i] == 'basketball') for i in range(4) for j in range(i+1, 4)]))

# Clue 4: The person who has black hair is the person who loves tennis.
solver.add(Or([And(house_hair_colors[i] == 'black', house_favorite_sports[i] == 'tennis') for i in range(4)]))

# Clue 5: Arnold is somewhere to the left of the person who has red hair.
solver.add(Or([And(house_names[i] == 'Arnold', house_hair_colors[j] == 'red') for i in range(4) for j in range(i+1, 4)]))

# Clue 6: Alice is the person who loves swimming.
solver.add(Or([And(house_names[i] == 'Alice', house_favorite_sports[i] == 'swimming') for i in range(4)]))

# Clue 7: The person who has red hair is directly left of the person who has black hair.
solver.add(Or([And(house_hair_colors[i] == 'red', house_hair_colors[i+1] == 'black') for i in range(3)]))

# Check if the solver can find a solution
if solver.check() == sat:
    model = solver.model()
    result = {
        "solution": {
            "header": ["House", "Name", "HairColor", "FavoriteSport"],
            "rows": []
        }
    }
    for i in range(4):
        house_number = str(i + 1)
        name = model[house_names[i]].as_string()[1:-1]
        hair_color = model[house_hair_colors[i]].as_string()[1:-1]
        favorite_sport = model[house_favorite_sports[i]].as_string()[1:-1]
        result["solution"]["rows"].append([house_number, name, hair_color, favorite_sport])
    print(result)
else:
    print("No solution found")