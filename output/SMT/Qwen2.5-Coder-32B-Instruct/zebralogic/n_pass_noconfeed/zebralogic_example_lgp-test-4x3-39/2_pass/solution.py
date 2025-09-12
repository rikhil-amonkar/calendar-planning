from z3 import *

# Define the variables
names = ['Eric', 'Alice', 'Peter', 'Arnold']
hair_colors = ['blonde', 'black', 'red', 'brown']
favorite_sports = ['swimming', 'soccer', 'basketball', 'tennis']
houses = [1, 2, 3, 4]

# Create the solver
solver = Solver()

# Define the arrays for each attribute
name_map = {house: Int(f'name_{house}') for house in houses}
hair_color_map = {house: Int(f'hair_color_{house}') for house in houses}
favorite_sport_map = {house: Int(f'favorite_sport_{house}') for house in houses}

# Add constraints for unique values
solver.add(Distinct([name_map[house] for house in houses]))
solver.add(Distinct([hair_color_map[house] for house in houses]))
solver.add(Distinct([favorite_sport_map[house] for house in houses]))

# Map values to integers
name_to_int = {name: i for i, name in enumerate(names)}
int_to_name = {i: name for i, name in enumerate(names)}

hair_color_to_int = {color: i for i, color in enumerate(hair_colors)}
int_to_hair_color = {i: color for i, color in enumerate(hair_colors)}

favorite_sport_to_int = {sport: i for i, sport in enumerate(favorite_sports)}
int_to_favorite_sport = {i: sport for i, sport in enumerate(favorite_sports)}

# Add constraints based on clues
# 1. The person who loves soccer is not in the second house.
solver.add(favorite_sport_map[2] != favorite_sport_to_int['soccer'])

# 2. Eric is the person who has blonde hair.
solver.add(name_map[houses.index(1)] == name_to_int['Eric'])
solver.add(hair_color_map[houses.index(1)] == hair_color_to_int['blonde'])

# 3. The person who has blonde hair is somewhere to the right of the person who loves basketball.
for i in range(1, 4):
    solver.add(Or(hair_color_map[i] != hair_color_to_int['blonde'], favorite_sport_map[i + 1] == favorite_sport_to_int['basketball']))

# 4. The person who has black hair is the person who loves tennis.
house = Int('house')
solver.add(Exists(house, And(house >= 1, house <= 4, hair_color_map[house] == hair_color_to_int['black'],
                              favorite_sport_map[house] == favorite_sport_to_int['tennis'])))

# 5. Arnold is somewhere to the left of the person who has red hair.
solver.add(Exists(i, And(i >= 1, i <= 3, name_map[i] == name_to_int['Arnold'], 
                         Exists(j, And(j >= 2, j <= 4, hair_color_map[j] == hair_color_to_int['red'], i < j)))))

# 6. Alice is the person who loves swimming.
solver.add(Exists(house, And(house >= 1, house <= 4, name_map[house] == name_to_int['Alice'], 
                             favorite_sport_map[house] == favorite_sport_to_int['swimming'])))

# 7. The person who has red hair is directly left of the person who has black hair.
solver.add(Exists(i, And(i >= 1, i <= 3, hair_color_map[i] == hair_color_to_int['red'], 
                         hair_color_map[i + 1] == hair_color_to_int['black'])))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "HairColor", "FavoriteSport"],
            "rows": []
        }
    }
    for house in houses:
        name = int_to_name[model.evaluate(name_map[house]).as_long()]
        hair_color = int_to_hair_color[model.evaluate(hair_color_map[house]).as_long()]
        favorite_sport = int_to_favorite_sport[model.evaluate(favorite_sport_map[house]).as_long()]
        solution["solution"]["rows"].append([str(house), name, hair_color, favorite_sport])
    
    import json
    print(json.dumps(solution))
else:
    print("No solution found")