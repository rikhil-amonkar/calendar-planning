from z3 import *
import json

# Define the solver
solver = Solver()

# Define the variables
names = ['Arnold', 'Eric']
hair_colors = ['black', 'brown']
favorite_sports = ['basketball', 'soccer']
smoothies = ['desert', 'cherry']
houses = [1, 2]

# Create dictionaries to hold the Z3 variables
name_vars = {house: Int(f'name_{house}') for house in houses}
hair_color_vars = {house: Int(f'hair_color_{house}') for house in houses}
favorite_sport_vars = {house: Int(f'favorite_sport_{house}') for house in houses}
smoothie_vars = {house: Int(f'smoothie_{house}') for house in houses}

# Add constraints for unique values in each category
solver.add(Distinct([name_vars[house] for house in houses]))
solver.add(Distinct([hair_color_vars[house] for house in houses]))
solver.add(Distinct([favorite_sport_vars[house] for house in houses]))
solver.add(Distinct([smoothie_vars[house] for house in houses]))

# Map strings to integers for Z3
name_map = {name: i for i, name in enumerate(names)}
hair_color_map = {color: i for i, color in enumerate(hair_colors)}
favorite_sport_map = {sport: i for i, sport in enumerate(favorite_sports)}
smoothie_map = {smoothie: i for i, smoothie in enumerate(smoothies)}

# Add constraints based on clues
# Clue 1: The Desert smoothie lover is Arnold.
solver.add(smoothie_vars[1] == smoothie_map['desert'])
solver.add(name_vars[1] == name_map['Arnold'])

# Clue 2: The person who has brown hair is the person who loves basketball.
solver.add(Or(
    And(hair_color_vars[1] == hair_color_map['brown'], favorite_sport_vars[1] == favorite_sport_map['basketball']),
    And(hair_color_vars[2] == hair_color_map['brown'], favorite_sport_vars[2] == favorite_sport_map['basketball'])
))

# Clue 3: Arnold is somewhere to the left of the person who has black hair.
solver.add(Or(
    And(name_vars[1] == name_map['Arnold'], hair_color_vars[2] == hair_color_map['black']),
    And(name_vars[1] == name_map['Arnold'], hair_color_vars[1] != hair_color_map['black'])
))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    
    # Prepare the solution in the required format
    solution = {
        "solution": {
            "header": ["House", "Name", "HairColor", "FavoriteSport", "Smoothie"],
            "rows": []
        }
    }
    
    for house in houses:
        name = names[model[name_vars[house]].as_long()]
        hair_color = hair_colors[model[hair_color_vars[house]].as_long()]
        favorite_sport = favorite_sports[model[favorite_sport_vars[house]].as_long()]
        smoothie = smoothies[model[smoothie_vars[house]].as_long()]
        
        solution["solution"]["rows"].append([
            str(house),
            name,
            hair_color,
            favorite_sport,
            smoothie
        ])
    
    # Print the solution as JSON
    print(json.dumps(solution, indent=4))
else:
    print("No solution found")