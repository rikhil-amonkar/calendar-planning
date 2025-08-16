from z3 import *

# Create a solver instance
solver = Solver()

# Define variables for each attribute of each person
names = ['Arnold', 'Eric']
sports = ['basketball', 'soccer']
hair_colors = ['brown', 'black']
heights = ['very short', 'short']
smoothies = ['desert', 'cherry']
flowers = ['daffodils', 'carnations']

# Create variables for each house
house1_name = String('house1_name')
house2_name = String('house2_name')

house1_sport = String('house1_sport')
house2_sport = String('house2_sport')

house1_hair_color = String('house1_hair_color')
house2_hair_color = String('house2_hair_color')

house1_height = String('house1_height')
house2_height = String('house2_height')

house1_smoothie = String('house1_smoothie')
house2_smoothie = String('house2_smoothie')

house1_flower = String('house1_flower')
house2_flower = String('house2_flower')

# Add constraints for each attribute being unique across houses
solver.add(Distinct(house1_name, house2_name))
solver.add(Distinct(house1_sport, house2_sport))
solver.add(Distinct(house1_hair_color, house2_hair_color))
solver.add(Distinct(house1_height, house2_height))
solver.add(Distinct(house1_smoothie, house2_smoothie))
solver.add(Distinct(house1_flower, house2_flower))

# Add domain constraints for each variable
for var in [house1_name, house2_name]:
    solver.add(Or(var == 'Arnold', var == 'Eric'))

for var in [house1_sport, house2_sport]:
    solver.add(Or(var == 'basketball', var == 'soccer'))

for var in [house1_hair_color, house2_hair_color]:
    solver.add(Or(var == 'brown', var == 'black'))

for var in [house1_height, house2_height]:
    solver.add(Or(var == 'very short', var == 'short'))

for var in [house1_smoothie, house2_smoothie]:
    solver.add(Or(var == 'desert', var == 'cherry'))

for var in [house1_flower, house2_flower]:
    solver.add(Or(var == 'daffodils', var == 'carnations'))

# Add specific clues as constraints
# Clue 1: The person who loves soccer is not in the second house.
solver.add(house2_sport != 'soccer')

# Clue 2: The Desert smoothie lover is directly left of the person who is very short.
solver.add(Implies(house1_smoothie == 'desert', house2_height == 'very short'))

# Clue 3: The person who is very short is the person who has brown hair.
solver.add(Implies(house2_height == 'very short', house2_hair_color == 'brown'))

# Clue 4: The person who loves a carnations arrangement is the Desert smoothie lover.
solver.add(Implies(house1_smoothie == 'desert', house1_flower == 'carnations'))

# Clue 5: Eric and the person who has brown hair are next to each other.
solver.add(Or(
    And(house1_name == 'Eric', house2_hair_color == 'brown'),
    And(house2_name == 'Eric', house1_hair_color == 'brown')
))

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "FavoriteSport", "HairColor", "Height", "Smoothie", "Flower"],
            "rows": [
                ["1",
                 model[house1_name].as_string(),
                 model[house1_sport].as_string(),
                 model[house1_hair_color].as_string(),
                 model[house1_height].as_string(),
                 model[house1_smoothie].as_string(),
                 model[house1_flower].as_string()],
                ["2",
                 model[house2_name].as_string(),
                 model[house2_sport].as_string(),
                 model[house2_hair_color].as_string(),
                 model[house2_height].as_string(),
                 model[house2_smoothie].as_string(),
                 model[house2_flower].as_string()]
            ]
        }
    }
    print(solution)
else:
    print("No solution found")