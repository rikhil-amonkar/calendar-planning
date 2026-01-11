from z3 import *

# Define variables
house1_name = String('house1_name')
house2_name = String('house2_name')
house1_hair_color = String('house1_hair_color')
house2_hair_color = String('house2_hair_color')
house1_favorite_sport = String('house1_favorite_sport')
house2_favorite_sport = String('house2_favorite_sport')
house1_smoothie = String('house1_smoothie')
house2_smoothie = String('house2_smoothie')

# Create a solver instance
solver = Solver()

# Add constraints for unique values
solver.add(Distinct(house1_name, house2_name))
solver.add(Distinct(house1_hair_color, house2_hair_color))
solver.add(Distinct(house1_favorite_sport, house2_favorite_sport))
solver.add(Distinct(house1_smoothie, house2_smoothie))

# Add specific constraints from the problem statement
# Constraint 1: The Desert smoothie lover is Arnold.
solver.add(Or(
    And(house1_smoothie == 'desert', house1_name == 'Arnold'),
    And(house2_smoothie == 'desert', house2_name == 'Arnold')
))

# Constraint 2: The person who has brown hair is the person who loves basketball.
solver.add(Or(
    And(house1_hair_color == 'brown', house1_favorite_sport == 'basketball'),
    And(house2_hair_color == 'brown', house2_favorite_sport == 'basketball')
))

# Constraint 3: Arnold is somewhere to the left of the person who has black hair.
solver.add(Implies(house1_name == 'Arnold', house2_hair_color == 'black'))

# Possible values for each variable
names = ['Arnold', 'Eric']
hair_colors = ['black', 'brown']
favorite_sports = ['basketball', 'soccer']
smoothies = ['desert', 'cherry']

# Add constraints for possible values
solver.add(Or(house1_name == 'Arnold', house1_name == 'Eric'))
solver.add(Or(house2_name == 'Arnold', house2_name == 'Eric'))
solver.add(Or(house1_hair_color == 'black', house1_hair_color == 'brown'))
solver.add(Or(house2_hair_color == 'black', house2_hair_color == 'brown'))
solver.add(Or(house1_favorite_sport == 'basketball', house1_favorite_sport == 'soccer'))
solver.add(Or(house2_favorite_sport == 'basketball', house2_favorite_sport == 'soccer'))
solver.add(Or(house1_smoothie == 'desert', house1_smoothie == 'cherry'))
solver.add(Or(house2_smoothie == 'desert', house2_smoothie == 'cherry'))

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "HairColor", "FavoriteSport", "Smoothie"],
            "rows": [
                ["1", model[house1_name].as_string(), model[house1_hair_color].as_string(), model[house1_favorite_sport].as_string(), model[house1_smoothie].as_string()],
                ["2", model[house2_name].as_string(), model[house2_hair_color].as_string(), model[house2_favorite_sport].as_string(), model[house2_smoothie].as_string()]
            ]
        }
    }
    print(solution)
else:
    print("No solution found")