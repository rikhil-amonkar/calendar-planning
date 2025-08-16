from z3 import *

# Create a solver instance
solver = Solver()

# Define variables
house1_name = String('house1_name')
house2_name = String('house2_name')
house1_favorite_sport = String('house1_favorite_sport')
house2_favorite_sport = String('house2_favorite_sport')
house1_hobby = String('house1_hobby')
house2_hobby = String('house2_hobby')

# Define the domain for each variable
names = ['Eric', 'Arnold']
sports = ['basketball', 'soccer']
hobbies = ['photography', 'gardening']

# Add constraints for unique names, sports, and hobbies
solver.add(Distinct(house1_name, house2_name))
solver.add(Distinct(house1_favorite_sport, house2_favorite_sport))
solver.add(Distinct(house1_hobby, house2_hobby))

# Add constraints based on clues
# Clue 1: The person who enjoys gardening is Arnold.
solver.add(Implies(house1_hobby == 'gardening', house1_name == 'Arnold'))
solver.add(Implies(house2_hobby == 'gardening', house2_name == 'Arnold'))

# Clue 2: The photography enthusiast is not in the first house.
solver.add(house1_hobby != 'photography')

# Clue 3: The person who loves soccer is not in the first house.
solver.add(house1_favorite_sport != 'soccer')

# Add constraints for the domain of each variable
solver.add(Or(house1_name == 'Eric', house1_name == 'Arnold'))
solver.add(Or(house2_name == 'Eric', house2_name == 'Arnold'))
solver.add(Or(house1_favorite_sport == 'basketball', house1_favorite_sport == 'soccer'))
solver.add(Or(house2_favorite_sport == 'basketball', house2_favorite_sport == 'soccer'))
solver.add(Or(house1_hobby == 'photography', house1_hobby == 'gardening'))
solver.add(Or(house2_hobby == 'photography', house2_hobby == 'gardening'))

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "FavoriteSport", "Hobby"],
            "rows": [
                ["1", model[house1_name].as_string(), model[house1_favorite_sport].as_string(), model[house1_hobby].as_string()],
                ["2", model[house2_name].as_string(), model[house2_favorite_sport].as_string(), model[house2_hobby].as_string()]
            ]
        }
    }
    print(solution)
else:
    print("No solution found")