from z3 import *

# Define the domain for each variable
names = ['Eric', 'Arnold']
sports = ['basketball', 'soccer']
hobbies = ['photography', 'gardening']

# Create variables for each house
house1_name = EnumSort('house1_name', names)[0]
house1_sport = EnumSort('house1_sport', sports)[0]
house1_hobby = EnumSort('house1_hobby', hobbies)[0]

house2_name = EnumSort('house2_name', names)[0]
house2_sport = EnumSort('house2_sport', sports)[0]
house2_hobby = EnumSort('house2_hobby', hobbies)[0]

# Create a solver instance
solver = Solver()

# Add constraints based on the clues
# Clue 1: Arnold enjoys gardening
solver.add(Or(
    And(house1_name == 'Arnold', house1_hobby == 'gardening'),
    And(house2_name == 'Arnold', house2_hobby == 'gardening')
))

# Clue 2: The photography enthusiast is not in the first house
solver.add(house1_hobby != 'photography')

# Clue 3: The person who loves soccer is not in the first house
solver.add(house1_sport != 'soccer')

# Ensure each person, sport, and hobby is unique across the houses
solver.add(Distinct(house1_name, house2_name))
solver.add(Distinct(house1_sport, house2_sport))
solver.add(Distinct(house1_hobby, house2_hobby))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    
    # Extract the values from the model
    house1_name_val = str(model[house1_name])
    house1_sport_val = str(model[house1_sport])
    house1_hobby_val = str(model[house1_hobby])
    
    house2_name_val = str(model[house2_name])
    house2_sport_val = str(model[house2_sport])
    house2_hobby_val = str(model[house2_hobby])
    
    # Format the solution as JSON
    solution = {
        "solution": {
            "header": ["House", "Name", "FavoriteSport", "Hobby"],
            "rows": [
                ["1", house1_name_val, house1_sport_val, house1_hobby_val],
                ["2", house2_name_val, house2_sport_val, house2_hobby_val]
            ]
        }
    }
    
    print(solution)
else:
    print("No solution found")