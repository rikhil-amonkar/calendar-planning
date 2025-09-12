from z3 import *

# Define the variables
house1_name = Int('house1_name')
house2_name = Int('house2_name')
house1_sport = Int('house1_sport')
house2_sport = Int('house2_sport')
house1_hobby = Int('house1_hobby')
house2_hobby = Int('house2_hobby')

# Define the domains for the variables
names = {'Eric': 0, 'Arnold': 1}
sports = {'basketball': 0, 'soccer': 1}
hobbies = {'photography': 0, 'gardening': 1}

# Create a solver instance
solver = Solver()

# Add constraints for unique names, sports, and hobbies
solver.add(Distinct(house1_name, house2_name))
solver.add(Distinct(house1_sport, house2_sport))
solver.add(Distinct(house1_hobby, house2_hobby))

# Add constraints based on the clues
# Clue 1: The person who enjoys gardening is Arnold.
solver.add(house1_hobby == hobbies['gardening'] ==>
           house1_name == names['Arnold'])
solver.add(house2_hobby == hobbies['gardening'] ==>
           house2_name == names['Arnold'])

# Clue 2: The photography enthusiast is not in the first house.
solver.add(house1_hobby != hobbies['photography'])

# Clue 3: The person who loves soccer is not in the first house.
solver.add(house1_sport != sports['soccer'])

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    
    # Extract the solution
    house1_name_val = [name for name, val in names.items() if model.evaluate(house1_name) == val][0]
    house2_name_val = [name for name, val in names.items() if model.evaluate(house2_name) == val][0]
    house1_sport_val = [sport for sport, val in sports.items() if model.evaluate(house1_sport) == val][0]
    house2_sport_val = [sport for sport, val in sports.items() if model.evaluate(house2_sport) == val][0]
    house1_hobby_val = [hobby for hobby, val in hobbies.items() if model.evaluate(house1_hobby) == val][0]
    house2_hobby_val = [hobby for hobby, val in hobbies.items() if model.evaluate(house2_hobby) == val][0]
    
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
    
    import json
    print(json.dumps(solution))
else:
    print("No solution found")