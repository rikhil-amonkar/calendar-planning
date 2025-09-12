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

# Add domain constraints for each variable
solver.add(Or(house1_name == names['Eric'], house1_name == names['Arnold']))
solver.add(Or(house2_name == names['Eric'], house2_name == names['Arnold']))
solver.add(Or(house1_sport == sports['basketball'], house1_sport == sports['soccer']))
solver.add(Or(house2_sport == sports['basketball'], house2_sport == sports['soccer']))
solver.add(Or(house1_hobby == hobbies['photography'], house1_hobby == hobbies['gardening']))
solver.add(Or(house2_hobby == hobbies['photography'], house2_hobby == hobbies['gardening']))

# Add constraints based on the clues
# Clue 1: The person who enjoys gardening is Arnold.
solver.add(Implies(house1_hobby == hobbies['gardening'], house1_name == names['Arnold']))
solver.add(Implies(house2_hobby == hobbies['gardening'], house2_name == names['Arnold']))

# Clue 2: The photography enthusiast is not in the first house.
solver.add(house1_hobby != hobbies['photography'])

# Clue 3: The person who loves soccer is not in the first house.
solver.add(house1_sport != sports['soccer'])

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    
    # Debugging: Print the model values
    print(f"house1_name: {model[house1_name]}")
    print(f"house2_name: {model[house2_name]}")
    print(f"house1_sport: {model[house1_sport]}")
    print(f"house2_sport: {model[house2_sport]}")
    print(f"house1_hobby: {model[house1_hobby]}")
    print(f"house2_hobby: {model[house2_hobby]}")
    
    # Extract the solution
    house1_name_val = [name for name, val in names.items() if model[house1_name] == val]
    house2_name_val = [name for name, val in names.items() if model[house2_name] == val]
    house1_sport_val = [sport for sport, val in sports.items() if model[house1_sport] == val]
    house2_sport_val = [sport for sport, val in sports.items() if model[house2_sport] == val]
    house1_hobby_val = [hobby for hobby, val in hobbies.items() if model[house1_hobby] == val]
    house2_hobby_val = [hobby for hobby, val in hobbies.items() if model[house2_hobby] == val]
    
    # Ensure there is exactly one match
    if len(house1_name_val) == 0 or len(house2_name_val) == 0 or \
       len(house1_sport_val) == 0 or len(house2_sport_val) == 0 or \
       len(house1_hobby_val) == 0 or len(house2_hobby_val) == 0:
        raise ValueError("Model does not match any expected values in the dictionaries.")
    
    house1_name_val = house1_name_val[0]
    house2_name_val = house2_name_val[0]
    house1_sport_val = house1_sport_val[0]
    house2_sport_val = house2_sport_val[0]
    house1_hobby_val = house1_hobby_val[0]
    house2_hobby_val = house2_hobby_val[0]
    
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