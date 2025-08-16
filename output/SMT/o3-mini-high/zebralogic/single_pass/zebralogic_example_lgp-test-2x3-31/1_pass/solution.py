import json
from z3 import *

# Encoding:
# For Name: 0 -> "Arnold", 1 -> "Eric"
# For FavoriteSport: 0 -> "basketball", 1 -> "soccer"
# For Hobby: 0 -> "gardening", 1 -> "photography"

# Create the Z3 solver instance
s = Solver()

# Define variables for each house
house1_name = Int('house1_name')
house2_name = Int('house2_name')
house1_sport = Int('house1_sport')
house2_sport = Int('house2_sport')
house1_hobby = Int('house1_hobby')
house2_hobby = Int('house2_hobby')

# Each variable can be 0 or 1 since we have exactly 2 options per attribute.
for var in [house1_name, house2_name, house1_sport, house2_sport, house1_hobby, house2_hobby]:
    s.add(Or(var == 0, var == 1))

# Ensure all attributes are unique across houses.
s.add(house1_name != house2_name)
s.add(house1_sport != house2_sport)
s.add(house1_hobby != house2_hobby)

# Clue 2: "The photography enthusiast is not in the first house."
# Photography is encoded as 1, so house 1's hobby cannot be 1.
s.add(house1_hobby == 0)  # Therefore, house1_hobby must be gardening.

# Clue 3: "The person who loves soccer is not in the first house."
# Soccer is encoded as 1 for FavoriteSport.
s.add(house1_sport == 0)  # Therefore, house1_sport must be basketball.

# Clue 1: "The person who enjoys gardening is Arnold."
# Gardening is encoded as 0 for Hobby and Arnold is 0 for Name.
# Enforce that in each house: having gardening <=> being Arnold.
s.add(Implies(house1_hobby == 0, house1_name == 0))
s.add(Implies(house1_name == 0, house1_hobby == 0))
s.add(Implies(house2_hobby == 0, house2_name == 0))
s.add(Implies(house2_name == 0, house2_hobby == 0))

# Solve the constraints.
if s.check() == sat:
    m = s.model()
    
    # Mapping dictionaries
    name_map = {0: "Arnold", 1: "Eric"}
    sport_map = {0: "basketball", 1: "soccer"}
    hobby_map = {0: "gardening", 1: "photography"}
    
    solution = {
        "solution": {
            "header": ["House", "Name", "FavoriteSport", "Hobby"],
            "rows": [
                [
                    "1",
                    name_map[m[house1_name].as_long()],
                    sport_map[m[house1_sport].as_long()],
                    hobby_map[m[house1_hobby].as_long()]
                ],
                [
                    "2",
                    name_map[m[house2_name].as_long()],
                    sport_map[m[house2_sport].as_long()],
                    hobby_map[m[house2_hobby].as_long()]
                ]
            ]
        }
    }
    print(json.dumps(solution))
else:
    print(json.dumps({"solution": None}))