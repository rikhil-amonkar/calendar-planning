from z3 import *

# Create the solver
solver = Solver()

# For easier reading, we will represent:
# Names: 0 = Arnold, 1 = Eric
# Hair colors: 0 = black, 1 = brown
# Favorite sports: 0 = basketball, 1 = soccer
# Smoothies: 0 = desert, 1 = cherry

# Create integer variables for House 1
name1 = Int('name1')
hair1 = Int('hair1')
sport1 = Int('sport1')
smoothie1 = Int('smoothie1')

# Create integer variables for House 2
name2 = Int('name2')
hair2 = Int('hair2')
sport2 = Int('sport2')
smoothie2 = Int('smoothie2')

# Each variable can only be 0 or 1
variables = [name1, hair1, sport1, smoothie1, name2, hair2, sport2, smoothie2]
for var in variables:
    solver.add(Or(var == 0, var == 1))

# Each category must have distinct values across houses.
solver.add(Distinct(name1, name2))
solver.add(Distinct(hair1, hair2))
solver.add(Distinct(sport1, sport2))
solver.add(Distinct(smoothie1, smoothie2))

# Clue 1: "The Desert smoothie lover is Arnold."
# This tells us that the person who drinks the desert smoothie is Arnold.
# In our encoding: desert = 0 and Arnold = 0.
# Enforce equivalence for each house.
solver.add(Implies(smoothie1 == 0, name1 == 0))
solver.add(Implies(name1 == 0, smoothie1 == 0))
solver.add(Implies(smoothie2 == 0, name2 == 0))
solver.add(Implies(name2 == 0, smoothie2 == 0))

# Clue 2: "The person who has brown hair is the person who loves basketball."
# We encode brown hair as 1 and basketball as 0.
# Enforce that in a house, having brown hair means the sport is basketball and vice versa.
solver.add(Implies(hair1 == 1, sport1 == 0))
solver.add(Implies(sport1 == 0, hair1 == 1))
solver.add(Implies(hair2 == 1, sport2 == 0))
solver.add(Implies(sport2 == 0, hair2 == 1))

# Clue 3: "Arnold is somewhere to the left of the person who has black hair."
# With houses numbered 1 (left) and 2 (right), this forces Arnold to be in House 1,
# and the person with black hair (black = 0) to be in House 2.
solver.add(name1 == 0)   # Arnold must be in House 1.
solver.add(hair2 == 0)   # House 2 must have black hair.

# Check for solution
if solver.check() == sat:
    model = solver.model()

    # Helper functions to decode our encoding back to strings
    def decode_name(val):
        return "Arnold" if val == 0 else "Eric"

    def decode_hair(val):
        return "black" if val == 0 else "brown"

    def decode_sport(val):
        return "basketball" if val == 0 else "soccer"

    def decode_smoothie(val):
        return "desert" if val == 0 else "cherry"

    # Build the solution in the required format.
    solution = {
        "solution": {
            "header": ["House", "Name", "HairColor", "FavoriteSport", "Smoothie"],
            "rows": [
                ["1", 
                 decode_name(model[name1].as_long()), 
                 decode_hair(model[hair1].as_long()), 
                 decode_sport(model[sport1].as_long()), 
                 decode_smoothie(model[smoothie1].as_long())
                ],
                ["2", 
                 decode_name(model[name2].as_long()), 
                 decode_hair(model[hair2].as_long()), 
                 decode_sport(model[sport2].as_long()), 
                 decode_smoothie(model[smoothie2].as_long())
                ]
            ]
        }
    }

    import json
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")