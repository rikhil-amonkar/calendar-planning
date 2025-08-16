import json
from z3 import *

# Create a solver instance
s = Solver()

# Define the attributes for each house
houses = [1, 2]
names = ['Eric', 'Arnold']
house_styles = ['victorian', 'colonial']
smoothies = ['cherry', 'desert']
pets = ['dog', 'cat']

# Create variables for each attribute in each house
name = {h: String(f'name_{h}') for h in houses}
house_style = {h: String(f'house_style_{h}') for h in houses}
smoothie = {h: String(f'smoothie_{h}') for h in houses}
pet = {h: String(f'pet_{h}') for h in houses}

# Add constraints that each attribute must be one of the allowed values
for h in houses:
    s.add(Or([name[h] == n for n in names]))
    s.add(Or([house_style[h] == hs for hs in house_styles]))
    s.add(Or([smoothie[h] == sm for sm in smoothies]))
    s.add(Or([pet[h] == p for p in pets]))

# Add uniqueness constraints for each attribute across houses
for attr in [name, house_style, smoothie, pet]:
    for h1 in houses:
        for h2 in houses:
            if h1 < h2:
                s.add(attr[h1] != attr[h2])

# Clue 1: The person who likes Cherry smoothies is the person who owns a dog.
for h in houses:
    s.add(Implies(smoothie[h] == 'cherry', pet[h] == 'dog'))

# Clue 2: The person residing in a Victorian house is the person who owns a dog.
for h in houses:
    s.add(Implies(house_style[h] == 'victorian', pet[h] == 'dog'))

# Clue 3: The person residing in a Victorian house is somewhere to the left of Eric.
# This means the Victorian house is to the left of the house where Eric lives.
# So, if house 1 is Victorian, Eric must be in house 2.
# If house 2 is Victorian, this cannot be satisfied because there's no house to its left.
s.add(Or(
    And(house_style[1] == 'victorian', name[2] == 'Eric'),
    And(house_style[2] == 'victorian', name[1] == 'Eric')  # This would violate the "left of" condition
))
# But since house 2 cannot be to the left of Eric (as there's no house to its left), we can simplify:
s.add(And(house_style[1] == 'victorian', name[2] == 'Eric'))

# Check if the solver can find a solution
if s.check() == sat:
    model = s.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "Smoothie", "Pet"],
            "rows": []
        }
    }
    for h in sorted(houses):
        row = [
            str(h),
            str(model.eval(name[h])),
            str(model.eval(house_style[h])),
            str(model.eval(smoothie[h])),
            str(model.eval(pet[h]))
        ]
        solution["solution"]["rows"].append(row)
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")