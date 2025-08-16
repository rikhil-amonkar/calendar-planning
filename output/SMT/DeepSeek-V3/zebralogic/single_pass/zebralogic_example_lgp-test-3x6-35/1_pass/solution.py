import json
from z3 import *

# Create the solver
s = Solver()

# Define the houses
houses = [1, 2, 3]

# Define the attributes
names = ["Eric", "Arnold", "Peter"]
vacations = ["mountain", "city", "beach"]
heights = ["very short", "short", "average"]
flowers = ["carnations", "daffodils", "lilies"]
hair_colors = ["brown", "black", "blonde"]
educations = ["associate", "bachelor", "high school"]

# Create variables for each attribute in each house
name = {h: String(f"name_{h}") for h in houses}
vacation = {h: String(f"vacation_{h}") for h in houses}
height = {h: String(f"height_{h}") for h in houses}
flower = {h: String(f"flower_{h}") for h in houses}
hair_color = {h: String(f"hair_color_{h}") for h in houses}
education = {h: String(f"education_{h}") for h in houses}

# Add constraints that each attribute is one of the possible values
for h in houses:
    s.add(Or([name[h] == n for n in names]))
    s.add(Or([vacation[h] == v for v in vacations]))
    s.add(Or([height[h] == ht for ht in heights]))
    s.add(Or([flower[h] == f for f in flowers]))
    s.add(Or([hair_color[h] == hc for hc in hair_colors]))
    s.add(Or([education[h] == e for e in educations]))

# Add uniqueness constraints for each attribute across houses
for attr in [name, vacation, height, flower, hair_color, education]:
    for h1 in houses:
        for h2 in houses:
            if h1 < h2:
                s.add(attr[h1] != attr[h2])

# Apply the clues one by one
# Clue 1: Peter is the person who has an average height.
for h in houses:
    s.add(Implies(name[h] == "Peter", height[h] == "average"))

# Clue 2: The person who loves a bouquet of daffodils is Arnold.
for h in houses:
    s.add(Implies(flower[h] == "daffodils", name[h] == "Arnold"))

# Clue 3: The person who is very short is not in the second house.
s.add(height[2] != "very short")

# Clue 4: The person who loves beach vacations is in the first house.
s.add(vacation[1] == "beach")

# Clue 5: The person with a high school diploma is in the third house.
s.add(education[3] == "high school")

# Clue 6: The person who is short is somewhere to the right of the person who is very short.
# This means very short must be in house 1 and short in house 2 or 3, or very short in 2 and short in 3
s.add(Or(
    And(height[1] == "very short", Or(height[2] == "short", height[3] == "short")),
    And(height[2] == "very short", height[3] == "short")
))

# Clue 7: The person who loves the bouquet of lilies is Eric.
for h in houses:
    s.add(Implies(flower[h] == "lilies", name[h] == "Eric"))

# Clue 8: The person who loves the bouquet of lilies is the person with a bachelor's degree.
for h in houses:
    s.add(Implies(flower[h] == "lilies", education[h] == "bachelor"))

# Clue 9: The person who prefers city breaks is somewhere to the right of Peter.
# This means Peter must be to the left of the city vacation person
for h_peter in houses:
    for h_city in houses:
        if h_city > h_peter:
            s.add(Implies(name[h_peter] == "Peter", vacation[h_city] == "city"))

# Clue 10: The person who has blonde hair is in the third house.
s.add(hair_color[3] == "blonde")

# Clue 11: The person who loves beach vacations is the person who has brown hair.
s.add(hair_color[1] == "brown")  # because beach is in house 1 (from clue 4)

# Solve the problem
if s.check() == sat:
    model = s.model()
    
    # Prepare the solution
    solution = {
        "solution": {
            "header": ["House", "Name", "Vacation", "Height", "Flower", "HairColor", "Education"],
            "rows": []
        }
    }
    
    for h in sorted(houses):
        row = [
            str(h),
            str(model.eval(name[h])),
            str(model.eval(vacation[h])),
            str(model.eval(height[h])),
            str(model.eval(flower[h])),
            str(model.eval(hair_color[h])),
            str(model.eval(education[h]))
        ]
        solution["solution"]["rows"].append(row)
    
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")