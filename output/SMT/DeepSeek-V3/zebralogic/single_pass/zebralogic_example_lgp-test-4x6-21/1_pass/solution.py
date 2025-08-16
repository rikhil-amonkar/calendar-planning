import json
from z3 import *

# Initialize the solver
s = Solver()

# Define the attributes
houses = [1, 2, 3, 4]
names = ["Peter", "Arnold", "Alice", "Eric"]
flowers = ["roses", "daffodils", "carnations", "lilies"]
hobbies = ["photography", "painting", "cooking", "gardening"]
pets = ["dog", "fish", "bird", "cat"]
colors = ["red", "yellow", "green", "white"]
house_styles = ["craftsman", "colonial", "ranch", "victorian"]

# Create variables for each attribute in each house
name = {house: String(f"name_{house}") for house in houses}
flower = {house: String(f"flower_{house}") for house in houses}
hobby = {house: String(f"hobby_{house}") for house in houses}
pet = {house: String(f"pet_{house}") for house in houses}
color = {house: String(f"color_{house}") for house in houses}
house_style = {house: String(f"house_style_{house}") for house in houses}

# Add constraints that each attribute in each house is one of the possible values
for house in houses:
    s.add(Or([name[house] == n for n in names]))
    s.add(Or([flower[house] == f for f in flowers]))
    s.add(Or([hobby[house] == h for h in hobbies]))
    s.add(Or([pet[house] == p for p in pets]))
    s.add(Or([color[house] == c for c in colors]))
    s.add(Or([house_style[house] == hs for hs in house_styles]))

# Add uniqueness constraints for each attribute across houses
for attr in [name, flower, hobby, pet, color, house_style]:
    for i in houses:
        for j in houses:
            if i < j:
                s.add(attr[i] != attr[j])

# Clue 6: The person in a Craftsman-style house is in the second house.
s.add(house_style[2] == "craftsman")

# Clue 1: The person in a Craftsman-style house is Arnold.
s.add(name[2] == "Arnold")

# Clue 7: Eric is the person residing in a Victorian house.
for house in houses:
    s.add(Implies(name[house] == "Eric", house_style[house] == "victorian"))

# Clue 14: The person who has a cat is Eric.
for house in houses:
    s.add(Implies(pet[house] == "cat", name[house] == "Eric"))

# Clue 5: The person who loves the rose bouquet is the person whose favorite color is red.
for house in houses:
    s.add(Implies(flower[house] == "roses", color[house] == "red"))

# Clue 13: The person living in a colonial-style house is the person whose favorite color is red.
for house in houses:
    s.add(Implies(house_style[house] == "colonial", color[house] == "red"))

# Clue 2: The person who loves the rose bouquet is somewhere to the right of Peter.
# Peter is to the left of the house with roses.
# So, for all houses i, if name[i] is Peter, then there exists a house j > i where flower[j] is roses.
# This is a bit tricky, but we can model it as:
# There exists a house j where flower[j] is roses, and for any house i where name[i] is Peter, i < j.
# So, first find Peter's house, then ensure that roses are in a house to its right.
# Alternatively, for all i, if name[i] is Peter, then for some j > i, flower[j] is roses.
# But Z3 doesn't have existential quantifiers directly in the solver, so we can use Or over possible positions.
# So, for each possible house of Peter, the roses are in a house to the right.
# For example, if Peter is in 1, roses are in 2,3, or 4.
# If Peter is in 2, roses are in 3 or 4, etc.
# So, for each house i, if name[i] is Peter, then Or(flower[i+1] == "roses", flower[i+2] == "roses", ...)
for i in houses:
    for j in houses:
        if j > i:
            s.add(Implies(name[i] == "Peter", Or(flower[j] == "roses")))

# Clue 4: The person who loves a bouquet of daffodils is not in the fourth house.
s.add(flower[4] != "daffodils")

# Clue 12: The person who loves a bouquet of daffodils is the person who loves yellow.
for house in houses:
    s.add(Implies(flower[house] == "daffodils", color[house] == "yellow"))

# Clue 3: The photography enthusiast is the person who owns a dog.
for house in houses:
    s.add(Implies(hobby[house] == "photography", pet[house] == "dog"))

# Clue 8: The person with an aquarium of fish is the person who loves white.
for house in houses:
    s.add(Implies(pet[house] == "fish", color[house] == "white"))

# Clue 10: The person who loves white is the person who loves a carnations arrangement.
for house in houses:
    s.add(Implies(color[house] == "white", flower[house] == "carnations"))

# Clue 11: The person who loves white is somewhere to the right of the person who enjoys gardening.
# So, the gardening hobby is in a house left of any house with white color.
# For all houses i, if color[i] is white, then there exists a house j < i where hobby[j] is gardening.
# Similar to clue 2, we can model this as:
# For each house i, if color[i] is white, then Or(hobby[1] == "gardening" and 1 < i, hobby[2] == "gardening" and 2 < i, etc.)
for i in houses:
    for j in houses:
        if j < i:
            s.add(Implies(color[i] == "white", Or(hobby[j] == "gardening")))

# Clue 9: The person who loves cooking is somewhere to the right of the person whose favorite color is red.
# So, the house with cooking is to the right of the house with color red.
# For all houses i, if color[i] is red, then for some j > i, hobby[j] is cooking.
for i in houses:
    for j in houses:
        if j > i:
            s.add(Implies(color[i] == "red", Or(hobby[j] == "cooking")))

# Solve the constraints
if s.check() == sat:
    model = s.model()
    
    # Prepare the solution
    solution = {
        "solution": {
            "header": ["House", "Name", "Flower", "Hobby", "Pet", "Color", "HouseStyle"],
            "rows": []
        }
    }
    
    for house in houses:
        row = [str(house)]
        # Retrieve each attribute's value from the model
        n = model.eval(name[house])
        f = model.eval(flower[house])
        h = model.eval(hobby[house])
        p = model.eval(pet[house])
        c = model.eval(color[house])
        hs = model.eval(house_style[house])
        
        # Convert Z3 string expressions to Python strings
        row.append(str(n))
        row.append(str(f))
        row.append(str(h))
        row.append(str(p))
        row.append(str(c))
        row.append(str(hs))
        
        solution["solution"]["rows"].append(row)
    
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")