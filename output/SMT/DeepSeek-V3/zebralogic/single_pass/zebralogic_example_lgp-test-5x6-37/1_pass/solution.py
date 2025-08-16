from z3 import *

# Create the solver
s = Solver()

# Define the houses
houses = [1, 2, 3, 4, 5]

# Define the attributes
names = ["Bob", "Arnold", "Alice", "Peter", "Eric"]
hobbies = ["cooking", "gardening", "painting", "photography", "knitting"]
sports = ["swimming", "tennis", "soccer", "baseball", "basketball"]
house_styles = ["ranch", "craftsman", "victorian", "modern", "colonial"]
children = ["Timothy", "Samantha", "Bella", "Meredith", "Fred"]
heights = ["average", "very tall", "very short", "short", "tall"]

# Create variables for each attribute in each house
name = {h: String(f"name_{h}") for h in houses}
hobby = {h: String(f"hobby_{h}") for h in houses}
sport = {h: String(f"sport_{h}") for h in houses}
house_style = {h: String(f"house_style_{h}") for h in houses}
child = {h: String(f"child_{h}") for h in houses}
height = {h: String(f"height_{h}") for h in houses}

# Add constraints that each attribute is unique within its category
for h in houses:
    s.add(Or([name[h] == n for n in names]))
    s.add(Or([hobby[h] == ho for ho in hobbies]))
    s.add(Or([sport[h] == sp for sp in sports]))
    s.add(Or([house_style[h] == hs for hs in house_styles]))
    s.add(Or([child[h] == c for c in children]))
    s.add(Or([height[h] == he for he in heights]))

for attr in [name, hobby, sport, house_style, child, height]:
    for h1 in houses:
        for h2 in houses:
            if h1 < h2:
                s.add(attr[h1] != attr[h2])

# Add constraints based on the clues

# Clue 2: The person who is tall is in the second house.
s.add(height[2] == "tall")

# Clue 4: Alice is the person who is tall.
s.add(name[2] == "Alice")

# Clue 16: Peter is the person who is very tall.
# From clue 5: The person who loves baseball is the person who is very tall.
# So Peter loves baseball and is very tall.
for h in houses:
    s.add(Implies(name[h] == "Peter", And(height[h] == "very tall", sport[h] == "baseball")))

# Clue 3: Peter is directly left of the person residing in a Victorian house.
# So Peter is in house h, Victorian is in h+1.
for h in [1, 2, 3, 4]:
    s.add(Implies(name[h] == "Peter", house_style[h+1] == "victorian"))

# Clue 20: The person residing in a Victorian house is in the fifth house.
s.add(house_style[5] == "victorian")

# From clue 3 and 20, Peter must be in house 4.
s.add(name[4] == "Peter")

# From clue 14: The person's child is named Fred is the person residing in a Victorian house.
s.add(child[5] == "Fred")

# From clue 13: The person in a Craftsman-style house is the person who has an average height.
for h in houses:
    s.add(Implies(house_style[h] == "craftsman", height[h] == "average"))

# From clue 1: The person who has an average height is the person's child is named Meredith.
for h in houses:
    s.add(Implies(height[h] == "average", child[h] == "Meredith"))

# From clue 6: The person's child is named Meredith and the person who is the mother of Timothy are next to each other.
# So if house h has child Meredith, then house h-1 or h+1 has child Timothy, and vice versa.
for h in houses:
    s.add(Implies(child[h] == "Meredith", 
                  Or(And(h > 1, child[h-1] == "Timothy"), 
                     And(h < 5, child[h+1] == "Timothy"))))
    s.add(Implies(child[h] == "Timothy", 
                  Or(And(h > 1, child[h-1] == "Meredith"), 
                     And(h < 5, child[h+1] == "Meredith"))))

# From clue 7: Bob is the person who paints as a hobby.
for h in houses:
    s.add(Implies(name[h] == "Bob", hobby[h] == "painting"))

# From clue 8: The person who enjoys gardening is in the second house.
s.add(hobby[2] == "gardening")

# From clue 18: The person who enjoys knitting and the person who enjoys gardening are next to each other.
# Gardening is in house 2, so knitting is in house 1 or 3.
s.add(Or(hobby[1] == "knitting", hobby[3] == "knitting"))

# From clue 19: The person in a modern-style house is the person who loves cooking.
for h in houses:
    s.add(Implies(house_style[h] == "modern", hobby[h] == "cooking"))

# From clue 17: The person in a ranch-style home is somewhere to the left of the person who loves cooking.
# So ranch is in h, cooking is in h', h < h'.
# Cooking is in modern house, so find modern house.
# So ranch is left of modern.
for h in houses:
    for h2 in houses:
        if h < h2:
            s.add(Implies(And(house_style[h] == "ranch", hobby[h2] == "cooking"), h < h2))

# From clue 12: The person's child is named Samantha is the person in a modern-style house.
for h in houses:
    s.add(Implies(child[h] == "Samantha", house_style[h] == "modern"))

# From clue 10: The person who loves tennis is the person's child is named Samantha.
for h in houses:
    s.add(Implies(sport[h] == "tennis", child[h] == "Samantha"))

# From clue 11: The person who loves soccer is not in the first house.
s.add(sport[1] != "soccer")

# From clue 15: The person who is short is the person who loves basketball.
for h in houses:
    s.add(Implies(height[h] == "short", sport[h] == "basketball"))

# From clue 9: The person who is very short is somewhere to the right of Eric.
# So Eric is in h, very short is in h', h < h'.
for h in houses:
    for h2 in houses:
        if h < h2:
            s.add(Implies(And(name[h] == "Eric", height[h2] == "very short"), h < h2))

# Solve the problem
if s.check() == sat:
    m = s.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Hobby", "FavoriteSport", "HouseStyle", "Children", "Height"],
            "rows": []
        }
    }
    for h in sorted(houses):
        row = [
            str(h),
            m.eval(name[h]).as_string(),
            m.eval(hobby[h]).as_string(),
            m.eval(sport[h]).as_string(),
            m.eval(house_style[h]).as_string(),
            m.eval(child[h]).as_string(),
            m.eval(height[h]).as_string()
        ]
        solution["solution"]["rows"].append(row)
    print(solution)
else:
    print("No solution found")