import json
from z3 import *

# Create a solver instance
s = Solver()

# Define the houses
houses = [1, 2, 3, 4, 5]

# Define the attributes
names = ["Alice", "Peter", "Bob", "Eric", "Arnold"]
heights = ["very short", "short", "tall", "average", "very tall"]
mothers = ["Janelle", "Kailyn", "Penny", "Holly", "Aniya"]
hair_colors = ["blonde", "black", "gray", "red", "brown"]

# Create variables for each attribute in each house
name = {h: Int(f"name_{h}") for h in houses}
height = {h: Int(f"height_{h}") for h in houses}
mother = {h: Int(f"mother_{h}") for h in houses}
hair_color = {h: Int(f"hair_color_{h}") for h in houses}

# Add constraints to ensure each attribute is within the valid range
for h in houses:
    s.add(name[h] >= 0, name[h] < len(names))
    s.add(height[h] >= 0, height[h] < len(heights))
    s.add(mother[h] >= 0, mother[h] < len(mothers))
    s.add(hair_color[h] >= 0, hair_color[h] < len(hair_colors))

# Ensure all attributes in each category are unique across houses
s.add(Distinct([name[h] for h in houses]))
s.add(Distinct([height[h] for h in houses]))
s.add(Distinct([mother[h] for h in houses]))
s.add(Distinct([hair_color[h] for h in houses]))

# Clue 8: Bob is in the fifth house.
s.add(name[5] == names.index("Bob"))

# Clue 5: Eric is the person who has black hair.
s.add(Or([And(name[h] == names.index("Eric"), hair_color[h] == hair_colors.index("black")) for h in houses]))

# Clue 4: The person who has black hair is not in the fourth house.
s.add(hair_color[4] != hair_colors.index("black"))

# Clue 7: Eric and the person who has gray hair are next to each other.
for h in houses:
    if h > 1:
        s.add(Implies(name[h] == names.index("Eric"), Or(hair_color[h-1] == hair_colors.index("gray"), 
                                                         (h < 5 and hair_color[h+1] == hair_colors.index("gray")))))
    if h < 5:
        s.add(Implies(name[h+1] == names.index("Eric"), hair_color[h] == hair_colors.index("gray")))
        s.add(Implies(name[h] == names.index("Eric"), hair_color[h+1] == hair_colors.index("gray")))

# Clue 3: The person who has gray hair is directly left of the person whose mother's name is Janelle.
for h in houses:
    if h < 5:
        s.add(Implies(hair_color[h] == hair_colors.index("gray"), mother[h+1] == mothers.index("Janelle")))

# Clue 12: The person who has brown hair is somewhere to the left of the person whose mother's name is Janelle.
for h in houses:
    for h2 in houses:
        if h2 > h:
            s.add(Implies(hair_color[h] == hair_colors.index("brown"), mother[h2] == mothers.index("Janelle")))

# Clue 11: Arnold is the person who has brown hair.
s.add(Or([And(name[h] == names.index("Arnold"), hair_color[h] == hair_colors.index("brown")) for h in houses]))

# Clue 9: The person who has red hair is Peter.
s.add(Or([And(name[h] == names.index("Peter"), hair_color[h] == hair_colors.index("red")) for h in houses]))

# Clue 14: The person whose mother's name is Kailyn is in the third house.
s.add(mother[3] == mothers.index("Kailyn"))

# Clue 10: The person whose mother's name is Kailyn is directly left of the person who is short.
s.add(height[4] == heights.index("short"))

# Clue 2: There are two houses between the person who has an average height and the person who is short.
# Since the person who is short is in house 4, the person with average height must be in house 1.
s.add(height[1] == heights.index("average"))

# Clue 6: The person who is very short is the person whose mother's name is Penny.
s.add(Or([And(height[h] == heights.index("very short"), mother[h] == mothers.index("Penny")) for h in houses]))

# Clue 13: The person whose mother's name is Aniya and the person who is very short are next to each other.
for h in houses:
    if h > 1:
        s.add(Implies(mother[h] == mothers.index("Aniya"), 
                      Or(height[h-1] == heights.index("very short"), 
                         (h < 5 and height[h+1] == heights.index("very short")))))
    if h < 5:
        s.add(Implies(mother[h+1] == mothers.index("Aniya"), height[h] == heights.index("very short")))
        s.add(Implies(mother[h] == mothers.index("Aniya"), height[h+1] == heights.index("very short")))

# Clue 1: The person who is tall is the person whose mother's name is Holly.
s.add(Or([And(height[h] == heights.index("tall"), mother[h] == mothers.index("Holly")) for h in houses]))

# Solve the constraints
if s.check() == sat:
    m = s.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Height", "Mother", "HairColor"],
            "rows": []
        }
    }
    for h in houses:
        row = [
            str(h),
            names[m.evaluate(name[h]).as_long()],
            heights[m.evaluate(height[h]).as_long()],
            mothers[m.evaluate(mother[h]).as_long()],
            hair_colors[m.evaluate(hair_color[h]).as_long()]
        ]
        solution["solution"]["rows"].append(row)
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")