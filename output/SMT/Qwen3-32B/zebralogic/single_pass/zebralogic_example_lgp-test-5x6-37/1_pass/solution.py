from z3 import *
import json

# Define variables for each house (0-4)
name_vars = [Int(f"name_{i}") for i in range(5)]
hobby_vars = [Int(f"hobby_{i}") for i in range(5)]
sport_vars = [Int(f"sport_{i}") for i in range(5)]
style_vars = [Int(f"style_{i}") for i in range(5)]
child_vars = [Int(f"child_{i}") for i in range(5)]
height_vars = [Int(f"height_{i}") for i in range(5)]

s = Solver()

# Add basic constraints for each attribute: 0-4 and distinct
for vars_list in [name_vars, hobby_vars, sport_vars, style_vars, child_vars, height_vars]:
    for v in vars_list:
        s.add(And(0 <= v, v <= 4))
    s.add(Distinct(vars_list))

# Clue 1: average height (0) has child Meredith (3)
for i in range(5):
    s.add(Implies(height_vars[i] == 0, child_vars[i] == 3))

# Clue 2: house 2 (i=1) has height 4 (tall)
s.add(height_vars[1] == 4)

# Clue 3: Peter (3) is directly left of Victorian (2)
clue3 = Or(
    And(name_vars[0] == 3, style_vars[1] == 2),
    And(name_vars[1] == 3, style_vars[2] == 2),
    And(name_vars[2] == 3, style_vars[3] == 2),
    And(name_vars[3] == 3, style_vars[4] == 2)
)
s.add(clue3)

# Clue 4: Alice (2) has height 4
for i in range(5):
    s.add(Implies(name_vars[i] == 2, height_vars[i] == 4))

# Clue 5: baseball (3) implies very tall (1)
for i in range(5):
    s.add(Implies(sport_vars[i] == 3, height_vars[i] == 1))

# Clue 6: Meredith (3) and Timothy (0) are adjacent
clue6 = Or(
    And(child_vars[0] == 3, child_vars[1] == 0),
    And(child_vars[1] == 3, child_vars[2] == 0),
    And(child_vars[2] == 3, child_vars[3] == 0),
    And(child_vars[3] == 3, child_vars[4] == 0),
    And(child_vars[0] == 0, child_vars[1] == 3),
    And(child_vars[1] == 0, child_vars[2] == 3),
    And(child_vars[2] == 0, child_vars[3] == 3),
    And(child_vars[3] == 0, child_vars[4] == 3)
)
s.add(clue6)

# Clue 7: Bob (0) has hobby painting (2)
for i in range(5):
    s.add(Implies(name_vars[i] == 0, hobby_vars[i] == 2))

# Clue 8: house 2 (i=1) has hobby gardening (1)
s.add(hobby_vars[1] == 1)

# Clue 9: very short (2) is to the right of Eric (4)
for i in range(5):
    s.add(Implies(name_vars[i] == 4, Or(*[height_vars[j] == 2 for j in range(i+1, 5)])))

# Clue 10: tennis (1) implies child Samantha (1)
for i in range(5):
    s.add(Implies(sport_vars[i] == 1, child_vars[i] == 1))

# Clue 11: first house (i=0) not soccer (2)
s.add(sport_vars[0] != 2)

# Clue 12: child Samantha (1) implies style modern (3)
for i in range(5):
    s.add(Implies(child_vars[i] == 1, style_vars[i] == 3))

# Clue 13: craftsman (1) implies average height (0)
for i in range(5):
    s.add(Implies(style_vars[i] == 1, height_vars[i] == 0))

# Clue 14: child Fred (4) implies style victorian (2)
for i in range(5):
    s.add(Implies(child_vars[i] == 4, style_vars[i] == 2))

# Clue 15: short (3) implies basketball (4)
for i in range(5):
    s.add(Implies(height_vars[i] == 3, sport_vars[i] == 4))

# Clue 16: Peter (3) has very tall (1)
for i in range(5):
    s.add(Implies(name_vars[i] == 3, height_vars[i] == 1))

# Clue 17: ranch (0) is left of cooking (0)
clue17 = Or(
    And(style_vars[0] == 0, hobby_vars[1] == 0),
    And(style_vars[0] == 0, hobby_vars[2] == 0),
    And(style_vars[0] == 0, hobby_vars[3] == 0),
    And(style_vars[0] == 0, hobby_vars[4] == 0),
    And(style_vars[1] == 0, hobby_vars[2] == 0),
    And(style_vars[1] == 0, hobby_vars[3] == 0),
    And(style_vars[1] == 0, hobby_vars[4] == 0),
    And(style_vars[2] == 0, hobby_vars[3] == 0),
    And(style_vars[2] == 0, hobby_vars[4] == 0),
    And(style_vars[3] == 0, hobby_vars[4] == 0)
)
s.add(clue17)

# Clue 18: knitting (4) and gardening (1) adjacent
clue18 = Or(
    And(hobby_vars[0] == 4, hobby_vars[1] == 1),
    And(hobby_vars[1] == 4, hobby_vars[2] == 1),
    And(hobby_vars[2] == 4, hobby_vars[3] == 1),
    And(hobby_vars[3] == 4, hobby_vars[4] == 1),
    And(hobby_vars[0] == 1, hobby_vars[1] == 4),
    And(hobby_vars[1] == 1, hobby_vars[2] == 4),
    And(hobby_vars[2] == 1, hobby_vars[3] == 4),
    And(hobby_vars[3] == 1, hobby_vars[4] == 4)
)
s.add(clue18)

# Clue 19: modern (3) implies cooking (0)
for i in range(5):
    s.add(Implies(style_vars[i] == 3, hobby_vars[i] == 0))

# Clue 20: style victorian (2) in house 5 (i=4)
s.add(style_vars[4] == 2)

# Check if the solver can find a solution
if s.check() == sat:
    model = s.model()
    # Now extract the data
    names_list = ["Bob", "Arnold", "Alice", "Peter", "Eric"]
    hobbies_list = ["cooking", "gardening", "painting", "photography", "knitting"]
    sports_list = ["swimming", "tennis", "soccer", "baseball", "basketball"]
    styles_list = ["ranch", "craftsman", "victorian", "modern", "colonial"]
    children_list = ["Timothy", "Samantha", "Bella", "Meredith", "Fred"]
    heights_list = ["average", "very tall", "very short", "short", "tall"]
    
    rows = []
    for i in range(5):
        house_num = str(i+1)
        name = names_list[model[name_vars[i]].as_long()]
        hobby = hobbies_list[model[hobby_vars[i]].as_long()]
        sport = sports_list[model[sport_vars[i]].as_long()]
        style = styles_list[model[style_vars[i]].as_long()]
        child = children_list[model[child_vars[i]].as_long()]
        height = heights_list[model[height_vars[i]].as_long()]
        rows.append([house_num, name, hobby, sport, style, child, height])
    
    solution = {
        "solution": {
            "header": ["House", "Name", "Hobby", "FavoriteSport", "HouseStyle", "Children", "Height"],
            "rows": rows
        }
    }
    
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")