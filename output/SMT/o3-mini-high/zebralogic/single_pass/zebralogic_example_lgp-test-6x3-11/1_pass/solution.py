from z3 import *
import json

# We use the following integer encodings:
# Names: 0 = Bob, 1 = Peter, 2 = Eric, 3 = Alice, 4 = Arnold, 5 = Carol
# Hair Colors: 0 = auburn, 1 = blonde, 2 = brown, 3 = black, 4 = red, 5 = gray
# Heights: 0 = very tall, 1 = average, 2 = very short, 3 = tall, 4 = super tall, 5 = short

num_houses = 6
name_vars = [Int(f"name_{i}") for i in range(num_houses)]
hair_vars = [Int(f"hair_{i}") for i in range(num_houses)]
height_vars = [Int(f"height_{i}") for i in range(num_houses)]

s = Solver()

# Each attribute is one of 0..5 and all houses have different values per category.
for i in range(num_houses):
    s.add(And(name_vars[i] >= 0, name_vars[i] <= 5))
    s.add(And(hair_vars[i] >= 0, hair_vars[i] <= 5))
    s.add(And(height_vars[i] >= 0, height_vars[i] <= 5))
    
s.add(Distinct(name_vars))
s.add(Distinct(hair_vars))
s.add(Distinct(height_vars))

# Clue 2: Alice is in the fourth house.
s.add(name_vars[3] == 3)  # House 4 (index 3) is Alice.

# Clue 10: The person who is very short is in the fifth house.
s.add(height_vars[4] == 2)  # very short = 2, House 5 (index 4).

# Clue 4: The person who is tall is in the sixth house.
s.add(height_vars[5] == 3)  # tall = 3, House 6 (index 5).

# Clue 12: The person who has gray hair is in the third house.
s.add(hair_vars[2] == 5)  # gray = 5, House 3 (index 2).

# Clue 1: The person who has blonde hair is directly left of Bob.
# That is: for any house i (except the last) if its hair = blonde (1) then house i+1’s name = Bob (0).
for i in range(num_houses - 1):
    s.add(Implies(hair_vars[i] == 1, name_vars[i+1] == 0))
# Also, the last house cannot have blonde hair.
s.add(hair_vars[5] != 1)

# Clue 8: The person who has blonde hair is Carol.
# We enforce that if a house has blonde hair then the occupant is Carol (5), and vice versa.
for i in range(num_houses):
    s.add(Implies(hair_vars[i] == 1, name_vars[i] == 5))
    s.add(Implies(name_vars[i] == 5, hair_vars[i] == 1))

# Clue 11: Bob is the person who has brown hair.
# (Brown = 2, Bob = 0)
for i in range(num_houses):
    s.add(Implies(name_vars[i] == 0, hair_vars[i] == 2))

# Clue 6: The person who has red hair is Eric.
# (Red = 4, Eric = 2)
for i in range(num_houses):
    s.add(Implies(hair_vars[i] == 4, name_vars[i] == 2))
    s.add(Implies(name_vars[i] == 2, hair_vars[i] == 4))

# Clue 5: The person who has black hair is not in the fourth house.
# (Black = 3, so House 4 (index 3) cannot have hair 3.)
s.add(hair_vars[3] != 3)

# Clue 7: The person who is super tall is somewhere to the right of the person who has an average height.
# (Average = 1, Super tall = 4. We ensure that the index of the house with average height is less than that with super tall.)
pos_avg = Sum([If(height_vars[i] == 1, i, 0) for i in range(num_houses)])
pos_super = Sum([If(height_vars[i] == 4, i, 0) for i in range(num_houses)])
s.add(pos_avg < pos_super)

# Clue 3: The person who is short is Arnold.
# (Short = 5, Arnold = 4)
for i in range(num_houses):
    s.add(Implies(name_vars[i] == 4, height_vars[i] == 5))
    s.add(Implies(height_vars[i] == 5, name_vars[i] == 4))

# Clue 13: The person who has blonde hair is the person who is very tall.
# (Very tall = 0, blonde = 1)
for i in range(num_houses):
    s.add(Implies(hair_vars[i] == 1, height_vars[i] == 0))
    s.add(Implies(height_vars[i] == 0, hair_vars[i] == 1))

# Clue 9: There is one house between the person who has gray hair and the person who has red hair.
# Gray hair is fixed in House 3 (index 2). For a one-house gap, red hair (4) must be in either house1 or house5.
# House 1 (index 0) would be too far left given other clues, so we force red hair into the fifth house.
s.add(hair_vars[4] == 4)  # House 5 (index 4): red hair.

# At this point, the only remaining assignments (by the distinct constraints and the implications)
# should force the unique solution:
# House1 (index 0): Carol, blonde, very tall.
# House2 (index 1): Bob, brown, average.
# House3 (index 2): Arnold, gray, short.
# House4 (index 3): Alice, auburn, super tall.
# House5 (index 4): Eric, red, very short.
# House6 (index 5): Peter, black, tall.

if s.check() == sat:
    m = s.model()
    # Reverse mappings to print the solution in plain text.
    names = {0: "Bob", 1: "Peter", 2: "Eric", 3: "Alice", 4: "Arnold", 5: "Carol"}
    hairs = {0: "auburn", 1: "blonde", 2: "brown", 3: "black", 4: "red", 5: "gray"}
    heights = {0: "very tall", 1: "average", 2: "very short", 3: "tall", 4: "super tall", 5: "short"}
    
    solution = {"solution": {"header": ["House", "Name", "HairColor", "Height"], "rows": []}}
    
    for i in range(num_houses):
        house_num = str(i+1)  # Houses numbered 1 to 6.
        n = m[name_vars[i]].as_long()
        h = m[hair_vars[i]].as_long()
        t = m[height_vars[i]].as_long()
        solution["solution"]["rows"].append([house_num, names[n], hairs[h], heights[t]])
    
    # Output the solution as valid JSON.
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")