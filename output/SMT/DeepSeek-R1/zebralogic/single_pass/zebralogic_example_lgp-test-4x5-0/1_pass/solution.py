from z3 import *

# Create the solver
s = Solver()

# Define the attributes for 4 houses (0-indexed: house0=1, house1=2, house2=3, house3=4)
names = [Int('n0'), Int('n1'), Int('n2'), Int('n3')]
smoothies = [Int('s0'), Int('s1'), Int('s2'), Int('s3')]
cigars = [Int('c0'), Int('c1'), Int('c2'), Int('c3')]
heights = [Int('h0'), Int('h1'), Int('h2'), Int('h3')]
phones = [Int('p0'), Int('p1'), Int('p2'), Int('p3')]

# All attributes must be between 0 and 3
for lst in [names, smoothies, cigars, heights, phones]:
    for x in lst:
        s.add(x >= 0, x <= 3)
    s.add(Distinct(lst))

# Clue 1: Dragonfruit smoothie lover is Eric (smoothie 0 -> name 0)
for i in range(4):
    s.add(Implies(smoothies[i] == 0, names[i] == 0))

# Clue 2: Dunhill smoker (cigar=2) is the cherry smoothie lover (smoothie=1)
for i in range(4):
    s.add((cigars[i] == 2) == (smoothies[i] == 1))

# Clue 3: Samsung Galaxy S21 (phone=1) directly left of iPhone 13 (phone=2)
s.add(Or(
    And(phones[0] == 1, phones[1] == 2),
    And(phones[1] == 1, phones[2] == 2),
    And(phones[2] == 1, phones[3] == 2)
))

# Clue 4: Dunhill smoker (cigar=2) is to the right of very short person (height=3)
# First, very short cannot be in the last house (house index 3)
s.add(Or(heights[0] == 3, heights[1] == 3, heights[2] == 3))
# Then, if very short is in house i, dunhill must be in a house j>i
s.add(Or(
    And(heights[0] == 3, Or(cigars[1] == 2, cigars[2] == 2, cigars[3] == 2)),
    And(heights[1] == 3, Or(cigars[2] == 2, cigars[3] == 2)),
    And(heights[2] == 3, cigars[3] == 2)
))

# Clue 5: Watermelon smoothie (3) is to the right of desert smoothie (2)
s.add(Or(
    And(smoothies[0] == 2, Or(smoothies[1] == 3, smoothies[2] == 3, smoothies[3] == 3)),
    And(smoothies[1] == 2, Or(smoothies[2] == 3, smoothies[3] == 3)),
    And(smoothies[2] == 2, smoothies[3] == 3)
))

# Clue 6: Prince smoker (cigar=3) uses OnePlus 9 (phone=3)
for i in range(4):
    s.add((cigars[i] == 3) == (phones[i] == 3))

# Clue 7: Tall person (height=0) is in the third house (index2)
s.add(heights[2] == 0)

# Clue 8: Very short person (height=3) uses iPhone 13 (phone=2)
for i in range(4):
    s.add((heights[i] == 3) == (phones[i] == 2))

# Clue 9: Blue Master smoker (cigar=0) not in first house (index0)
s.add(cigars[0] != 0)

# Clue 10: Dunhill smoker (cigar=2) is short (height=2)
for i in range(4):
    s.add((cigars[i] == 2) == (heights[i] == 2))

# Clue 11: Peter (name=1) not in third house (index2)
s.add(names[2] != 1)

# Clue 12: Arnold (name=2) uses Google Pixel 6 (phone=0)
for i in range(4):
    s.add((names[i] == 2) == (phones[i] == 0))

# Clue 13: Dragonfruit smoothie (smoothie=0) is Pall Mall smoker (cigar=1)
for i in range(4):
    s.add((smoothies[i] == 0) == (cigars[i] == 1))

# Check and get the model
if s.check() == sat:
    model = s.model()
    
    # Map the integer values to strings
    name_map = {0: "Eric", 1: "Peter", 2: "Arnold", 3: "Alice"}
    smoothie_map = {0: "dragonfruit", 1: "cherry", 2: "desert", 3: "watermelon"}
    cigar_map = {0: "blue master", 1: "pall mall", 2: "dunhill", 3: "prince"}
    height_map = {0: "tall", 1: "average", 2: "short", 3: "very short"}
    phone_map = {0: "google pixel 6", 1: "samsung galaxy s21", 2: "iphone 13", 3: "oneplus 9"}
    
    # Prepare the rows
    rows = []
    for i in range(4):
        house_num = str(i+1)
        n_val = model.eval(names[i]).as_long()
        s_val = model.eval(smoothies[i]).as_long()
        c_val = model.eval(cigars[i]).as_long()
        h_val = model.eval(heights[i]).as_long()
        p_val = model.eval(phones[i]).as_long()
        row = [
            house_num,
            name_map[n_val],
            smoothie_map[s_val],
            cigar_map[c_val],
            height_map[h_val],
            phone_map[p_val]
        ]
        rows.append(row)
    
    # Format the solution as JSON
    solution = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "Cigar", "Height", "PhoneModel"],
            "rows": rows
        }
    }
    
    # Output as JSON string
    import json
    print(json.dumps(solution, indent=2))
    
else:
    print("No solution found")