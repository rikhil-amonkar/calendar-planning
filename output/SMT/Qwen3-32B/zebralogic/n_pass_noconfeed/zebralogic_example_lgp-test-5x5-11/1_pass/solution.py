import z3
import json

# Define the possible values for each attribute
names_list = ['Peter', 'Arnold', 'Eric', 'Bob', 'Alice']
heights_list = ['average', 'very tall', 'very short', 'short', 'tall']
cigars_list = ['prince', 'dunhill', 'blends', 'pall mall', 'blue master']
smoothies_list = ['lime', 'cherry', 'dragonfruit', 'watermelon', 'desert']
phones_list = ['oneplus 9', 'samsung galaxy s21', 'iphone 13', 'huawei p50', 'google pixel 6']

# Initialize Z3 solver
s = z3.Solver()

# Create variables for each house (0-4)
names = [z3.Int(f'name_{i}') for i in range(5)]
heights = [z3.Int(f'height_{i}') for i in range(5)]
cigars = [z3.Int(f'cigar_{i}') for i in range(5)]
smoothies = [z3.Int(f'smoothie_{i}') for i in range(5)]
phones = [z3.Int(f'phone_{i}') for i in range(5)]

# Add constraints for distinct and range
for attr in [names, heights, cigars, smoothies, phones]:
    s.add(z3.Distinct(*attr))
    for var in attr:
        s.add(var >= 0, var <= 4)

# Add all the puzzle constraints
# Clue 1: Prince smoker is Desert smoothie lover
s.add(z3.Or([z3.And(cigars[i] == 0, smoothies[i] == 4) for i in range(5)]))

# Clue 2: Eric and Alice have one house between them
possible_pairs = [(0, 2), (2, 0), (1, 3), (3, 1), (2, 4), (4, 2)]
s.add(z3.Or([z3.And(names[i] == 2, names[j] == 4) for i, j in possible_pairs]))

# Clue 3: Short is Blends
s.add(z3.Or([z3.And(heights[i] == 3, cigars[i] == 2) for i in range(5)]))

# Clue 4: iPhone 13 is directly left of Blue Master
s.add(z3.Or([z3.And(phones[i] == 2, cigars[i+1] == 4) for i in range(4)]))

# Clue 5: Average height is Dunhill
s.add(z3.Or([z3.And(heights[i] == 0, cigars[i] == 1) for i in range(5)]))

# Clue 6: Eric is very tall
for i in range(5):
    s.add(z3.Implies(names[i] == 2, heights[i] == 1))

# Clue 7: Arnold is directly left of Huawei P50
s.add(z3.Or([z3.And(names[i] == 1, phones[i+1] == 3) for i in range(4)]))

# Clue 8: Bob is not in the fourth house
s.add(names[3] != 3)

# Clue 9: Eric is directly left of Cherry smoothie lover
s.add(z3.Or([z3.And(names[i] == 2, smoothies[i+1] == 1) for i in range(4)]))

# Clue 10: Bob is Dunhill smoker
for i in range(5):
    s.add(z3.Implies(names[i] == 3, cigars[i] == 1))

# Clue 11: Dragonfruit lover is Bob
for i in range(5):
    s.add(z3.Implies(names[i] == 3, smoothies[i] == 2))

# Clue 12: iPhone 13 and OnePlus 9 are next to each other
s.add(z3.Or([z3.Or(
    z3.And(phones[i] == 2, phones[i+1] == 0),
    z3.And(phones[i] == 0, phones[i+1] == 2)
) for i in range(4)]))

# Clue 13: Samsung Galaxy S21 user is short
s.add(z3.Or([z3.And(phones[i] == 1, heights[i] == 3) for i in range(5)]))

# Clue 14: Very tall (Eric) and Dragonfruit lover (Bob) have two houses between
s.add(z3.Or(
    z3.And(names[0] == 2, names[3] == 3),
    z3.And(names[3] == 2, names[0] == 3),
    z3.And(names[1] == 2, names[4] == 3),
    z3.And(names[4] == 2, names[1] == 3)
))

# Clue 15: iPhone 13 user is Eric
for i in range(5):
    s.add(z3.Implies(names[i] == 2, phones[i] == 2))

# Clue 16: Desert lover is left of Lime lover
for i in range(5):
    for j in range(5):
        s.add(z3.Implies(z3.And(smoothies[i] == 4, smoothies[j] == 0), i < j))

# Clue 17: Arnold and very short are next to each other
s.add(z3.Or(
    [z3.And(names[i] == 1, heights[i+1] == 2) for i in range(4)] + 
    [z3.And(heights[i] == 2, names[i+1] == 1) for i in range(4)]
))

# Solve the constraints
if s.check() == z3.sat:
    model = s.model()
    solution = []
    for i in range(5):
        house_num = i + 1
        name_val = model[names[i]].as_long()
        height_val = model[heights[i]].as_long()
        cigar_val = model[cigars[i]].as_long()
        smoothie_val = model[smoothies[i]].as_long()
        phone_val = model[phones[i]].as_long()
        solution.append([
            str(house_num),
            names_list[name_val],
            heights_list[height_val],
            cigars_list[cigar_val],
            smoothies_list[smoothie_val],
            phones_list[phone_val]
        ])
    output = {
        "solution": {
            "header": ["House", "Name", "Height", "Cigar", "Smoothie", "PhoneModel"],
            "rows": solution
        }
    }
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")