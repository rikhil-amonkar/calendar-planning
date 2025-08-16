import z3

s = z3.Solver()

# Define variables for each house (0-4)
names = [z3.Int('name_%d' % i) for i in range(5)]
heights = [z3.Int('height_%d' % i) for i in range(5)]
cigars = [z3.Int('cigar_%d' % i) for i in range(5)]
smoothies = [z3.Int('smoothie_%d' % i) for i in range(5)]
phones = [z3.Int('phone_%d' % i) for i in range(5)]

# Add distinct and range constraints
for attr in [names, heights, cigars, smoothies, phones]:
    s.add(z3.Distinct(attr))
    for var in attr:
        s.add(z3.And(0 <= var, var <= 4))

# Clue 1: Prince smoker is Desert smoothie lover.
for i in range(5):
    s.add(z3.Implies(cigars[i] == 0, smoothies[i] == 4))

# Clue 2: One house between Eric and Alice.
pos_Eric = z3.Int('pos_Eric')
pos_Alice = z3.Int('pos_Alice')
s.add(z3.And(0 <= pos_Eric, pos_Eric <= 4))
s.add(z3.And(0 <= pos_Alice, pos_Alice <= 4))
for i in range(5):
    i_val = z3.IntVal(i)
    # For Eric
    s.add(z3.Implies(pos_Eric == i_val, names[i] == 2))
    s.add(z3.Implies(names[i] == 2, pos_Eric == i_val))
    # For Alice
    s.add(z3.Implies(pos_Alice == i_val, names[i] == 4))
    s.add(z3.Implies(names[i] == 4, pos_Alice == i_val))
s.add(z3.Abs(pos_Eric - pos_Alice) == 2)

# Clue 3: Short person smokes Blends.
for i in range(5):
    s.add(z3.Implies(heights[i] == 3, cigars[i] == 2))

# Clue 4: iPhone 13 user is directly left of Blue Master smoker.
s.add(z3.Or([z3.And(phones[i] == 2, cigars[i+1] == 4) for i in range(4)]))

# Clue 5: Average height person smokes Dunhill.
for i in range(5):
    s.add(z3.Implies(heights[i] == 0, cigars[i] == 1))

# Clue 6: Eric is very tall.
s.add(z3.Or(
    z3.And(pos_Eric == 0, heights[0] == 1),
    z3.And(pos_Eric == 1, heights[1] == 1),
    z3.And(pos_Eric == 2, heights[2] == 1),
    z3.And(pos_Eric == 3, heights[3] == 1),
    z3.And(pos_Eric == 4, heights[4] == 1)
))

# Clue 7: Arnold is directly left of Huawei P50 user.
s.add(z3.Or([z3.And(names[i] == 1, phones[i+1] == 3) for i in range(4)]))

# Clue 8: Bob is not in the fourth house (index 3).
s.add(names[3] != 3)

# Clue 9: Eric is directly left of Cherry smoothie lover.
s.add(z3.Or([z3.And(names[i] == 2, smoothies[i+1] == 1) for i in range(4)]))

# Clue 10: Bob smokes Dunhill.
pos_Bob = z3.Int('pos_Bob')
s.add(z3.And(0 <= pos_Bob, pos_Bob <= 4))
for i in range(5):
    i_val = z3.IntVal(i)
    s.add(z3.Implies(pos_Bob == i_val, names[i] == 3))
    s.add(z3.Implies(names[i] == 3, pos_Bob == i_val))
s.add(z3.Or(
    z3.And(pos_Bob == 0, cigars[0] == 1),
    z3.And(pos_Bob == 1, cigars[1] == 1),
    z3.And(pos_Bob == 2, cigars[2] == 1),
    z3.And(pos_Bob == 3, cigars[3] == 1),
    z3.And(pos_Bob == 4, cigars[4] == 1)
))

# Clue 11: Dragonfruit smoothie lover is Bob.
s.add(z3.Or(
    z3.And(pos_Bob == 0, smoothies[0] == 2),
    z3.And(pos_Bob == 1, smoothies[1] == 2),
    z3.And(pos_Bob == 2, smoothies[2] == 2),
    z3.And(pos_Bob == 3, smoothies[3] == 2),
    z3.And(pos_Bob == 4, smoothies[4] == 2)
))

# Clue 12: iPhone 13 and OnePlus 9 are next to each other.
s.add(z3.Or([z3.Or(
    z3.And(phones[i] == 2, phones[i+1] == 0),
    z3.And(phones[i] == 0, phones[i+1] == 2)
) for i in range(4)]))

# Clue 13: Samsung Galaxy S21 user is short.
for i in range(5):
    s.add(z3.Implies(phones[i] == 1, heights[i] == 3))

# Clue 14: Two houses between very tall (Eric) and Dragonfruit lover (Bob).
s.add(z3.Abs(pos_Eric - pos_Bob) == 3)

# Clue 15: iPhone 13 user is Eric.
s.add(z3.Or(
    z3.And(pos_Eric == 0, phones[0] == 2),
    z3.And(pos_Eric == 1, phones[1] == 2),
    z3.And(pos_Eric == 2, phones[2] == 2),
    z3.And(pos_Eric == 3, phones[3] == 2),
    z3.And(pos_Eric == 4, phones[4] == 2)
))

# Clue 16: Desert lover is left of Lime.
pos_desert = z3.Int('pos_desert')
pos_lime = z3.Int('pos_lime')
s.add(z3.And(0 <= pos_desert, pos_desert <= 4))
s.add(z3.And(0 <= pos_lime, pos_lime <= 4))
for i in range(5):
    i_val = z3.IntVal(i)
    s.add(z3.Implies(smoothies[i] == 4, pos_desert == i_val))
    s.add(z3.Implies(pos_desert == i_val, smoothies[i] == 4))
    s.add(z3.Implies(smoothies[i] == 0, pos_lime == i_val))
    s.add(z3.Implies(pos_lime == i_val, smoothies[i] == 0))
s.add(pos_desert < pos_lime)

# Clue 17: Arnold and very short are next to each other.
s.add(z3.Or([z3.Or(
    z3.And(names[i] == 1, heights[i+1] == 2),
    z3.And(heights[i] == 2, names[i+1] == 1)
) for i in range(4)]))

# Check if the constraints are satisfiable
if s.check() == z3.sat:
    model = s.model()
    # Now extract the values for each house
    rows = []
    for house in range(5):
        name_val = model[names[house]].as_long()
        height_val = model[heights[house]].as_long()
        cigar_val = model[cigars[house]].as_long()
        smoothie_val = model[smoothies[house]].as_long()
        phone_val = model[phones[house]].as_long()
        
        name_str = ['Peter', 'Arnold', 'Eric', 'Bob', 'Alice'][name_val]
        height_str = ['average', 'very tall', 'very short', 'short', 'tall'][height_val]
        cigar_str = ['prince', 'dunhill', 'blends', 'pall mall', 'blue master'][cigar_val]
        smoothie_str = ['lime', 'cherry', 'dragonfruit', 'watermelon', 'desert'][smoothie_val]
        phone_str = ['oneplus 9', 'samsung galaxy s21', 'iphone 13', 'huawei p50', 'google pixel 6'][phone_val]
        
        rows.append([str(house + 1), name_str, height_str, cigar_str, smoothie_str, phone_str])
    
    solution = {
        "solution": {
            "header": ["House", "Name", "Height", "Cigar", "Smoothie", "PhoneModel"],
            "rows": rows
        }
    }
    print(solution)
else:
    print("No solution found.")