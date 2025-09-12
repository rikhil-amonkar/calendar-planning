import z3
import json

# Define variables for each name's house
alice_h = z3.Int('alice_h')
eric_h = z3.Int('eric_h')
bob_h = z3.Int('bob_h')
peter_h = z3.Int('peter_h')
arnold_h = z3.Int('arnold_h')
carol_h = z3.Int('carol_h')

names_h = [alice_h, eric_h, bob_h, peter_h, arnold_h, carol_h]

# Define variables for each height's house
very_tall_h = z3.Int('very_tall_h')
tall_h = z3.Int('tall_h')
super_tall_h = z3.Int('super_tall_h')
average_h = z3.Int('average_h')
very_short_h = z3.Int('very_short_h')
short_h = z3.Int('short_h')

heights_h = [very_tall_h, tall_h, super_tall_h, average_h, very_short_h, short_h]

# Define variables for each phone's house
oneplus9_h = z3.Int('oneplus9_h')
googlepixel6_h = z3.Int('googlepixel6_h')
samsungs21_h = z3.Int('samsungs21_h')
iphone13_h = z3.Int('iphone13_h')
huawei_h = z3.Int('huawei_h')
xiaomi_h = z3.Int('xiaomi_h')

phones_h = [oneplus9_h, googlepixel6_h, samsungs21_h, iphone13_h, huawei_h, xiaomi_h]

# Create the solver and add constraints
s = z3.Solver()

# All variables between 0 and 5
for var in names_h + heights_h + phones_h:
    s.add(z3.And(0 <= var, var <= 5))

# All variables in each category are distinct
s.add(z3.Distinct(names_h))
s.add(z3.Distinct(heights_h))
s.add(z3.Distinct(phones_h))

# Add the clues as constraints
# Clue 1: Bob is directly left of the person who is tall.
s.add(bob_h + 1 == tall_h)

# Clue 2: Peter is somewhere left of iPhone 13 user.
s.add(peter_h < iphone13_h)

# Clue 3: very_short is to the right of Google Pixel 6.
s.add(very_short_h > googlepixel6_h)

# Clue 4: Carol is very tall.
s.add(carol_h == very_tall_h)

# Clue 5: one house between Google Pixel 6 and short.
s.add(googlepixel6_h + 2 == short_h)

# Clue 12: short is in house 6 (index 5)
s.add(short_h == 5)

# Clue 6: Samsung Galaxy S21 not in first house (index 0)
s.add(samsungs21_h != 0)

# Clue 7: OnePlus 9 directly left of short (index 5)
s.add(oneplus9_h + 1 == short_h)

# Clue 8: tall is Arnold
s.add(tall_h == arnold_h)

# Clue 9: super tall in first house (index 0)
s.add(super_tall_h == 0)

# Clue 10: Carol uses Xiaomi Mi 11
s.add(carol_h == xiaomi_h)

# Clue 11: Google Pixel 6 is to the right of Eric
s.add(eric_h < googlepixel6_h)

# Check if the solver can find a solution
if s.check() == z3.sat:
    model = s.model()
    # Build the solution
    solution = []
    for house_idx in range(6):
        # Determine the name
        name = None
        for i, n in enumerate(["Alice", "Eric", "Bob", "Peter", "Arnold", "Carol"]):
            if model.evaluate(names_h[i]).as_long() == house_idx:
                name = n
        # Determine the height
        height = None
        for i, h in enumerate(["very tall", "tall", "super tall", "average", "very short", "short"]):
            if model.evaluate(heights_h[i]).as_long() == house_idx:
                height = h
        # Determine the phone
        phone = None
        for i, p in enumerate(["oneplus 9", "google pixel 6", "samsung galaxy s21", "iphone 13", "huawei p50", "xiaomi mi 11"]):
            if model.evaluate(phones_h[i]).as_long() == house_idx:
                phone = p
        solution.append([str(house_idx + 1), name, height, phone])
    # Format as JSON
    output = {
        "solution": {
            "header": ["House", "Name", "Height", "PhoneModel"],
            "rows": solution
        }
    }
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")