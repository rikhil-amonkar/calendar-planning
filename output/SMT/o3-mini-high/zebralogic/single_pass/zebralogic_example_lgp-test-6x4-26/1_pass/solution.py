from z3 import *
import json

# There are 6 houses, numbered 0..5 (which we later display as 1..6).
n = 6

# Create an integer variable for each house’s attribute.
Names = [Int(f"name_{i}") for i in range(n)]
Pets = [Int(f"pet_{i}") for i in range(n)]
Styles = [Int(f"style_{i}") for i in range(n)]
Birthdays = [Int(f"bday_{i}") for i in range(n)]

# We assign each attribute a unique integer value from 0 to 5.
# Mappings (the actual text values will be recovered at the end):
# Names mapping:
#   Peter: 0, Bob: 1, Carol: 2, Eric: 3, Alice: 4, Arnold: 5
PETER, BOB, CAROL, ERIC, ALICE, ARNOLD = 0, 1, 2, 3, 4, 5

# Pets mapping:
#   bird: 0, dog: 1, cat: 2, rabbit: 3, fish: 4, hamster: 5
BIRD, DOG, CAT, RABBIT, FISH, HAMSTER = 0, 1, 2, 3, 4, 5

# HouseStyle mapping:
#   victorian: 0, ranch: 1, modern: 2, mediterranean: 3, colonial: 4, craftsman: 5
VICTORIAN, RANCH, MODERN, MEDITERRANEAN, COLONIAL, CRAFTSMAN = 0, 1, 2, 3, 4, 5

# Birthday mapping:
#   mar: 0, sept: 1, may: 2, feb: 3, jan: 4, april: 5
MAR, SEPT, MAY, FEB, JAN, APRIL = 0, 1, 2, 3, 4, 5

s = Solver()

# Every attribute variable is in the domain 0..5.
for i in range(n):
    s.add(And(Names[i] >= 0, Names[i] < 6))
    s.add(And(Pets[i] >= 0, Pets[i] < 6))
    s.add(And(Styles[i] >= 0, Styles[i] < 6))
    s.add(And(Birthdays[i] >= 0, Birthdays[i] < 6))

# All values must be distinct in each category.
s.add(Distinct(Names))
s.add(Distinct(Pets))
s.add(Distinct(Styles))
s.add(Distinct(Birthdays))

# ----- Clues -----

# 3. The person whose birthday is in May is in the second house (index 1).
s.add(Birthdays[1] == MAY)

# 4. The person living in a colonial-style house is in the second house.
s.add(Styles[1] == COLONIAL)

# 5. Carol is in the third house (index 2).
s.add(Names[2] == CAROL)

# 8. Eric is in the sixth house (index 5).
s.add(Names[5] == ERIC)

# 11 & 18. The person in a Craftsman-style house is in the fourth house (index 3) and that person is Arnold.
s.add(Styles[3] == CRAFTSMAN)
s.add(Names[3] == ARNOLD)

# 19. The person who owns a dog is in the fourth house.
s.add(Pets[3] == DOG)

# 14. Peter is the person living in a colonial-style house.
# (Since the colonial house is at index 1, this forces:)
s.add(Names[1] == PETER)

# 17. Carol is the person whose birthday is in March.
s.add(Birthdays[2] == MAR)

# 15. The person whose birthday is in January is directly left of the person whose birthday is in April.
# That is, for some 0 <= i < 5: if house i has birthday JAN then house i+1 has birthday APRIL.
s.add(Or([And(Birthdays[i] == JAN, Birthdays[i+1] == APRIL) for i in range(n - 1)]))

# 2. The person whose birthday is in January is somewhere to the left of the person whose birthday is in September.
for i in range(n):
    for j in range(n):
        s.add(Implies(And(Birthdays[i] == JAN, Birthdays[j] == SEPT), i < j))

# 1. The person with a pet hamster is somewhere to the right of the person whose birthday is in March.
for i in range(n):
    for j in range(n):
        s.add(Implies(And(Birthdays[i] == MAR, Pets[j] == HAMSTER), i < j))

# 7. The person with an aquarium of fish is somewhere to the right of Bob.
for i in range(n):
    for j in range(n):
        s.add(Implies(And(Names[i] == BOB, Pets[j] == FISH), i < j))

# 9. There is one house between the person who has a cat and the person residing in a Victorian house.
for i in range(n):
    for j in range(n):
        s.add(Implies(And(Pets[i] == CAT, Styles[j] == VICTORIAN), Abs(i - j) == 2))

# 10. There are two houses between the person residing in a Victorian house and the person with a pet hamster.
for i in range(n):
    for j in range(n):
        s.add(Implies(And(Styles[i] == VICTORIAN, Pets[j] == HAMSTER), Abs(i - j) == 3))

# 12. The person living in a colonial-style house is somewhere to the left of the person in a modern-style house.
for i in range(n):
    for j in range(n):
        s.add(Implies(And(Styles[i] == COLONIAL, Styles[j] == MODERN), i < j))

# 13. The person with an aquarium of fish is not in the second house.
s.add(Pets[1] != FISH)

# 16. There is one house between the person who keeps a pet bird and the person in a modern-style house.
for i in range(n):
    for j in range(n):
        s.add(Implies(And(Pets[i] == BIRD, Styles[j] == MODERN), Abs(i - j) == 2))

# 6. The person in a Mediterranean-style villa is not in the sixth house.
s.add(Styles[5] != MEDITERRANEAN)

# ----- Solve and output the solution -----

if s.check() == sat:
    m = s.model()
    # Reverse mappings to convert numbers back to words.
    name_map = {PETER: "Peter", BOB: "Bob", CAROL: "Carol", ERIC: "Eric", ALICE: "Alice", ARNOLD: "Arnold"}
    pet_map = {BIRD: "bird", DOG: "dog", CAT: "cat", RABBIT: "rabbit", FISH: "fish", HAMSTER: "hamster"}
    style_map = {VICTORIAN: "victorian", RANCH: "ranch", MODERN: "modern", MEDITERRANEAN: "mediterranean", COLONIAL: "colonial", CRAFTSMAN: "craftsman"}
    bday_map = {MAR: "mar", SEPT: "sept", MAY: "may", FEB: "feb", JAN: "january", APRIL: "april"}

    solution_rows = []
    for i in range(n):
        # House numbers are 1-indexed.
        house = str(i + 1)
        name_val = m.evaluate(Names[i]).as_long()
        pet_val = m.evaluate(Pets[i]).as_long()
        style_val = m.evaluate(Styles[i]).as_long()
        bday_val = m.evaluate(Birthdays[i]).as_long()
        solution_rows.append([house, name_map[name_val], pet_map[pet_val], style_map[style_val], bday_map[bday_val]])
    
    output = {
        "solution": {
            "header": ["House", "Name", "Pet", "HouseStyle", "Birthday"],
            "rows": solution_rows
        }
    }
    print(json.dumps(output, indent=2))
else:
    print("No solution found")