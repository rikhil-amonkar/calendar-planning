from z3 import *

s = Solver()

# Create variables for each house's attributes (houses 1-6, indexes 0-5)
names = [Int('name_%d' % i) for i in range(6)]
pets = [Int('pet_%d' % i) for i in range(6)]
housestyles = [Int('housestyle_%d' % i) for i in range(6)]
birthdays = [Int('birthday_%d' % i) for i in range(6)]

# Add constraints that each array is a permutation of 0-5
for arr in [names, pets, housestyles, birthdays]:
    s.add(Distinct(arr))
    s.add(And([And(0 <= arr[i], arr[i] <= 5) for i in range(6)]))

# Now add fixed clues
s.add(birthdays[1] == 4)  # Clue 3: house 2's birthday is may (4)
s.add(housestyles[1] == 4)  # Clue 4: house 2's housestyle is colonial (4)
s.add(names[2] == 2)  # Clue 5: house 3's name is Carol (2)
s.add(names[5] == 3)  # Clue 8: house 6's name is Eric (3)
s.add(names[1] == 0)  # Clue 14: house 2's name is Peter (0)
s.add(birthdays[2] == 2)  # Clue 17: house 3's birthday is March (2)
s.add(housestyles[3] == 5)  # Clue 18: house 4's housestyle is Craftsman (5)
s.add(names[3] == 5)  # Clue 11: house 4's name is Arnold (5)
s.add(pets[3] == 1)  # Clue 19: house 4's pet is dog (1)

# Clue 1: hamster (5) is in house 4,5,6 (indexes 3,4,5)
s.add(Or(pets[3] == 5, pets[4] == 5, pets[5] == 5))

# Clue 2: jan (0) is left of sept (5)
for i in range(6):
    for j in range(6):
        s.add(Implies(And(birthdays[i] == 0, birthdays[j] == 5), i < j))

# Clue 7: Fish (4) is to the right of Bob (1)
for i in range(6):
    for j in range(6):
        s.add(Implies(And(names[i] == 1, pets[j] == 4), i < j))

# Clue 9: one house between cat (2) and victorian (0)
for i in range(6):
    for j in range(6):
        s.add(Implies(And(pets[i] == 2, housestyles[j] == 0), Abs(i - j) == 2))

# Clue 10: two houses between victorian (0) and hamster (5)
for i in range(6):
    for j in range(6):
        s.add(Implies(And(housestyles[i] == 0, pets[j] == 5), Abs(i - j) == 3))

# Clue 12: colonial (4) is in house 2 (index 1), modern (2) is to the right (i.e., modern's index >1)
for i in range(6):
    s.add(Implies(housestyles[i] == 2, i > 1))

# Clue 13: Fish (4) not in house 2 (index 1)
s.add(pets[1] != 4)

# Clue 15: jan (0) directly left of april (3)
s.add(Or(*[And(birthdays[i] == 0, birthdays[i + 1] == 3) for i in range(5)]))

# Clue 16: one house between bird (0) and modern (2)
for i in range(6):
    for j in range(6):
        s.add(Implies(And(pets[i] == 0, housestyles[j] == 2), Abs(i - j) == 2))

# Clue 6: house 6 (index 5) not mediterranean (3)
s.add(housestyles[5] != 3)

if s.check() == sat:
    m = s.model()
    solution = []
    for i in range(6):
        house_num = i + 1
        name_val = m.evaluate(names[i])
        pet_val = m.evaluate(pets[i])
        housestyle_val = m.evaluate(housestyles[i])
        birthday_val = m.evaluate(birthdays[i])
        name_str = ["Peter", "Bob", "Carol", "Eric", "Alice", "Arnold"][name_val.as_long()]
        pet_str = ["bird", "dog", "cat", "rabbit", "fish", "hamster"][pet_val.as_long()]
        housestyle_str = ["victorian", "ranch", "modern", "mediterranean", "colonial", "craftsman"][housestyle_val.as_long()]
        birthday_str = ["jan", "feb", "mar", "april", "may", "sept"][birthday_val.as_long()]
        solution.append([str(house_num), name_str, pet_str, housestyle_str, birthday_str])
    print(json.dumps({
        "solution": {
            "header": ["House", "Name", "Pet", "HouseStyle", "Birthday"],
            "rows": solution
        }
    }, indent=2))
else:
    print("No solution found")