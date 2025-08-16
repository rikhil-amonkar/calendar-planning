from z3 import *
import json

# Initialize Z3 solver
s = Solver()

# Define variables for each house (1-5) and attributes
names = [Int(f'name_{i+1}') for i in range(5)]
birthdays = [Int(f'birthday_{i+1}') for i in range(5)]
cigars = [Int(f'cigar_{i+1}') for i in range(5)]
drinks = [Int(f'drink_{i+1}') for i in range(5)]

# All variables are between 0 and 4
for var in names + birthdays + cigars + drinks:
    s.add(And(0 <= var, var <= 4))

# All must be distinct in each category
s.add(Distinct(names))
s.add(Distinct(birthdays))
s.add(Distinct(cigars))
s.add(Distinct(drinks))

# Clue 1: Root beer lover is Eric (house 3)
s.add(drinks[2] == 4)

# Clue 2: Pall Mall in third house
s.add(cigars[2] == 0)

# Clue 3: Bob's birthday is April
s.add(Or(
    And(names[0] == 3, birthdays[0] == 0),
    And(names[1] == 3, birthdays[1] == 0)
))

# Clue 4: Dunhill smoker has March birthday
for i in range(5):
    s.add(Implies(cigars[i] == 2, birthdays[i] == 2))

# Clue 6: Jan birthday and Peter (house 5) separated by one house
s.add(birthdays[2] == 3)  # Jan in house 3

# Clue 7 & 8: Blends smoker (cigar 3) in house 2 with Feb birthday
s.add(birthdays[1] == 1)
s.add(cigars[1] == 3)

# Clue 9: Arnold (4) is directly left of Peter (0)
s.add(names[3] == 4)
s.add(names[4] == 0)

# Clue 10: Milk not in fifth house
s.add(drinks[4] != 3)

# Clue 11: Blue Master smoker drinks coffee
for i in range(5):
    s.add(Implies(cigars[i] == 4, drinks[i] == 1))

# Clue 12: One house between tea and coffee
pairs = [(0, 2), (1, 3), (2, 4)]
for i, j in pairs:
    s.add(Or(
        And(drinks[i] == 1, drinks[j] == 2),
        And(drinks[i] == 2, drinks[j] == 1)
    ))

# Clue 13: Eric in house 3
s.add(names[2] == 2)

if s.check() == sat:
    model = s.model()
    solution = []
    for i in range(5):
        house_num = i + 1
        name_val = model[names[i]].as_long()
        birthday_val = model[birthdays[i]].as_long()
        cigar_val = model[cigars[i]].as_long()
        drink_val = model[drinks[i]].as_long()
        solution.append([
            str(house_num),
            ["Peter", "Alice", "Eric", "Bob", "Arnold"][name_val],
            ["april", "feb", "mar", "jan", "sept"][birthday_val],
            ["pall mall", "prince", "dunhill", "blends", "blue master"][cigar_val],
            ["water", "coffee", "tea", "milk", "root beer"][drink_val]
        ])
    print(json.dumps({
        "solution": {
            "header": ["House", "Name", "Birthday", "Cigar", "Drink"],
            "rows": solution
        }
    }, indent=2))
else:
    print("No solution found.")