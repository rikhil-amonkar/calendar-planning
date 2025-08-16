from z3 import *
import json

# Create 5 houses indexed 0..4 (corresponding to House 1..5)
num_houses = 5

# Each house has: name, birthday, cigar, drink.
# We represent their values as integers with the following mapping:
# Names: Bob=0, Alice=1, Eric=2, Arnold=3, Peter=4
# Birthdays: april=0, feb=1, jan=2, mar=3, sept=4
# Cigars: pall mall=0, prince=1, dunhill=2, blends=3, blue master=4
# Drinks: water=0, coffee=1, tea=2, milk=3, root beer=4

# Create Z3 integer arrays for each attribute.
names    = [Int(f"name_{i}") for i in range(num_houses)]
birthdays = [Int(f"birthday_{i}") for i in range(num_houses)]
cigars    = [Int(f"cigar_{i}") for i in range(num_houses)]
drinks    = [Int(f"drink_{i}") for i in range(num_houses)]

solver = Solver()

# Each variable is in the range 0..4.
for i in range(num_houses):
    solver.add(And(names[i] >= 0, names[i] < 5))
    solver.add(And(birthdays[i] >= 0, birthdays[i] < 5))
    solver.add(And(cigars[i] >= 0, cigars[i] < 5))
    solver.add(And(drinks[i] >= 0, drinks[i] < 5))

# All attributes must be distinct across houses.
solver.add(Distinct(names))
solver.add(Distinct(birthdays))
solver.add(Distinct(cigars))
solver.add(Distinct(drinks))

# --- Clues ---

# Clue 13: Eric is in the third house (house index 2).
solver.add(names[2] == 2)

# Clue 2: The person partial to Pall Mall is in the third house.
# ("pall mall" maps to 0)
solver.add(cigars[2] == 0)

# Clue 8: The person whose birthday is in February is in the second house (house index 1).
# (feb maps to 1)
solver.add(birthdays[1] == 1)

# Clue 1: The root beer lover is Eric.
# (root beer maps to 4; Eric is 2)
# We already know Eric is in house index 2, so force his drink to be root beer:
solver.add(drinks[2] == 4)

# Clue 3: The person whose birthday is in April is Bob.
# (april -> 0, Bob -> 0). Enforce that for any house, if name==0 then birthday==0, and vice versa.
for i in range(num_houses):
    solver.add(Implies(names[i] == 0, birthdays[i] == 0))
    solver.add(Implies(birthdays[i] == 0, names[i] == 0))

# Clue 4: The Dunhill smoker is the person whose birthday is in March.
# (dunhill -> 2, mar -> 3). So in any house, cigar==2 <-> birthday==3.
for i in range(num_houses):
    solver.add(Implies(cigars[i] == 2, birthdays[i] == 3))
    solver.add(Implies(birthdays[i] == 3, cigars[i] == 2))

# Clue 5: Peter is somewhere to the right of the root beer lover.
# (Peter -> 4, root beer -> 4). For any house i with Peter and any house j with drink==4, ensure i > j.
for i in range(num_houses):
    for j in range(num_houses):
        solver.add(Implies(And(names[i] == 4, drinks[j] == 4), i > j))

# Clue 6: There is one house between the person whose birthday is in January and Peter.
# (jan -> 2, Peter -> 4). Find the unique houses i and j with these properties and enforce |i - j| == 2.
# Since the uniqueness is ensured by Distinct, we can require for all i, j:
indices = range(num_houses)
for i in indices:
    for j in indices:
        solver.add(Implies(And(birthdays[i] == 2, names[j] == 4), Abs(i - j) == 2))

# Clue 7: The person who smokes many unique blends is the person whose birthday is in February.
# (blends -> 3, feb -> 1). So for any house, cigar==3 <-> birthday==1.
for i in range(num_houses):
    solver.add(Implies(cigars[i] == 3, birthdays[i] == 1))
    solver.add(Implies(birthdays[i] == 1, cigars[i] == 3))

# Clue 9: Arnold is directly left of Peter.
# (Arnold -> 3, Peter -> 4). For every house j that has Peter, ensure j > 0 and the house immediately left (j-1) has Arnold.
for j in range(num_houses):
    # if house j has Peter then j must be at least 1 and house j-1 is Arnold.
    solver.add(Implies(names[j] == 4, And(j > 0, names[j-1] == 3)))

# Clue 10: The person who likes milk is not in the fifth house (house index 4).
# (milk -> 3).
solver.add(drinks[4] != 3)

# Clue 11: The person who smokes Blue Master is the coffee drinker.
# (blue master -> 4, coffee -> 1). For all houses, cigar==4 <-> drink==1.
for i in range(num_houses):
    solver.add(Implies(cigars[i] == 4, drinks[i] == 1))
    solver.add(Implies(drinks[i] == 1, cigars[i] == 4))

# Clue 12: There is one house between the tea drinker and the coffee drinker.
# (tea -> 2, coffee -> 1). For all houses i and j for which these hold, enforce Abs(i - j) == 2.
for i in range(num_houses):
    for j in range(num_houses):
        solver.add(Implies(And(drinks[i] == 2, drinks[j] == 1), Abs(i - j) == 2))

# --- End of constraints ---

if solver.check() == sat:
    model = solver.model()
    
    # Mapping dictionaries for converting integer codes back to strings.
    name_map = {0: "Bob", 1: "Alice", 2: "Eric", 3: "Arnold", 4: "Peter"}
    birthday_map = {0: "april", 1: "feb", 2: "jan", 3: "mar", 4: "sept"}
    cigar_map = {0: "pall mall", 1: "prince", 2: "dunhill", 3: "blends", 4: "blue master"}
    drink_map = {0: "water", 1: "coffee", 2: "tea", 3: "milk", 4: "root beer"}
    
    # Construct the solution rows in the order House 1 to House 5.
    rows = []
    for i in range(num_houses):
        house_num = str(i+1)
        sol_name = name_map[model.evaluate(names[i]).as_long()]
        sol_birthday = birthday_map[model.evaluate(birthdays[i]).as_long()]
        sol_cigar = cigar_map[model.evaluate(cigars[i]).as_long()]
        sol_drink = drink_map[model.evaluate(drinks[i]).as_long()]
        rows.append([house_num, sol_name, sol_birthday, sol_cigar, sol_drink])
    
    solution = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Cigar", "Drink"],
            "rows": rows
        }
    }
    # Print the JSON-formatted solution
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")