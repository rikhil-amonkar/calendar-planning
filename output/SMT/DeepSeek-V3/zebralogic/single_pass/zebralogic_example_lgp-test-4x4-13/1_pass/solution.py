from z3 import *

# Create a solver instance
s = Solver()

# Define the attributes for each house (1 to 4)
houses = [1, 2, 3, 4]

# Define variables for each attribute
name = {h: String(f"name_{h}") for h in houses}
cigar = {h: String(f"cigar_{h}") for h in houses}
favorite_sport = {h: String(f"sport_{h}") for h in houses}
drink = {h: String(f"drink_{h}") for h in houses}

# Define the possible values for each attribute
names = ["Alice", "Peter", "Arnold", "Eric"]
cigars = ["prince", "dunhill", "blue master", "pall mall"]
sports = ["swimming", "basketball", "soccer", "tennis"]
drinks = ["coffee", "water", "milk", "tea"]

# Add constraints that each attribute is unique across houses
for h in houses:
    s.add(Or([name[h] == n for n in names]))
    s.add(Or([cigar[h] == c for c in cigars]))
    s.add(Or([favorite_sport[h] == sp for sp in sports]))
    s.add(Or([drink[h] == d for d in drinks]))

for h1 in houses:
    for h2 in houses:
        if h1 < h2:
            s.add(name[h1] != name[h2])
            s.add(cigar[h1] != cigar[h2])
            s.add(favorite_sport[h1] != favorite_sport[h2])
            s.add(drink[h1] != drink[h2])

# Add constraints based on the clues
# 1. Peter is in the fourth house.
s.add(name[4] == "Peter")

# 2. The tea drinker is the person who loves basketball.
for h in houses:
    s.add(Implies(drink[h] == "tea", favorite_sport[h] == "basketball"))

# 3. Arnold is the person who smokes Blue Master.
for h in houses:
    s.add(Implies(name[h] == "Arnold", cigar[h] == "blue master"))

# 4. The person who loves basketball is Eric.
for h in houses:
    s.add(Implies(favorite_sport[h] == "basketball", name[h] == "Eric"))

# 5. The person who loves tennis is the person who smokes Blue Master.
for h in houses:
    s.add(Implies(favorite_sport[h] == "tennis", cigar[h] == "blue master"))

# 6. There are two houses between the one who only drinks water and Peter.
# Peter is in house 4, so water drinker is in house 1 (since 4 - 3 = 1)
s.add(drink[1] == "water")

# 7. The coffee drinker is Arnold.
for h in houses:
    s.add(Implies(name[h] == "Arnold", drink[h] == "coffee"))

# 8. The person who loves basketball is in the third house.
s.add(favorite_sport[3] == "basketball")

# 9. The Prince smoker is the person who loves soccer.
for h in houses:
    s.add(Implies(cigar[h] == "prince", favorite_sport[h] == "soccer"))

# 10. Peter is the person partial to Pall Mall.
s.add(cigar[4] == "pall mall")

# Solve the model
if s.check() == sat:
    m = s.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Cigar", "FavoriteSport", "Drink"],
            "rows": []
        }
    }
    for h in houses:
        row = [
            str(h),
            m.evaluate(name[h]).as_string(),
            m.evaluate(cigar[h]).as_string(),
            m.evaluate(favorite_sport[h]).as_string(),
            m.evaluate(drink[h]).as_string()
        ]
        solution["solution"]["rows"].append(row)
    import json
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")