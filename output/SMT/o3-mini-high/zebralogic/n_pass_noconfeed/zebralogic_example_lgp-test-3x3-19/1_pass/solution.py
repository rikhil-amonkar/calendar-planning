from z3 import *
import json

# Mappings for each attribute
names_map = {0: "Peter", 1: "Arnold", 2: "Eric"}
smoothies_map = {0: "desert", 1: "watermelon", 2: "cherry"}
genres_map = {0: "science fiction", 1: "romance", 2: "mystery"}

# There are 3 houses, index 0 for house 1, index 1 for house 2, index 2 for house 3.
num_houses = 3

# Create Z3 Int variables for each house attribute.
names = [Int(f"name_{i}") for i in range(num_houses)]
smoothies = [Int(f"smoothie_{i}") for i in range(num_houses)]
genres = [Int(f"genre_{i}") for i in range(num_houses)]

s = Solver()

# Domain constraints: Each variable is between 0 and 2.
for i in range(num_houses):
    s.add(And(names[i] >= 0, names[i] <= 2))
    s.add(And(smoothies[i] >= 0, smoothies[i] <= 2))
    s.add(And(genres[i] >= 0, genres[i] <= 2))

# All attributes in each category must be distinct.
s.add(Distinct(names))
s.add(Distinct(smoothies))
s.add(Distinct(genres))

# Clue 5: Peter is in the first house.
# Mapping: Peter = 0.
s.add(names[0] == 0)

# Clue 2: Arnold is the person who loves mystery books.
# Mapping: Arnold = 1 and mystery = 2.
for i in range(num_houses):
    s.add(Implies(names[i] == 1, genres[i] == 2))

# Clue 3: The person who loves science fiction books is not in the first house.
# Mapping: science fiction = 0.
s.add(genres[0] != 0)

# To satisfy Clue 4 (direct neighbor relation), mystery cannot be in the first house.
s.add(genres[0] != 2)

# Clue 4: The Desert smoothie lover is directly left of the person who loves mystery books.
# Mapping: desert = 0.
# For house index 1: if house2 has mystery then house1 must have desert.
s.add(Implies(genres[1] == 2, smoothies[0] == 0))
# For house index 2: if house3 has mystery then house2 must have desert.
s.add(Implies(genres[2] == 2, smoothies[1] == 0))

# Clue 1: The person who likes Cherry smoothies is somewhere to the left of the person who loves mystery books.
# Mapping: cherry = 2.
# If mystery is in house 2, then house 1 must have cherry.
s.add(Implies(genres[1] == 2, smoothies[0] == 2))
# If mystery is in house 3, then either house 1 or house 2 must have cherry.
s.add(Implies(genres[2] == 2, Or(smoothies[0] == 2, smoothies[1] == 2)))

# Check for a solution
if s.check() == sat:
    m = s.model()
    solution_rows = []
    for i in range(num_houses):
        house_num = str(i + 1)
        name_val = names_map[m[names[i]].as_long()]
        smoothie_val = smoothies_map[m[smoothies[i]].as_long()]
        genre_val = genres_map[m[genres[i]].as_long()]
        solution_rows.append([house_num, name_val, smoothie_val, genre_val])
    
    solution = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "BookGenre"],
            "rows": solution_rows
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print(json.dumps({"solution": "No solution found"}))