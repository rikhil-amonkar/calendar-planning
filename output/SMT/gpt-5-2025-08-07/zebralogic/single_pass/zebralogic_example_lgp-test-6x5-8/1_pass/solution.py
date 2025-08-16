# Solve the logic puzzle with Z3 and print the solution as the required JSON dict
from z3 import *
import json

# Houses indexed 0..5 internally corresponding to 1..6
N = 6
idx = range(N)

# Enumerations
Names = ["Arnold", "Peter", "Bob", "Eric", "Carol", "Alice"]
Animals = ["horse", "rabbit", "fish", "cat", "bird", "dog"]
Occupations = ["engineer", "nurse", "lawyer", "teacher", "artist", "doctor"]
Sports = ["basketball", "volleyball", "soccer", "tennis", "baseball", "swimming"]
Heights = ["average", "tall", "short", "very short", "very tall", "super tall"]

name_map = {v: i for i, v in enumerate(Names)}
animal_map = {v: i for i, v in enumerate(Animals)}
occ_map = {v: i for i, v in enumerate(Occupations)}
sport_map = {v: i for i, v in enumerate(Sports)}
height_map = {v: i for i, v in enumerate(Heights)}

# Variables
name = [Int(f"name_{i+1}") for i in idx]
animal = [Int(f"animal_{i+1}") for i in idx]
occupation = [Int(f"occupation_{i+1}") for i in idx]
sport = [Int(f"sport_{i+1}") for i in idx]
height = [Int(f"height_{i+1}") for i in idx]

s = Solver()

# Domains
for arr in [name, animal, occupation, sport, height]:
    for v in arr:
        s.add(And(v >= 0, v < N))
# All-different per attribute
s.add(Distinct(name))
s.add(Distinct(animal))
s.add(Distinct(occupation))
s.add(Distinct(sport))
s.add(Distinct(height))

def left_of(arrA, valA, arrB, valB):
    return Or([And(arrA[i] == valA, arrB[j] == valB, i < j) for i in idx for j in idx])

def direct_left(arrA, valA, arrB, valB):
    return Or([And(arrA[i] == valA, arrB[i+1] == valB) for i in range(N-1)])

# Clues:

# 1. Engineer is the dog owner.
for i in idx:
    s.add(Implies(occupation[i] == occ_map["engineer"], animal[i] == animal_map["dog"]))

# 2. average left of short.
s.add(left_of(height, height_map["average"], height, height_map["short"]))

# 3. average directly left of rabbit owner.
s.add(direct_left(height, height_map["average"], animal, animal_map["rabbit"]))

# 4. tall left of very short.
s.add(left_of(height, height_map["tall"], height, height_map["very short"]))

# 5. Arnold is the cat lover. (equivalence)
for i in idx:
    s.add((name[i] == name_map["Arnold"]) == (animal[i] == animal_map["cat"]))

# 6. horse <-> teacher
for i in idx:
    s.add((animal[i] == animal_map["horse"]) == (occupation[i] == occ_map["teacher"]))

# 7. Carol <-> soccer
for i in idx:
    s.add((name[i] == name_map["Carol"]) == (sport[i] == sport_map["soccer"]))

# 8. tall <-> volleyball
for i in idx:
    s.add((height[i] == height_map["tall"]) == (sport[i] == sport_map["volleyball"]))

# 9. lawyer is in the fifth house.
s.add(occupation[4] == occ_map["lawyer"])

# 10. tennis <-> teacher
for i in idx:
    s.add((sport[i] == sport_map["tennis"]) == (occupation[i] == occ_map["teacher"]))

# 11. average <-> swimming
for i in idx:
    s.add((height[i] == height_map["average"]) == (sport[i] == sport_map["swimming"]))

# 12. baseball directly left of engineer.
s.add(direct_left(sport, sport_map["baseball"], occupation, occ_map["engineer"]))

# 13. Peter <-> nurse
for i in idx:
    s.add((name[i] == name_map["Peter"]) == (occupation[i] == occ_map["nurse"]))

# 14. Bob to the right of artist.
s.add(left_of(occupation, occ_map["artist"], name, name_map["Bob"]))

# 15. teacher directly left of soccer lover.
s.add(direct_left(occupation, occ_map["teacher"], sport, sport_map["soccer"]))

# 16. rabbit <-> Alice
for i in idx:
    s.add((animal[i] == animal_map["rabbit"]) == (name[i] == name_map["Alice"]))

# 17. fish <-> Carol
for i in idx:
    s.add((animal[i] == animal_map["fish"]) == (name[i] == name_map["Carol"]))

# 18. baseball is in the first house.
s.add(sport[0] == sport_map["baseball"])

# 19. cat lover to the right of very short.
s.add(left_of(height, height_map["very short"], animal, animal_map["cat"]))

# 20. super tall is in the fifth house.
s.add(height[4] == height_map["super tall"])

assert s.check() == sat
m = s.model()

# Build the output
rows = []
for i in idx:
    rows.append([
        str(i+1),
        Names[m[name[i]].as_long()],
        Animals[m[animal[i]].as_long()],
        Occupations[m[occupation[i]].as_long()],
        Sports[m[sport[i]].as_long()],
        Heights[m[height[i]].as_long()],
    ])

solution = {
  "solution": {
    "header": ["House", "Name", "Animal", "Occupation", "FavoriteSport", "Height"],
    "rows": rows
  }
}

print(json.dumps(solution, indent=2))