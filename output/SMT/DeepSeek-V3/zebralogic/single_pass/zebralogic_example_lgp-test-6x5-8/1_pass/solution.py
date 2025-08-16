import json
from z3 import *

# Initialize the solver
s = Solver()

# Define the houses
houses = [1, 2, 3, 4, 5, 6]

# Define the attributes
names = ["Arnold", "Peter", "Bob", "Eric", "Carol", "Alice"]
animals = ["horse", "rabbit", "fish", "cat", "bird", "dog"]
occupations = ["engineer", "nurse", "lawyer", "teacher", "artist", "doctor"]
sports = ["basketball", "volleyball", "soccer", "tennis", "baseball", "swimming"]
heights = ["average", "tall", "short", "very short", "very tall", "super tall"]

# Create variables for each attribute in each house
name = {h: String(f"name_{h}") for h in houses}
animal = {h: String(f"animal_{h}") for h in houses}
occupation = {h: String(f"occupation_{h}") for h in houses}
sport = {h: String(f"sport_{h}") for h in houses}
height = {h: String(f"height_{h}") for h in houses}

# Each attribute must be one of the allowed values
for h in houses:
    s.add(Or([name[h] == n for n in names]))
    s.add(Or([animal[h] == a for a in animals]))
    s.add(Or([occupation[h] == o for o in occupations]))
    s.add(Or([sport[h] == sp for sp in sports]))
    s.add(Or([height[h] == ht for ht in heights]))

# All attributes in each house must be unique
for attr in [name, animal, occupation, sport, height]:
    for h1 in houses:
        for h2 in houses:
            if h1 < h2:
                s.add(attr[h1] != attr[h2])

# Apply the clues
# Clue 1: The person who is an engineer is the dog owner.
for h in houses:
    s.add(Implies(occupation[h] == "engineer", animal[h] == "dog"))

# Clue 2: The person who has an average height is somewhere to the left of the person who is short.
average_house = Int("average_house")
short_house = Int("short_house")
s.add(And(average_house >= 1, average_house <= 6))
s.add(And(short_house >= 1, short_house <= 6))
s.add(average_house < short_house)
for h in houses:
    s.add(Implies(height[h] == "average", average_house == h))
    s.add(Implies(height[h] == "short", short_house == h))

# Clue 3: The person who has an average height is directly left of the rabbit owner.
for h in range(1, 6):
    s.add(Implies(height[h] == "average", animal[h+1] == "rabbit"))

# Clue 4: The person who is tall is somewhere to the left of the person who is very short.
tall_house = Int("tall_house")
very_short_house = Int("very_short_house")
s.add(And(tall_house >= 1, tall_house <= 6))
s.add(And(very_short_house >= 1, very_short_house <= 6))
s.add(tall_house < very_short_house)
for h in houses:
    s.add(Implies(height[h] == "tall", tall_house == h))
    s.add(Implies(height[h] == "very short", very_short_house == h))

# Clue 5: Arnold is the cat lover.
for h in houses:
    s.add(Implies(name[h] == "Arnold", animal[h] == "cat"))

# Clue 6: The person who keeps horses is the person who is a teacher.
for h in houses:
    s.add(Implies(animal[h] == "horse", occupation[h] == "teacher"))

# Clue 7: Carol is the person who loves soccer.
for h in houses:
    s.add(Implies(name[h] == "Carol", sport[h] == "soccer"))

# Clue 8: The person who is tall is the person who loves volleyball.
for h in houses:
    s.add(Implies(height[h] == "tall", sport[h] == "volleyball"))

# Clue 9: The person who is a lawyer is in the fifth house.
s.add(occupation[5] == "lawyer")

# Clue 10: The person who loves tennis is the person who is a teacher.
for h in houses:
    s.add(Implies(sport[h] == "tennis", occupation[h] == "teacher"))

# Clue 11: The person who has an average height is the person who loves swimming.
for h in houses:
    s.add(Implies(height[h] == "average", sport[h] == "swimming"))

# Clue 12: The person who loves baseball is directly left of the person who is an engineer.
for h in range(1, 6):
    s.add(Implies(sport[h] == "baseball", occupation[h+1] == "engineer"))

# Clue 13: Peter is the person who is a nurse.
for h in houses:
    s.add(Implies(name[h] == "Peter", occupation[h] == "nurse"))

# Clue 14: Bob is somewhere to the right of the person who is an artist.
artist_house = Int("artist_house")
bob_house = Int("bob_house")
s.add(And(artist_house >= 1, artist_house <= 6))
s.add(And(bob_house >= 1, bob_house <= 6))
s.add(artist_house < bob_house)
for h in houses:
    s.add(Implies(occupation[h] == "artist", artist_house == h))
    s.add(Implies(name[h] == "Bob", bob_house == h))

# Clue 15: The person who is a teacher is directly left of the person who loves soccer.
for h in range(1, 6):
    s.add(Implies(occupation[h] == "teacher", sport[h+1] == "soccer"))

# Clue 16: The rabbit owner is Alice.
for h in houses:
    s.add(Implies(animal[h] == "rabbit", name[h] == "Alice"))

# Clue 17: The fish enthusiast is Carol.
for h in houses:
    s.add(Implies(animal[h] == "fish", name[h] == "Carol"))

# Clue 18: The person who loves baseball is in the first house.
s.add(sport[1] == "baseball")

# Clue 19: The cat lover is somewhere to the right of the person who is very short.
cat_house = Int("cat_house")
s.add(And(cat_house >= 1, cat_house <= 6))
s.add(very_short_house < cat_house)
for h in houses:
    s.add(Implies(animal[h] == "cat", cat_house == h))

# Clue 20: The person who is super tall is in the fifth house.
s.add(height[5] == "super tall")

# Solve the problem
if s.check() == sat:
    model = s.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Animal", "Occupation", "FavoriteSport", "Height"],
            "rows": []
        }
    }
    for h in houses:
        row = [
            str(h),
            str(model.eval(name[h])),
            str(model.eval(animal[h])),
            str(model.eval(occupation[h])),
            str(model.eval(sport[h])),
            str(model.eval(height[h]))
        ]
        solution["solution"]["rows"].append(row)
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")