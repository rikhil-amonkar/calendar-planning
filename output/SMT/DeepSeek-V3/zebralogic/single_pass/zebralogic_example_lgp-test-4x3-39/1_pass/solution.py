from z3 import *

# Create a solver instance
s = Solver()

# Define the houses
houses = [1, 2, 3, 4]

# Define the attributes
names = ["Eric", "Alice", "Peter", "Arnold"]
hair_colors = ["blonde", "black", "red", "brown"]
sports = ["swimming", "soccer", "basketball", "tennis"]

# Create variables for each attribute in each house
name_vars = {house: String(f"name_{house}") for house in houses}
hair_vars = {house: String(f"hair_{house}") for house in houses}
sport_vars = {house: String(f"sport_{house}") for house in houses}

# Add constraints that each attribute is one of the possible values
for house in houses:
    s.add(Or([name_vars[house] == name for name in names]))
    s.add(Or([hair_vars[house] == color for color in hair_colors]))
    s.add(Or([sport_vars[house] == sport for sport in sports]))

# Add uniqueness constraints for each attribute across houses
for attr in [name_vars, hair_vars, sport_vars]:
    for i in houses:
        for j in houses:
            if i < j:
                s.add(attr[i] != attr[j])

# Clue 1: The person who loves soccer is not in the second house.
s.add(sport_vars[2] != "soccer")

# Clue 2: Eric is the person who has blonde hair.
for house in houses:
    s.add(Implies(name_vars[house] == "Eric", hair_vars[house] == "blonde"))

# Clue 3: The person who has blonde hair is somewhere to the right of the person who loves basketball.
# This means there exists a house with basketball to the left of a house with blonde hair.
s.add(Or(
    And(sport_vars[1] == "basketball", Or(hair_vars[2] == "blonde", hair_vars[3] == "blonde", hair_vars[4] == "blonde")),
    And(sport_vars[2] == "basketball", Or(hair_vars[3] == "blonde", hair_vars[4] == "blonde")),
    And(sport_vars[3] == "basketball", hair_vars[4] == "blonde")
))

# Clue 4: The person who has black hair is the person who loves tennis.
for house in houses:
    s.add(Implies(hair_vars[house] == "black", sport_vars[house] == "tennis"))

# Clue 5: Arnold is somewhere to the left of the person who has red hair.
# This means there exists a house with Arnold to the left of a house with red hair.
s.add(Or(
    And(name_vars[1] == "Arnold", Or(hair_vars[2] == "red", hair_vars[3] == "red", hair_vars[4] == "red")),
    And(name_vars[2] == "Arnold", Or(hair_vars[3] == "red", hair_vars[4] == "red")),
    And(name_vars[3] == "Arnold", hair_vars[4] == "red")
))

# Clue 6: Alice is the person who loves swimming.
for house in houses:
    s.add(Implies(name_vars[house] == "Alice", sport_vars[house] == "swimming"))

# Clue 7: The person who has red hair is directly left of the person who has black hair.
# This means red is in house n, black is in house n+1
s.add(Or(
    And(hair_vars[1] == "red", hair_vars[2] == "black"),
    And(hair_vars[2] == "red", hair_vars[3] == "black"),
    And(hair_vars[3] == "red", hair_vars[4] == "black")
))

# Check if the problem is satisfiable
if s.check() == sat:
    model = s.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "HairColor", "FavoriteSport"],
            "rows": []
        }
    }
    for house in sorted(houses):
        name = model.eval(name_vars[house])
        hair = model.eval(hair_vars[house])
        sport = model.eval(sport_vars[house])
        solution["solution"]["rows"].append([str(house), str(name), str(hair), str(sport)])
    print(solution)
else:
    print("No solution found")