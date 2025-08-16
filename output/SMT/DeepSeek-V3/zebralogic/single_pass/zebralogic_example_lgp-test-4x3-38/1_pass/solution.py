from z3 import *

# Create a solver instance
s = Solver()

# Define the houses
houses = [1, 2, 3, 4]

# Define the variables for each attribute
name = {h: String(f"name_{h}") for h in houses}
mother = {h: String(f"mother_{h}") for h in houses}
flower = {h: String(f"flower_{h}") for h in houses}

# Define the possible values for each attribute
names = ["Alice", "Peter", "Arnold", "Eric"]
mothers = ["Holly", "Kailyn", "Janelle", "Aniya"]
flowers = ["carnations", "roses", "lilies", "daffodils"]

# Add constraints that each attribute is unique across houses
for h in houses:
    s.add(Or([name[h] == n for n in names]))
    s.add(Or([mother[h] == m for m in mothers]))
    s.add(Or([flower[h] == f for f in flowers]))

for i in range(len(names)):
    for j in range(i + 1, len(names)):
        s.add(name[houses[i]] != name[houses[j]])
        s.add(mother[houses[i]] != mother[houses[j]])
        s.add(flower[houses[i]] != flower[houses[j]])

# Clue 8: Alice is in the third house.
s.add(name[3] == "Alice")

# Clue 1: Alice is the person whose mother's name is Kailyn.
s.add(mother[3] == "Kailyn")

# Clue 5: Arnold is the person whose mother's name is Holly.
for h in houses:
    s.add(Implies(name[h] == "Arnold", mother[h] == "Holly"))

# Clue 6: The person who loves carnations is somewhere to the right of the person whose mother's name is Holly.
# First find the house where mother is Holly (Arnold's house)
holly_house = Int("holly_house")
s.add(Or([And(mother[h] == "Holly", holly_house == h) for h in houses]))
carnations_house = Int("carnations_house")
s.add(Or([And(flower[h] == "carnations", carnations_house == h) for h in houses]))
s.add(carnations_house > holly_house)

# Clue 2: The person whose mother's name is Janelle is somewhere to the right of Arnold.
# Arnold is in holly_house
janelle_house = Int("janelle_house")
s.add(Or([And(mother[h] == "Janelle", janelle_house == h) for h in houses]))
s.add(janelle_house > holly_house)

# Clue 3: Peter is somewhere to the right of the person who loves carnations.
peter_house = Int("peter_house")
s.add(Or([And(name[h] == "Peter", peter_house == h) for h in houses]))
s.add(peter_house > carnations_house)

# Clue 4: Eric is the person who loves a bouquet of daffodils.
for h in houses:
    s.add(Implies(name[h] == "Eric", flower[h] == "daffodils"))

# Clue 7: The person who loves the bouquet of lilies is directly left of Alice.
# Alice is in house 3, so lilies are in house 2
s.add(flower[2] == "lilies")

# Solve the constraints
if s.check() == sat:
    model = s.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Mother", "Flower"],
            "rows": []
        }
    }
    for h in houses:
        row = [
            str(h),
            model.eval(name[h]).as_string(),
            model.eval(mother[h]).as_string(),
            model.eval(flower[h]).as_string()
        ]
        solution["solution"]["rows"].append(row)
    print(solution)
else:
    print("No solution found")