from z3 import *

# Create a solver instance
s = Solver()

# Define the houses
houses = [1, 2, 3]

# Define the attributes
names = ["Eric", "Peter", "Arnold"]
mothers = ["Holly", "Aniya", "Janelle"]
foods = ["pizza", "grilled cheese", "spaghetti"]

# Create variables for each attribute in each house
name = {h: String(f"name_{h}") for h in houses}
mother = {h: String(f"mother_{h}") for h in houses}
food = {h: String(f"food_{h}") for h in houses}

# Add constraints that each attribute is one of the possible values
for h in houses:
    s.add(Or([name[h] == n for n in names]))
    s.add(Or([mother[h] == m for m in mothers]))
    s.add(Or([food[h] == f for f in foods]))

# Add constraints that all attributes are distinct in each category
s.add(Distinct([name[h] for h in houses]))
s.add(Distinct([mother[h] for h in houses]))
s.add(Distinct([food[h] for h in houses]))

# Clue 1: The person who loves the spaghetti eater and Peter are next to each other.
# This means Peter is next to the house where food is spaghetti.
for h in houses:
    if h == 1:
        s.add(Implies(food[h] == "spaghetti", name[h+1] == "Peter"))
        s.add(Implies(name[h] == "Peter", food[h+1] == "spaghetti"))
    elif h == 3:
        s.add(Implies(food[h] == "spaghetti", name[h-1] == "Peter"))
        s.add(Implies(name[h] == "Peter", food[h-1] == "spaghetti"))
    else:
        s.add(Implies(food[h] == "spaghetti", Or(name[h-1] == "Peter", name[h+1] == "Peter")))
        s.add(Implies(name[h] == "Peter", Or(food[h-1] == "spaghetti", food[h+1] == "spaghetti")))

# Clue 2: The person who loves eating grilled cheese is directly left of the person whose mother's name is Aniya.
# This means the house with grilled cheese is immediately to the left of the house with mother Aniya.
for h in houses:
    if h < 3:
        s.add(Implies(food[h] == "grilled cheese", mother[h+1] == "Aniya"))
    else:
        s.add(Not(food[h] == "grilled cheese"))  # grilled cheese cannot be in house 3

# Clue 3: The person who loves eating grilled cheese is Eric.
for h in houses:
    s.add(Implies(food[h] == "grilled cheese", name[h] == "Eric"))

# Clue 4: Peter is the person whose mother's name is Holly.
for h in houses:
    s.add(Implies(name[h] == "Peter", mother[h] == "Holly"))

# Check if the solver can find a solution
if s.check() == sat:
    model = s.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Mother", "Food"],
            "rows": []
        }
    }
    for h in sorted(houses):
        row = [
            str(h),
            model.eval(name[h]).as_string(),
            model.eval(mother[h]).as_string(),
            model.eval(food[h]).as_string()
        ]
        solution["solution"]["rows"].append(row)
    # Convert to JSON string
    import json
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")