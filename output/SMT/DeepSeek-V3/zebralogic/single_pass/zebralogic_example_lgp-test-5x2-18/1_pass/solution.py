import json
from z3 import *

# Create a solver instance
s = Solver()

# Define the houses
houses = [1, 2, 3, 4, 5]

# Define the names and children
names = ["Eric", "Alice", "Peter", "Bob", "Arnold"]
children = ["Timothy", "Meredith", "Samantha", "Fred", "Bella"]

# Create variables for each house's name and child
name_vars = {house: Int(f"name_{house}") for house in houses}
child_vars = {house: Int(f"child_{house}") for house in houses}

# Add constraints that each name and child is unique and within their respective ranges
for house in houses:
    s.add(And(name_vars[house] >= 0, name_vars[house] < len(names)))
    s.add(And(child_vars[house] >= 0, child_vars[house] < len(children)))

s.add(Distinct([name_vars[house] for house in houses]))
s.add(Distinct([child_vars[house] for house in houses]))

# Helper functions to get the index of a name or child
def name_index(name):
    return names.index(name)

def child_index(child):
    return children.index(child)

# Clue 3: The person's child is named Fred is in the second house.
s.add(child_vars[2] == child_index("Fred"))

# Clue 7: The person's child is named Fred is directly left of the person's child is named Bella.
s.add(child_vars[3] == child_index("Bella"))

# Clue 4: There is one house between Alice and the person's child is named Samantha.
# This means Alice is in house X, Samantha's child is in house X+2 or X-2.
# But since houses are 1-5, possible positions are:
# Alice in 1, Samantha in 3
# Alice in 2, Samantha in 4
# Alice in 3, Samantha in 5
# Alice cannot be in 4 or 5 because there's no house +2 from them.
for house in [1, 2, 3]:
    s.add(Implies(name_vars[house] == name_index("Alice"), child_vars[house + 2] == child_index("Samantha")))

# Clue 1: Bob is somewhere to the left of the person's child is named Samantha.
# So Bob's house number is less than the house where child is Samantha.
# We don't know where Samantha is yet, but we can express this as:
for bob_house in houses:
    for samantha_house in houses:
        if bob_house < samantha_house:
            s.add(Implies(
                And(name_vars[bob_house] == name_index("Bob"), child_vars[samantha_house] == child_index("Samantha")),
                bob_house < samantha_house
            ))

# Clue 2: The person who is the mother of Timothy is somewhere to the left of the person's child is named Samantha.
# So the house with child Timothy is left of the house with child Samantha.
for timothy_house in houses:
    for samantha_house in houses:
        if timothy_house < samantha_house:
            s.add(Implies(
                And(child_vars[timothy_house] == child_index("Timothy"), child_vars[samantha_house] == child_index("Samantha")),
                timothy_house < samantha_house
            ))

# Clue 5: Eric is not in the third house.
s.add(name_vars[3] != name_index("Eric"))

# Clue 6: Bob is not in the third house.
s.add(name_vars[3] != name_index("Bob"))

# Clue 8: The person's child is named Samantha is somewhere to the left of Peter.
# So the house with child Samantha is left of the house where name is Peter.
for samantha_house in houses:
    for peter_house in houses:
        if samantha_house < peter_house:
            s.add(Implies(
                And(child_vars[samantha_house] == child_index("Samantha"), name_vars[peter_house] == name_index("Peter")),
                samantha_house < peter_house
            ))

# Check if the solver can find a solution
if s.check() == sat:
    model = s.model()
    
    # Prepare the solution
    solution = {
        "solution": {
            "header": ["House", "Name", "Children"],
            "rows": []
        }
    }
    
    for house in houses:
        name_idx = model.evaluate(name_vars[house]).as_long()
        child_idx = model.evaluate(child_vars[house]).as_long()
        solution["solution"]["rows"].append([
            str(house),
            names[name_idx],
            children[child_idx]
        ])
    
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")