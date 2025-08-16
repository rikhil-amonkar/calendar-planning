from z3 import *

# Create a solver instance
s = Solver()

# Define the houses
houses = [1, 2, 3, 4, 5]

# Define the attributes
names = ["Alice", "Bob", "Arnold", "Eric", "Peter"]
vacations = ["cruise", "city", "camping", "beach", "mountain"]
children = ["Bella", "Samantha", "Fred", "Meredith", "Timothy"]
nationalities = ["dane", "norwegian", "brit", "german", "swede"]

# Create dictionaries to hold the variables for each attribute per house
name = {h: Int(f"name_{h}") for h in houses}
vacation = {h: Int(f"vacation_{h}") for h in houses}
child = {h: Int(f"child_{h}") for h in houses}
nationality = {h: Int(f"nationality_{h}") for h in houses}

# Add constraints that each attribute is within the range of the list indices
for h in houses:
    s.add(name[h] >= 0, name[h] < len(names))
    s.add(vacation[h] >= 0, vacation[h] < len(vacations))
    s.add(child[h] >= 0, child[h] < len(children))
    s.add(nationality[h] >= 0, nationality[h] < len(nationalities))

# All attributes in each category must be distinct
for attr in [name, vacation, child, nationality]:
    s.add(Distinct([attr[h] for h in houses]))

# Clue 1: The Norwegian is Peter.
# Find the index of "Peter" in names and "norwegian" in nationalities
peter_idx = names.index("Peter")
norwegian_idx = nationalities.index("norwegian")
for h in houses:
    s.add(Implies(nationality[h] == norwegian_idx, name[h] == peter_idx))

# Clue 2: The Swedish person is the person whose child is named Bella.
swede_idx = nationalities.index("swede")
bella_idx = children.index("Bella")
for h in houses:
    s.add(Implies(nationality[h] == swede_idx, child[h] == bella_idx))

# Clue 3: The person who loves beach vacations is directly left of the person whose child is named Samantha.
beach_idx = vacations.index("beach")
samantha_idx = children.index("Samantha")
for h in houses[:-1]:
    s.add(Implies(vacation[h] == beach_idx, child[h+1] == samantha_idx))

# Clue 4: The person whose child is named Bella is not in the second house.
s.add(child[2] != bella_idx)

# Clue 5: Alice is the British person.
alice_idx = names.index("Alice")
brit_idx = nationalities.index("brit")
for h in houses:
    s.add(Implies(name[h] == alice_idx, nationality[h] == brit_idx))

# Clue 6: The person who likes going on cruises is in the first house.
cruise_idx = vacations.index("cruise")
s.add(vacation[1] == cruise_idx)

# Clue 7: The person whose child is named Meredith is in the fourth house.
meredith_idx = children.index("Meredith")
s.add(child[4] == meredith_idx)

# Clue 8: Eric is not in the fifth house.
eric_idx = names.index("Eric")
s.add(name[5] != eric_idx)

# Clue 9: The Swedish person is somewhere to the right of the Norwegian.
# Find the house of the Norwegian and the Swede, and ensure Swede is to the right
norwegian_house = Int("norwegian_house")
swede_house = Int("swede_house")
s.add(Or([And(nationality[h] == norwegian_idx, norwegian_house == h) for h in houses]))
s.add(Or([And(nationality[h] == swede_idx, swede_house == h) for h in houses]))
s.add(swede_house > norwegian_house)

# Clue 10: There is one house between the person whose child is named Fred and the person who prefers city breaks.
fred_idx = children.index("Fred")
city_idx = vacations.index("city")
for h in houses:
    if h + 2 <= 5:
        s.add(Implies(child[h] == fred_idx, vacation[h+2] == city_idx))
    if h - 2 >= 1:
        s.add(Implies(vacation[h] == city_idx, child[h-2] == fred_idx))

# Clue 11: Bob is the person who enjoys camping trips.
bob_idx = names.index("Bob")
camping_idx = vacations.index("camping")
for h in houses:
    s.add(Implies(name[h] == bob_idx, vacation[h] == camping_idx))

# Clue 12: The Dane is in the fifth house.
dane_idx = nationalities.index("dane")
s.add(nationality[5] == dane_idx)

# Clue 13: The person who enjoys camping trips is not in the fifth house.
s.add(vacation[5] != camping_idx)

# Check if the solver can find a solution
if s.check() == sat:
    m = s.model()
    
    # Prepare the solution
    solution = {
        "solution": {
            "header": ["House", "Name", "Vacation", "Children", "Nationality"],
            "rows": []
        }
    }
    
    for h in houses:
        # Get the index for each attribute
        n = m.evaluate(name[h]).as_long()
        v = m.evaluate(vacation[h]).as_long()
        c = m.evaluate(child[h]).as_long()
        nat = m.evaluate(nationality[h]).as_long()
        
        # Append the row with the actual values
        solution["solution"]["rows"].append([
            str(h),
            names[n],
            vacations[v],
            children[c],
            nationalities[nat]
        ])
    
    # Print the solution as JSON
    import json
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")