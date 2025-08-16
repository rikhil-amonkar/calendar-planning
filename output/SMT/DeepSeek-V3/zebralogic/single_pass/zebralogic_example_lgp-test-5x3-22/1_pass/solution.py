from z3 import *

# Create a solver instance
s = Solver()

# Define the houses
houses = [1, 2, 3, 4, 5]

# Define the attributes
names = ["Arnold", "Eric", "Bob", "Peter", "Alice"]
smoothies = ["desert", "watermelon", "lime", "cherry", "dragonfruit"]
nationalities = ["german", "swede", "norwegian", "dane", "brit"]

# Create variables for each attribute in each house
name = {h: String(f"name_{h}") for h in houses}
smoothie = {h: String(f"smoothie_{h}") for h in houses}
nationality = {h: String(f"nationality_{h}") for h in houses}

# Add constraints that each attribute is one of the possible values
for h in houses:
    s.add(Or([name[h] == n for n in names]))
    s.add(Or([smoothie[h] == sm for sm in smoothies]))
    s.add(Or([nationality[h] == nat for nat in nationalities]))

# Add uniqueness constraints
for attr in [name, smoothie, nationality]:
    for h1 in houses:
        for h2 in houses:
            if h1 < h2:
                s.add(attr[h1] != attr[h2])

# Clue 2: The Dragonfruit smoothie lover is in the second house.
s.add(smoothie[2] == "dragonfruit")

# Clue 1: The Dragonfruit smoothie lover is somewhere to the left of Eric.
# Since dragonfruit is in house 2, Eric must be in house 3, 4, or 5.
s.add(Or([name[h] == "Eric" for h in [3, 4, 5]]))

# Clue 3: Peter is not in the first house.
s.add(name[1] != "Peter")

# Clue 4: The Dane and the British person are next to each other.
for h in range(1, 5):
    s.add(Or(
        And(nationality[h] == "dane", nationality[h+1] == "brit"),
        And(nationality[h] == "brit", nationality[h+1] == "dane")
    ))

# Clue 5: The Desert smoothie lover is not in the fifth house.
s.add(smoothie[5] != "desert")

# Clue 6: The Swedish person is somewhere to the left of the Dragonfruit smoothie lover.
# Dragonfruit is in house 2, so swede must be in house 1.
s.add(nationality[1] == "swede")

# Clue 7: There are two houses between the person who drinks Lime smoothies and the Dane.
# This means if lime is in h, dane is in h+3, or vice versa.
# Possible positions:
# lime in 1, dane in 4
# lime in 2, dane in 5
# But dragonfruit is in 2, so lime can't be in 2 (since all smoothies are unique)
s.add(Or(
    And(smoothie[1] == "lime", nationality[4] == "dane"),
    And(smoothie[2] == "lime", nationality[5] == "dane")
))
# But dragonfruit is in 2, so lime can't be in 2, so only lime in 1, dane in 4
s.add(smoothie[1] == "lime")
s.add(nationality[4] == "dane")

# Clue 8: Bob is the Dane.
# Dane is in house 4, so name[4] is Bob.
s.add(name[4] == "Bob")

# Clue 9: Alice is the Norwegian.
# So for whichever house Alice is in, nationality is norwegian.
for h in houses:
    s.add(Implies(name[h] == "Alice", nationality[h] == "norwegian"))

# Clue 10: Alice is in the third house.
s.add(name[3] == "Alice")
s.add(nationality[3] == "norwegian")

# Clue 11: The Watermelon smoothie lover is in the third house.
s.add(smoothie[3] == "watermelon")

# Now, solve the constraints
if s.check() == sat:
    model = s.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "Nationality"],
            "rows": []
        }
    }
    for h in sorted(houses):
        row = [
            str(h),
            model.eval(name[h]),
            model.eval(smoothie[h]),
            model.eval(nationality[h])
        ]
        solution["solution"]["rows"].append(row)
    print(solution)
else:
    print("No solution found")