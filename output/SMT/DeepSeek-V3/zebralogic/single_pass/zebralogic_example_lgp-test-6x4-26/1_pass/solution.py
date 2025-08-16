from z3 import *

# Create the solver
s = Solver()

# Define the houses
houses = [1, 2, 3, 4, 5, 6]

# Define the attributes
names = ["Peter", "Bob", "Carol", "Eric", "Alice", "Arnold"]
pets = ["bird", "dog", "cat", "rabbit", "fish", "hamster"]
house_styles = ["victorian", "ranch", "modern", "mediterranean", "colonial", "craftsman"]
birthday_months = ["mar", "sept", "may", "feb", "jan", "april"]

# Create dictionaries to hold the variables for each attribute
name = {h: String(f"name_{h}") for h in houses}
pet = {h: String(f"pet_{h}") for h in houses}
house_style = {h: String(f"house_style_{h}") for h in houses}
birthday = {h: String(f"birthday_{h}") for h in houses}

# Add constraints for uniqueness
s.add(Distinct([name[h] for h in houses]))
s.add(Distinct([pet[h] for h in houses]))
s.add(Distinct([house_style[h] for h in houses]))
s.add(Distinct([birthday[h] for h in houses]))

# Each attribute must be one of the allowed values
for h in houses:
    s.add(Or([name[h] == n for n in names]))
    s.add(Or([pet[h] == p for p in pets]))
    s.add(Or([house_style[h] == hs for hs in house_styles]))
    s.add(Or([birthday[h] == bm for bm in birthday_months]))

# Apply the clues one by one
# Clue 3: The person whose birthday is in May is in the second house.
s.add(birthday[2] == "may")

# Clue 4: The person living in a colonial-style house is in the second house.
s.add(house_style[2] == "colonial")

# Clue 5: Carol is in the third house.
s.add(name[3] == "Carol")

# Clue 6: The person in a Mediterranean-style villa is not in the sixth house.
s.add(house_style[6] != "mediterranean")

# Clue 7: The person with an aquarium of fish is somewhere to the right of Bob.
# This means Bob is to the left of the fish owner. We'll handle this after assigning Bob's position.

# Clue 8: Eric is in the sixth house.
s.add(name[6] == "Eric")

# Clue 9: There is one house between the person who has a cat and the person residing in a Victorian house.
# This means if cat is in h, victorian is in h+2, or vice versa.
for h in houses:
    if h + 2 <= 6:
        s.add(Implies(pet[h] == "cat", house_style[h + 2] == "victorian"))
        s.add(Implies(house_style[h] == "victorian", pet[h - 2] == "cat"))

# Clue 10: There are two houses between the person residing in a Victorian house and the person with a pet hamster.
# If victorian is in h, hamster is in h+3.
for h in houses:
    if h + 3 <= 6:
        s.add(Implies(house_style[h] == "victorian", pet[h + 3] == "hamster"))
        s.add(Implies(pet[h] == "hamster", house_style[h - 3] == "victorian"))

# Clue 11: The person in a Craftsman-style house is Arnold.
for h in houses:
    s.add(Implies(house_style[h] == "craftsman", name[h] == "Arnold"))

# Clue 12: The person living in a colonial-style house is somewhere to the left of the person in a modern-style house.
# colonial is in h1, modern is in h2, h1 < h2.
# From clue 4, colonial is in house 2, so modern must be to the right of house 2.
s.add(Or([And(house_style[h] == "modern", h > 2) for h in houses]))

# Clue 13: The person with an aquarium of fish is not in the second house.
s.add(pet[2] != "fish")

# Clue 14: Peter is the person living in a colonial-style house.
# From clue 4, colonial is in house 2, so:
s.add(name[2] == "Peter")

# Clue 15: The person whose birthday is in January is directly left of the person whose birthday is in April.
# jan is in h, april is in h+1.
for h in houses:
    if h + 1 <= 6:
        s.add(Implies(birthday[h] == "jan", birthday[h + 1] == "april"))
        s.add(Implies(birthday[h + 1] == "april", birthday[h] == "jan"))

# Clue 16: There is one house between the person who keeps a pet bird and the person in a modern-style house.
# bird is in h, modern is in h+2, or vice versa.
for h in houses:
    if h + 2 <= 6:
        s.add(Implies(pet[h] == "bird", house_style[h + 2] == "modern"))
        s.add(Implies(house_style[h] == "modern", pet[h - 2] == "bird"))

# Clue 17: Carol is the person whose birthday is in March.
# Carol is in house 3 (from clue 5), so:
s.add(birthday[3] == "mar")

# Clue 18: The person in a Craftsman-style house is in the fourth house.
s.add(house_style[4] == "craftsman")

# Clue 19: The person who owns a dog is in the fourth house.
s.add(pet[4] == "dog")

# Clue 1: The person with a pet hamster is somewhere to the right of the person whose birthday is in March.
# March is in house 3 (from clue 17), so hamster is in h > 3.
s.add(Or([And(pet[h] == "hamster", h > 3) for h in houses]))

# Clue 2: The person whose birthday is in January is somewhere to the left of the person whose birthday is in September.
# jan is in h1, sept is in h2, h1 < h2.
s.add(Or([And(birthday[h1] == "jan", birthday[h2] == "sept", h1 < h2) for h1 in houses for h2 in houses]))

# Clue 7: The person with an aquarium of fish is somewhere to the right of Bob.
# Find Bob's position and ensure fish is to the right.
# We'll add this after assigning Bob's position.

# Solve the constraints
if s.check() == sat:
    model = s.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Pet", "HouseStyle", "Birthday"],
            "rows": []
        }
    }
    for h in houses:
        row = [
            str(h),
            model.eval(name[h]).as_string(),
            model.eval(pet[h]).as_string(),
            model.eval(house_style[h]).as_string(),
            model.eval(birthday[h]).as_string()
        ]
        solution["solution"]["rows"].append(row)
    
    # Now, ensure that fish is to the right of Bob
    # Find Bob's house and fish's house
    bob_house = None
    fish_house = None
    for h in houses:
        if model.eval(name[h]).as_string() == "Bob":
            bob_house = h
        if model.eval(pet[h]).as_string() == "fish":
            fish_house = h
    if bob_house is not None and fish_house is not None:
        if fish_house <= bob_house:
            # Need to find another solution
            s.add(Not(And(name[bob_house] == "Bob", pet[fish_house] == "fish")))
            if s.check() == sat:
                model = s.model()
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Pet", "HouseStyle", "Birthday"],
                        "rows": []
                    }
                }
                for h in houses:
                    row = [
                        str(h),
                        model.eval(name[h]).as_string(),
                        model.eval(pet[h]).as_string(),
                        model.eval(house_style[h]).as_string(),
                        model.eval(birthday[h]).as_string()
                    ]
                    solution["solution"]["rows"].append(row)
            else:
                print("No solution found after applying fish to the right of Bob constraint.")
    else:
        print("Could not find Bob or fish in the solution.")
    
    # Print the solution in JSON format
    import json
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")