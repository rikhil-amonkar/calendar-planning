from z3 import *

# Create the solver
s = Solver()

# Define the houses
houses = [1, 2, 3, 4, 5]

# Define the attributes
names = ["Alice", "Peter", "Bob", "Eric", "Arnold"]
smoothies = ["lime", "dragonfruit", "desert", "watermelon", "cherry"]
animals = ["horse", "dog", "bird", "fish", "cat"]
nationalities = ["german", "swede", "norwegian", "brit", "dane"]

# Create dictionaries to hold the variables for each attribute
name = {h: String(f"name_{h}") for h in houses}
smoothie = {h: String(f"smoothie_{h}") for h in houses}
animal = {h: String(f"animal_{h}") for h in houses}
nationality = {h: String(f"nationality_{h}") for h in houses}

# Add constraints that each attribute is one of the given options
for h in houses:
    s.add(Or([name[h] == n for n in names]))
    s.add(Or([smoothie[h] == sm for sm in smoothies]))
    s.add(Or([animal[h] == a for a in animals]))
    s.add(Or([nationality[h] == nat for nat in nationalities]))

# Add uniqueness constraints for each attribute
for attr in [name, smoothie, animal, nationality]:
    for h1 in houses:
        for h2 in houses:
            if h1 < h2:
                s.add(attr[h1] != attr[h2])

# Add constraints based on the clues
# Clue 11: The person who keeps horses is in the third house.
s.add(animal[3] == "horse")

# Clue 3: The Dane is the person who keeps horses.
s.add(nationality[3] == "dane")

# Clue 10: The Desert smoothie lover is the dog owner.
for h in houses:
    s.add(Implies(smoothie[h] == "desert", animal[h] == "dog"))

# Clue 5: The dog owner is directly left of the person who drinks Lime smoothies.
for h in houses:
    if h < 5:
        s.add(Implies(animal[h] == "dog", smoothie[h+1] == "lime"))

# Clue 1: The Swedish person is directly left of the dog owner.
for h in houses:
    if h < 5:
        s.add(Implies(nationality[h] == "swede", animal[h+1] == "dog"))

# Clue 2: There are two houses between the dog owner and the British person.
for h in houses:
    if h + 3 <= 5:
        s.add(Implies(animal[h] == "dog", nationality[h+3] == "brit"))

# Clue 4: The bird keeper is somewhere to the right of the cat lover.
# We'll find the positions where cat is left of bird
for h_cat in houses:
    for h_bird in houses:
        if h_bird > h_cat:
            s.add(Implies(And(animal[h_cat] == "cat", animal[h_bird] == "bird"), h_bird > h_cat))

# Clue 6: Eric is the cat lover.
for h in houses:
    s.add(Implies(name[h] == "Eric", animal[h] == "cat"))

# Clue 7: Bob is the bird keeper.
for h in houses:
    s.add(Implies(name[h] == "Bob", animal[h] == "bird"))

# Clue 9: The bird keeper is the Watermelon smoothie lover.
for h in houses:
    s.add(Implies(animal[h] == "bird", smoothie[h] == "watermelon"))

# Clue 8: The person who likes Cherry smoothies is directly left of Peter.
for h in houses:
    if h < 5:
        s.add(Implies(smoothie[h] == "cherry", name[h+1] == "Peter"))

# Clue 12: The Norwegian is Alice.
for h in houses:
    s.add(Implies(nationality[h] == "norwegian", name[h] == "Alice"))

# Solve the problem
if s.check() == sat:
    model = s.model()
    
    # Prepare the solution in the required JSON format
    solution = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "Animal", "Nationality"],
            "rows": []
        }
    }
    
    for h in houses:
        row = [
            str(h),
            model.eval(name[h]).as_string(),
            model.eval(smoothie[h]).as_string(),
            model.eval(animal[h]).as_string(),
            model.eval(nationality[h]).as_string()
        ]
        solution["solution"]["rows"].append(row)
    
    # Convert to JSON
    import json
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")