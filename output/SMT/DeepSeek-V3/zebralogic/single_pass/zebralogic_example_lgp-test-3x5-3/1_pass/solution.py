from z3 import *

# Create a solver instance
s = Solver()

# Define the attributes for each house (1, 2, 3)
houses = [1, 2, 3]

# Define the possible values for each attribute
names = ["Eric", "Peter", "Arnold"]
smoothies = ["cherry", "watermelon", "desert"]
flowers = ["carnations", "lilies", "daffodils"]
animals = ["cat", "horse", "bird"]
hobbies = ["photography", "cooking", "gardening"]

# Create dictionaries to hold the variables for each attribute
name = {h: String(f"name_{h}") for h in houses}
smoothie = {h: String(f"smoothie_{h}") for h in houses}
flower = {h: String(f"flower_{h}") for h in houses}
animal = {h: String(f"animal_{h}") for h in houses}
hobby = {h: String(f"hobby_{h}") for h in houses}

# Add constraints that each attribute must be one of the possible values
for h in houses:
    s.add(Or([name[h] == n for n in names]))
    s.add(Or([smoothie[h] == sm for sm in smoothies]))
    s.add(Or([flower[h] == fl for fl in flowers]))
    s.add(Or([animal[h] == an for an in animals]))
    s.add(Or([hobby[h] == ho for ho in hobbies]))

# Add constraints that all attributes in each category are distinct
s.add(Distinct([name[h] for h in houses]))
s.add(Distinct([smoothie[h] for h in houses]))
s.add(Distinct([flower[h] for h in houses]))
s.add(Distinct([animal[h] for h in houses]))
s.add(Distinct([hobby[h] for h in houses]))

# Clue 1: The person who keeps horses and the photography enthusiast are next to each other.
for h in houses:
    if h == 1:
        s.add(Or(
            And(animal[h] == "horse", hobby[h+1] == "photography"),
            And(animal[h+1] == "horse", hobby[h] == "photography")
        ))
    elif h == 2:
        s.add(Or(
            And(animal[h] == "horse", hobby[h-1] == "photography"),
            And(animal[h-1] == "horse", hobby[h] == "photography"),
            And(animal[h] == "horse", hobby[h+1] == "photography"),
            And(animal[h+1] == "horse", hobby[h] == "photography")
        ))
    elif h == 3:
        s.add(Or(
            And(animal[h] == "horse", hobby[h-1] == "photography"),
            And(animal[h-1] == "horse", hobby[h] == "photography")
        ))

# Clue 2: The bird keeper is the person who likes Cherry smoothies.
for h in houses:
    s.add(Implies(animal[h] == "bird", smoothie[h] == "cherry"))

# Clue 3: The person who loves cooking is the Desert smoothie lover.
for h in houses:
    s.add(Implies(hobby[h] == "cooking", smoothie[h] == "desert"))

# Clue 4: The person who enjoys gardening is the person who loves a carnations arrangement.
for h in houses:
    s.add(Implies(hobby[h] == "gardening", flower[h] == "carnations"))

# Clue 5: The person who loves cooking is directly left of Peter.
for h in houses:
    if h < 3:
        s.add(Implies(hobby[h] == "cooking", name[h+1] == "Peter"))
    else:
        s.add(Not(hobby[h] == "cooking"))  # cooking cannot be in the last house if Peter is to its right

# Clue 6: The person who loves a bouquet of daffodils is the Desert smoothie lover.
for h in houses:
    s.add(Implies(flower[h] == "daffodils", smoothie[h] == "desert"))

# Clue 7: The Watermelon smoothie lover is the person who keeps horses.
for h in houses:
    s.add(Implies(smoothie[h] == "watermelon", animal[h] == "horse"))

# Clue 8: The photography enthusiast is Eric.
for h in houses:
    s.add(Implies(hobby[h] == "photography", name[h] == "Eric"))

# Solve the constraints
if s.check() == sat:
    model = s.model()
    
    # Prepare the solution in the required JSON format
    solution = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "Flower", "Animal", "Hobby"],
            "rows": []
        }
    }
    
    for h in houses:
        row = [
            str(h),
            model.eval(name[h]),
            model.eval(smoothie[h]),
            model.eval(flower[h]),
            model.eval(animal[h]),
            model.eval(hobby[h])
        ]
        solution["solution"]["rows"].append(row)
    
    # Convert to JSON string (though in Python it's a dictionary, we'll print it as JSON)
    import json
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")