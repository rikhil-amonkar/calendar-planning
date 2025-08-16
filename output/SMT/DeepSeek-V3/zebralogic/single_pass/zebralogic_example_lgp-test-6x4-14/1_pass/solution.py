from z3 import *

# Create a solver instance
s = Solver()

# Define the houses
houses = [1, 2, 3, 4, 5, 6]

# Define the attributes
names = ["Eric", "Bob", "Peter", "Alice", "Arnold", "Carol"]
car_models = ["ford f150", "honda civic", "toyota camry", "tesla model 3", "chevrolet silverado", "bmw 3 series"]
mothers = ["Sarah", "Penny", "Holly", "Aniya", "Kailyn", "Janelle"]
hobbies = ["photography", "cooking", "knitting", "gardening", "woodworking", "painting"]

# Create variables for each attribute in each house
name = {h: String(f"name_{h}") for h in houses}
car_model = {h: String(f"car_model_{h}") for h in houses}
mother = {h: String(f"mother_{h}") for h in houses}
hobby = {h: String(f"hobby_{h}") for h in houses}

# Add constraints that each attribute in each house must be one of the allowed values
for h in houses:
    s.add(Or([name[h] == n for n in names]))
    s.add(Or([car_model[h] == c for c in car_models]))
    s.add(Or([mother[h] == m for m in mothers]))
    s.add(Or([hobby[h] == o for o in hobbies]))

# Add constraints that all attributes in each category are distinct
s.add(Distinct([name[h] for h in houses]))
s.add(Distinct([car_model[h] for h in houses]))
s.add(Distinct([mother[h] for h in houses]))
s.add(Distinct([hobby[h] for h in houses]))

# Clue 1: The person who owns a Toyota Camry is in the sixth house.
s.add(car_model[6] == "toyota camry")

# Clue 2: Carol is the photography enthusiast.
s.add(Exists([h for h in houses], And(name[h] == "Carol", hobby[h] == "photography")))

# Clue 3: The person who owns a Chevrolet Silverado is the person whose mother's name is Aniya.
for h in houses:
    s.add(Implies(car_model[h] == "chevrolet silverado", mother[h] == "Aniya"))

# Clue 4: The person who owns a Chevrolet Silverado is not in the second house.
s.add(car_model[2] != "chevrolet silverado")

# Clue 5: The person who owns a Ford F-150 is the person whose mother's name is Sarah.
for h in houses:
    s.add(Implies(car_model[h] == "ford f150", mother[h] == "Sarah"))

# Clue 6: The person who owns a BMW 3 Series is Bob.
for h in houses:
    s.add(Implies(car_model[h] == "bmw 3 series", name[h] == "Bob"))

# Clue 7: The person whose mother's name is Kailyn is in the sixth house.
s.add(mother[6] == "Kailyn")

# Clue 8: Eric is directly left of the person who enjoys knitting.
for h in range(1, 6):
    s.add(Implies(name[h] == "Eric", hobby[h+1] == "knitting"))

# Clue 9: There is one house between the person whose mother's name is Sarah and the person who owns a Toyota Camry.
# Since Toyota Camry is in house 6, Sarah's mother must be in house 4 (because 4 + 1 + 1 = 6)
s.add(Exists([h for h in houses], And(mother[h] == "Sarah", h + 2 == 6)))

# Clue 10: The person whose mother's name is Penny is somewhere to the right of the person who enjoys knitting.
# This means knitting is to the left of Penny's mother.
for h_knit in houses:
    for h_penny in houses:
        if h_penny > h_knit:
            s.add(Implies(And(hobby[h_knit] == "knitting", mother[h_penny] == "Penny"), h_penny > h_knit))

# Clue 11: The person whose mother's name is Aniya is somewhere to the right of the person who owns a Honda Civic.
# This means Honda Civic is to the left of Aniya's mother.
for h_honda in houses:
    for h_aniya in houses:
        if h_aniya > h_honda:
            s.add(Implies(And(car_model[h_honda] == "honda civic", mother[h_aniya] == "Aniya"), h_aniya > h_honda))

# Clue 12: Alice is somewhere to the right of the person who owns a Ford F-150.
for h_ford in houses:
    for h_alice in houses:
        if h_alice > h_ford:
            s.add(Implies(And(car_model[h_ford] == "ford f150", name[h_alice] == "Alice"), h_alice > h_ford))

# Clue 13: Eric is the person who enjoys gardening.
s.add(Exists([h for h in houses], And(name[h] == "Eric", hobby[h] == "gardening")))

# Clue 14: The woodworking hobbyist is somewhere to the left of the person who enjoys knitting.
for h_wood in houses:
    for h_knit in houses:
        if h_knit > h_wood:
            s.add(Implies(And(hobby[h_wood] == "woodworking", hobby[h_knit] == "knitting"), h_knit > h_wood))

# Clue 15: There is one house between the person whose mother's name is Sarah and the person who loves cooking.
# From clue 9, Sarah's mother is in house 4, so cooking must be in house 6. But house 6's hobby is not yet assigned.
# Wait, house 6's mother is Kailyn, but hobby is not assigned yet.
# So if Sarah is in 4, cooking is in 6.
s.add(Exists([h for h in houses], And(mother[h] == "Sarah", hobby[h+2] == "cooking")))

# Clue 16: The person who owns a Honda Civic is Arnold.
for h in houses:
    s.add(Implies(car_model[h] == "honda civic", name[h] == "Arnold"))

# Clue 17: The person whose mother's name is Holly is directly left of the person who enjoys knitting.
for h in range(1, 6):
    s.add(Implies(mother[h] == "Holly", hobby[h+1] == "knitting"))

# Solve the constraints
if s.check() == sat:
    model = s.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "CarModel", "Mother", "Hobby"],
            "rows": []
        }
    }
    for h in houses:
        row = [
            str(h),
            model.eval(name[h]),
            model.eval(car_model[h]),
            model.eval(mother[h]),
            model.eval(hobby[h])
        ]
        solution["solution"]["rows"].append(row)
    print(solution)
else:
    print("No solution found")