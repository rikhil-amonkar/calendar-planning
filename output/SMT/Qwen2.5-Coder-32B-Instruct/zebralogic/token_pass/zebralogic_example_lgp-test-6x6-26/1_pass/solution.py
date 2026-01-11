from z3 import *

# Define the houses
houses = [1, 2, 3, 4, 5, 6]

# Define the domains for each characteristic
names = ["Peter", "Carol", "Eric", "Alice", "Bob", "Arnold"]
phone_models = ["huawei p50", "google pixel 6", "xiaomi mi 11", "iphone 13", "samsung galaxy s21", "oneplus 9"]
cigars = ["dunhill", "pall mall", "blends", "blue master", "prince", "yellow monster"]
flowers = ["daffodils", "carnations", "roses", "tulips", "lilies", "iris"]
colors = ["yellow", "red", "green", "blue", "white", "purple"]
favorite_sports = ["soccer", "tennis", "basketball", "volleyball", "swimming", "baseball"]

# Create symbolic variables
house_vars = {}
for house in houses:
    house_vars[house] = {
        "name": Int(f"name_{house}"),
        "phone_model": Int(f"phone_model_{house}"),
        "cigar": Int(f"cigar_{house}"),
        "flower": Int(f"flower_{house}"),
        "color": Int(f"color_{house}"),
        "favorite_sport": Int(f"favorite_sport_{house}")
    }

# Create the solver
solver = Solver()

# Add domain constraints
for house in houses:
    solver.add(house_vars[house]["name"] >= 0)
    solver.add(house_vars[house]["name"] < len(names))
    solver.add(house_vars[house]["phone_model"] >= 0)
    solver.add(house_vars[house]["phone_model"] < len(phone_models))
    solver.add(house_vars[house]["cigar"] >= 0)
    solver.add(house_vars[house]["cigar"] < len(cigars))
    solver.add(house_vars[house]["flower"] >= 0)
    solver.add(house_vars[house]["flower"] < len(flowers))
    solver.add(house_vars[house]["color"] >= 0)
    solver.add(house_vars[house]["color"] < len(colors))
    solver.add(house_vars[house]["favorite_sport"] >= 0)
    solver.add(house_vars[house]["favorite_sport"] < len(favorite_sports))

# Add uniqueness constraints
for char in ["name", "phone_model", "cigar", "flower", "color", "favorite_sport"]:
    solver.add(Distinct([house_vars[house][char] for house in houses]))

# Add clue constraints
# Clue 1
solver.add(house_vars[2]["phone_model"] == phone_models.index("oneplus 9"))

# Clue 2
for i in range(len(houses) - 1):
    solver.add(Implies(house_vars[i + 1]["phone_model"] == phone_models.index("xiaomi mi 11"), 
                      Or([house_vars[j + 1]["phone_model"] == phone_models.index("huawei p50") for j in range(i + 1, len(houses))])))

# Clue 3
solver.add(house_vars[houses.index(3)]["flower"] == flowers.index("carnations"))

# Clue 4
for i in range(len(houses) - 1):
    solver.add(Implies(house_vars[i + 1]["color"] == colors.index("purple"), 
                      house_vars[i + 2]["cigar"] == cigars.index("pall mall")))

# Clue 5
for house in houses:
    solver.add(Implies(house_vars[house]["color"] == colors.index("green"), 
                      house_vars[house]["cigar"] == cigars.index("blue master")))

# Clue 6
for i in range(len(houses) - 1):
    solver.add(Or(
        And(house_vars[i + 1]["color"] == colors.index("yellow"), house_vars[i + 2]["color"] == colors.index("blue")),
        And(house_vars[i + 2]["color"] == colors.index("yellow"), house_vars[i + 1]["color"] == colors.index("blue"))
    ))

# Clue 7
for i in range(len(houses) - 1):
    solver.add(Implies(house_vars[i + 1]["phone_model"] == phone_models.index("samsung galaxy s21"), 
                      house_vars[j + 1]["name"] == names.index("Eric") for j in range(i + 1, len(houses))))

# Clue 8
for i in range(len(houses) - 2):
    solver.add(Or(
        And(house_vars[i + 1]["name"] == names.index("Carol"), house_vars[i + 3]["flower"] == flowers.index("daffodils")),
        And(house_vars[i + 3]["name"] == names.index("Carol"), house_vars[i + 1]["flower"] == flowers.index("daffodils"))
    ))

# Clue 9
solver.add(house_vars[houses.index(4)]["cigar"] == cigars.index("prince"))
solver.add(house_vars[houses.index(4)]["favorite_sport"] == favorite_sports.index("basketball"))

# Clue 10
solver.add(house_vars[houses.index(5)]["cigar"] == cigars.index("dunhill"))
solver.add(house_vars[houses.index(5)]["favorite_sport"] == favorite_sports.index("volleyball"))

# Clue 11
solver.add(house_vars[houses.index(6)]["favorite_sport"] == favorite_sports.index("swimming"))
solver.add(house_vars[houses.index(6)]["phone_model"] == phone_models.index("google pixel 6"))

# Clue 12
for i in range(len(houses) - 1):
    solver.add(Implies(house_vars[i + 1]["phone_model"] == phone_models.index("huawei p50"), 
                      house_vars[i + 2]["color"] == colors.index("white")))

# Clue 13
solver.add(Or(
    And(house_vars[2]["phone_model"] == phone_models.index("oneplus 9"), house_vars[1]["flower"] == flowers.index("roses")),
    And(house_vars[1]["phone_model"] == phone_models.index("oneplus 9"), house_vars[2]["flower"] == flowers.index("roses"))
))

# Clue 14
for i in range(len(houses) - 1):
    solver.add(Implies(house_vars[i + 1]["flower"] == flowers.index("iris"), 
                      house_vars[j + 1]["name"] == names.index("Eric") for j in range(i + 1, len(houses))))

# Clue 15
solver.add(house_vars[houses.index(5)]["name"] == names.index("Peter"))
solver.add(house_vars[houses.index(5)]["cigar"] == cigars.index("dunhill"))

# Clue 16
solver.add(house_vars[houses.index(5)]["color"] == colors.index("blue"))

# Clue 17
solver.add(house_vars[houses.index(4)]["name"] == names.index("Bob"))
solver.add(house_vars[houses.index(4)]["flower"] == flowers.index("tulips"))

# Clue 18
solver.add(house_vars[1]["name"] == names.index("Alice"))

# Clue 19
for i in range(len(houses) - 1):
    solver.add(Implies(house_vars[i + 1]["favorite_sport"] == favorite_sports.index("baseball"), 
                      house_vars[i + 2]["cigar"] == cigars.index("blue master")))

# Clue 20
for i in range(len(houses) - 1):
    solver.add(Implies(house_vars[i + 1]["phone_model"] == phone_models.index("google pixel 6"), 
                      house_vars[j + 1]["cigar"] == cigars.index("blends") for j in range(i + 1, len(houses))))

# Clue 21
solver.add(house_vars[houses.index(3)]["name"] == names.index("Carol"))
solver.add(house_vars[houses.index(3)]["favorite_sport"] == favorite_sports.index("soccer"))

# Clue 22
for i in range(len(houses) - 1):
    solver.add(Implies(house_vars[i + 1]["flower"] == flowers.index("carnations"), 
                      house_vars[i + 2]["cigar"] == cigars.index("blends")))

# Clue 23
solver.add(house_vars[houses.index(3)]["cigar"] == cigars.index("blends"))

# Clue 24
for i in range(len(houses) - 1):
    solver.add(Implies(house_vars[i + 1]["flower"] == flowers.index("iris"), 
                      house_vars[j + 1]["name"] == names.index("Eric") for j in range(i + 1, len(houses))))

# Solve the problem
if solver.check() == sat:
    m = solver.model()
    solution = []
    for house in houses:
        name = names[m.eval(house_vars[house]["name"]).as_long()]
        phone_model = phone_models[m.eval(house_vars[house]["phone_model"]).as_long()]
        cigar = cigars[m.eval(house_vars[house]["cigar"]).as_long()]
        flower = flowers[m.eval(house_vars[house]["flower"]).as_long()]
        color = colors[m.eval(house_vars[house]["color"]).as_long()]
        favorite_sport = favorite_sports[m.eval(house_vars[house]["favorite_sport"]).as_long()]
        solution.append([str(house), name, phone_model, cigar, flower, color, favorite_sport])
    
    print({
        "solution": {
            "header": ["House", "Name", "PhoneModel", "Cigar", "Flower", "Color", "FavoriteSport"],
            "rows": solution
        }
    })
else:
    print("No solution found")