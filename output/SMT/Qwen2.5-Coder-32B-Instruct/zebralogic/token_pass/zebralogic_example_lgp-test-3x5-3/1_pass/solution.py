from z3 import *

# Define the variables for each house
house_names = ["House1", "House2", "House3"]
names = ["Eric", "Peter", "Arnold"]
smoothies = ["cherry", "watermelon", "desert"]
flowers = ["carnations", "lilies", "daffodils"]
animals = ["cat", "horse", "bird"]
hobbies = ["photography", "cooking", "gardening"]

# Create Z3 variables
house_vars = {}
for house in house_names:
    house_vars[house] = {
        "name": Int(f"{house}_name"),
        "smoothie": Int(f"{house}_smoothie"),
        "flower": Int(f"{house}_flower"),
        "animal": Int(f"{house}_animal"),
        "hobby": Int(f"{house}_hobby")
    }

# Create solvers and add constraints
solver = Solver()

# Add domain constraints
for house in house_names:
    solver.add(house_vars[house]["name"] >= 0)
    solver.add(house_vars[house]["name"] < len(names))
    solver.add(house_vars[house]["smoothie"] >= 0)
    solver.add(house_vars[house]["smoothie"] < len(smoothies))
    solver.add(house_vars[house]["flower"] >= 0)
    solver.add(house_vars[house]["flower"] < len(flowers))
    solver.add(house_vars[house]["animal"] >= 0)
    solver.add(house_vars[house]["animal"] < len(animals))
    solver.add(house_vars[house]["hobby"] >= 0)
    solver.add(house_vars[house]["hobby"] < len(hobbies))

# All values must be unique across houses
for attr in ["name", "smoothie", "flower", "animal", "hobby"]:
    solver.add(Distinct([house_vars[house][attr] for house in house_names]))

# Clue 1: The person who keeps horses and the photography enthusiast are next to each other.
solver.add(Or(
    And(house_vars["House1"]["animal"] == animals.index("horse"), house_vars["House2"]["hobby"] == hobbies.index("photography")),
    And(house_vars["House2"]["animal"] == animals.index("horse"), house_vars["House1"]["hobby"] == hobbies.index("photography")),
    And(house_vars["House2"]["animal"] == animals.index("horse"), house_vars["House3"]["hobby"] == hobbies.index("photography")),
    And(house_vars["House3"]["animal"] == animals.index("horse"), house_vars["House2"]["hobby"] == hobbies.index("photography"))
))

# Clue 2: The bird keeper is the person who likes Cherry smoothies.
solver.add(house_vars["House1"]["animal"] == animals.index("bird") == house_vars["House1"]["smoothie"] == smoothies.index("cherry"))
solver.add(house_vars["House2"]["animal"] == animals.index("bird") == house_vars["House2"]["smoothie"] == smoothies.index("cherry"))
solver.add(house_vars["House3"]["animal"] == animals.index("bird") == house_vars["House3"]["smoothie"] == smoothies.index("cherry"))

# Clue 3: The person who loves cooking is the Desert smoothie lover.
solver.add(house_vars["House1"]["hobby"] == hobbies.index("cooking") == house_vars["House1"]["smoothie"] == smoothies.index("desert"))
solver.add(house_vars["House2"]["hobby"] == hobbies.index("cooking") == house_vars["House2"]["smoothie"] == smoothies.index("desert"))
solver.add(house_vars["House3"]["hobby"] == hobbies.index("cooking") == house_vars["House3"]["smoothie"] == smoothies.index("desert"))

# Clue 4: The person who enjoys gardening is the person who loves a carnations arrangement.
solver.add(house_vars["House1"]["hobby"] == hobbies.index("gardening") == house_vars["House1"]["flower"] == flowers.index("carnations"))
solver.add(house_vars["House2"]["hobby"] == hobbies.index("gardening") == house_vars["House2"]["flower"] == flowers.index("carnations"))
solver.add(house_vars["House3"]["hobby"] == hobbies.index("gardening") == house_vars["House3"]["flower"] == flowers.index("carnations"))

# Clue 5: The person who loves cooking is directly left of Peter.
solver.add(Or(
    And(house_vars["House1"]["hobby"] == hobbies.index("cooking"), house_vars["House2"]["name"] == names.index("Peter")),
    And(house_vars["House2"]["hobby"] == hobbies.index("cooking"), house_vars["House3"]["name"] == names.index("Peter"))
))

# Clue 6: The person who loves a bouquet of daffodils is the Desert smoothie lover.
solver.add(house_vars["House1"]["flower"] == flowers.index("daffodils") == house_vars["House1"]["smoothie"] == smoothies.index("desert"))
solver.add(house_vars["House2"]["flower"] == flowers.index("daffodils") == house_vars["House2"]["smoothie"] == smoothies.index("desert"))
solver.add(house_vars["House3"]["flower"] == flowers.index("daffodils") == house_vars["House3"]["smoothie"] == smoothies.index("desert"))

# Clue 7: The Watermelon smoothie lover is the person who keeps horses.
solver.add(house_vars["House1"]["smoothie"] == smoothies.index("watermelon") == house_vars["House1"]["animal"] == animals.index("horse"))
solver.add(house_vars["House2"]["smoothie"] == smoothies.index("watermelon") == house_vars["House2"]["animal"] == animals.index("horse"))
solver.add(house_vars["House3"]["smoothie"] == smoothies.index("watermelon") == house_vars["House3"]["animal"] == animals.index("horse"))

# Clue 8: The photography enthusiast is Eric.
solver.add(house_vars["House1"]["hobby"] == hobbies.index("photography") == house_vars["House1"]["name"] == names.index("Eric"))
solver.add(house_vars["House2"]["hobby"] == hobbies.index("photography") == house_vars["House2"]["name"] == names.index("Eric"))
solver.add(house_vars["House3"]["hobby"] == hobbies.index("photography") == house_vars["House3"]["name"] == names.index("Eric"))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "Flower", "Animal", "Hobby"],
            "rows": []
        }
    }
    for i, house in enumerate(house_names):
        name = names[model[house_vars[house]["name"]].as_long()]
        smoothie = smoothies[model[house_vars[house]["smoothie"]].as_long()]
        flower = flowers[model[house_vars[house]["flower"]].as_long()]
        animal = animals[model[house_vars[house]["animal"]].as_long()]
        hobby = hobbies[model[house_vars[house]["hobby"]].as_long()]
        solution["solution"]["rows"].append([str(i+1), name, smoothie, flower, animal, hobby])
    print(solution)
else:
    print("No solution found")