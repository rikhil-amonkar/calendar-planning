from z3 import *

# Define the domain for each variable
names = ["Peter", "Arnold", "Alice", "Eric"]
flowers = ["roses", "daffodils", "carnations", "lilies"]
hobbies = ["photography", "painting", "cooking", "gardening"]
pets = ["dog", "fish", "bird", "cat"]
colors = ["red", "yellow", "green", "white"]
house_styles = ["craftsman", "colonial", "ranch", "victorian"]

# Create variables for each characteristic for each house
name_vars = [Int(f"name_{i}") for i in range(4)]
flower_vars = [Int(f"flower_{i}") for i in range(4)]
hobby_vars = [Int(f"hobby_{i}") for i in range(4)]
pet_vars = [Int(f"pet_{i}") for i in range(4)]
color_vars = [Int(f"color_{i}") for i in range(4)]
house_style_vars = [Int(f"house_style_{i}") for i in range(4)]

# Create the solver
solver = Solver()

# Add constraints for each variable to be within the domain
for var in name_vars + flower_vars + hobby_vars + pet_vars + color_vars + house_style_vars:
    solver.add(var >= 0)
    solver.add(var <= 3)

# All values for each characteristic must be unique
solver.add(Distinct(name_vars))
solver.add(Distinct(flower_vars))
solver.add(Distinct(hobby_vars))
solver.add(Distinct(pet_vars))
solver.add(Distinct(color_vars))
solver.add(Distinct(house_style_vars))

# Translate clues into constraints
# Clue 1 & 6: Arnold in craftsman house, house 2
solver.add(name_vars[1] == names.index("Arnold"))
solver.add(house_style_vars[1] == house_styles.index("craftsman"))

# Clue 2: Roses lover is somewhere to the right of Peter
solver.add(Or(flower_vars[1] == flowers.index("roses"), flower_vars[2] == flowers.index("roses"), flower_vars[3] == flowers.index("roses")))
solver.add(Implies(name_vars[0] == names.index("Peter"), Or(flower_vars[1] == flowers.index("roses"), flower_vars[2] == flowers.index("roses"), flower_vars[3] == flowers.index("roses"))))

# Clue 3: Photography enthusiast owns a dog
solver.add(Or((hobby_vars[i] == hobbies.index("photography") == pet_vars[i] == pets.index("dog")) for i in range(4)))

# Clue 4: Daffodils lover is not in the fourth house
solver.add(flower_vars[3] != flowers.index("daffodils"))

# Clue 5 & 13: Roses lover loves red, Colonial house has red
solver.add(Or((flower_vars[i] == flowers.index("roses") == color_vars[i] == colors.index("red")) for i in range(4)))
solver.add(Or((house_style_vars[i] == house_styles.index("colonial") == color_vars[i] == colors.index("red")) for i in range(4)))

# Clue 7: Eric in victorian house
solver.add(name_vars[3] == names.index("Eric"))
solver.add(house_style_vars[3] == house_styles.index("victorian"))

# Clue 8 & 10: Fish owner loves white, White lover loves carnations
solver.add(Or((pet_vars[i] == pets.index("fish") == color_vars[i] == colors.index("white")) for i in range(4)))
solver.add(Or((color_vars[i] == colors.index("white") == flower_vars[i] == flowers.index("carnations")) for i in range(4)))

# Clue 9: Cooking lover is somewhere to the right of red lover
solver.add(Implies(Or((color_vars[i] == colors.index("red")) for i in range(4)), Or((hobby_vars[j] == hobbies.index("cooking")) for j in range(i+1, 4))))

# Clue 11: White lover is somewhere to the right of gardening lover
solver.add(Implies(Or((color_vars[i] == colors.index("white")) for i in range(4)), Or((hobby_vars[j] == hobbies.index("gardening")) for j in range(i+1, 4))))

# Clue 12: Daffodils lover loves yellow
solver.add(Or((flower_vars[i] == flowers.index("daffodils") == color_vars[i] == colors.index("yellow")) for i in range(4)))

# Clue 14: Eric has a cat
solver.add(pet_vars[3] == pets.index("cat"))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = []
    for i in range(4):
        name = names[model.evaluate(name_vars[i]).as_long()]
        flower = flowers[model.evaluate(flower_vars[i]).as_long()]
        hobby = hobbies[model.evaluate(hobby_vars[i]).as_long()]
        pet = pets[model.evaluate(pet_vars[i]).as_long()]
        color = colors[model.evaluate(color_vars[i]).as_long()]
        house_style = house_styles[model.evaluate(house_style_vars[i]).as_long()]
        solution.append([str(i+1), name, flower, hobby, pet, color, house_style])
    
    print({
        "solution": {
            "header": ["House", "Name", "Flower", "Hobby", "Pet", "Color", "HouseStyle"],
            "rows": solution
        }
    })
else:
    print("No solution found")