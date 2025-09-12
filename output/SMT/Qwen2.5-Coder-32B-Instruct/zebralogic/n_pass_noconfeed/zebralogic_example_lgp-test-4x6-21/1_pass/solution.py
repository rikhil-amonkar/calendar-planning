from z3 import *

# Define the domain for each variable
names = ["Peter", "Arnold", "Alice", "Eric"]
flowers = ["roses", "daffodils", "carnations", "lilies"]
hobbies = ["photography", "painting", "cooking", "gardening"]
pets = ["dog", "fish", "bird", "cat"]
colors = ["red", "yellow", "green", "white"]
house_styles = ["craftsman", "colonial", "ranch", "victorian"]

# Create a solver instance
solver = Solver()

# Create dictionaries to hold the variables
name_vars = {i+1: Int(f"name_{i+1}") for i in range(4)}
flower_vars = {i+1: Int(f"flower_{i+1}") for i in range(4)}
hobby_vars = {i+1: Int(f"hobby_{i+1}") for i in range(4)}
pet_vars = {i+1: Int(f"pet_{i+1}") for i in range(4)}
color_vars = {i+1: Int(f"color_{i+1}") for i in range(4)}
house_style_vars = {i+1: Int(f"house_style_{i+1}") for i in range(4)}

# Add constraints for unique values
for var_dict, domain in [(name_vars, names), (flower_vars, flowers), (hobby_vars, hobbies),
                        (pet_vars, pets), (color_vars, colors), (house_style_vars, house_styles)]:
    solver.add(Distinct(*var_dict.values()))
    for var in var_dict.values():
        solver.add(var >= 0)
        solver.add(var < len(domain))

# Define helper function to convert variable to value
def get_value(model, var_dict, domain):
    return domain[model.evaluate(var_dict).as_long()]

# Add puzzle clues as constraints
solver.add(house_style_vars[2] == names.index("Arnold"))
solver.add(name_vars[2] == names.index("Arnold"))
solver.add(flower_vars[1] > name_vars[1])
solver.add(pet_vars[name_vars.index(names.index("photography"))] == pets.index("dog"))
solver.add(flower_vars[3] != flowers.index("daffodils"))
solver.add(flower_vars[name_vars.index(flowers.index("roses"))] == colors.index("red"))
solver.add(color_vars[name_vars.index(flowers.index("roses"))] == colors.index("red"))
solver.add(name_vars[4] == names.index("Eric"))
solver.add(house_style_vars[name_vars.index(names.index("Eric"))] == house_styles.index("victorian"))
solver.add(pet_vars[name_vars.index(colors.index("white"))] == pets.index("fish"))
solver.add(color_vars[name_vars.index(colors.index("white"))] == colors.index("white"))
solver.add(hobby_vars[name_vars.index(colors.index("white"))] == hobbies.index("cooking"))
solver.add(color_vars[name_vars.index(colors.index("white"))] == flowers.index("carnations"))
solver.add(hobby_vars[name_vars.index(colors.index("white"))] > hobby_vars[name_vars.index(hobbies.index("gardening"))])
solver.add(flower_vars[name_vars.index(flowers.index("daffodils"))] == colors.index("yellow"))
solver.add(color_vars[name_vars.index(house_styles.index("colonial"))] == colors.index("red"))
solver.add(pet_vars[name_vars.index(names.index("Eric"))] == pets.index("cat"))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Flower", "Hobby", "Pet", "Color", "HouseStyle"],
            "rows": []
        }
    }
    for house in range(1, 5):
        solution["solution"]["rows"].append([
            str(house),
            get_value(model, name_vars, names),
            get_value(model, flower_vars, flowers),
            get_value(model, hobby_vars, hobbies),
            get_value(model, pet_vars, pets),
            get_value(model, color_vars, colors),
            get_value(model, house_style_vars, house_styles)
        ])
    import json
    print(json.dumps(solution))
else:
    print("No solution found")