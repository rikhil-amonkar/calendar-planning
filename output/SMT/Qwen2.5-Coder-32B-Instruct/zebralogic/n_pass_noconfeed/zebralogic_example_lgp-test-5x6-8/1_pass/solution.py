from z3 import *

# Define the domains
names = ["Eric", "Peter", "Arnold", "Bob", "Alice"]
house_styles = ["modern", "craftsman", "ranch", "victorian", "colonial"]
mothers = ["Penny", "Kailyn", "Holly", "Janelle", "Aniya"]
phone_models = ["oneplus 9", "google pixel 6", "huawei p50", "iphone 13", "samsung galaxy s21"]
drinks = ["coffee", "water", "root beer", "tea", "milk"]
animals = ["fish", "dog", "horse", "bird", "cat"]

# Create a solver instance
solver = Solver()

# Define variables
houses = [Int(f"house_{i}") for i in range(1, 6)]
name_vars = {name: Int(f"name_{name}") for name in names}
house_style_vars = {style: Int(f"house_style_{style}") for style in house_styles}
mother_vars = {mother: Int(f"mother_{mother}") for mother in mothers}
phone_model_vars = {model: Int(f"phone_model_{model}") for model in phone_models}
drink_vars = {drink: Int(f"drink_{drink}") for drink in drinks}
animal_vars = {animal: Int(f"animal_{animal}") for animal in animals}

# Add domain constraints
for var in houses + list(name_vars.values()) + list(house_style_vars.values()) + \
           list(mother_vars.values()) + list(phone_model_vars.values()) + \
           list(drink_vars.values()) + list(animal_vars.values()):
    solver.add(var >= 1)
    solver.add(var <= 5)

# All variables are distinct
solver.add(Distinct(houses))
solver.add(Distinct(list(name_vars.values())))
solver.add(Distinct(list(house_style_vars.values())))
solver.add(Distinct(list(mother_vars.values())))
solver.add(Distinct(list(phone_model_vars.values())))
solver.add(Distinct(list(drink_vars.values())))
solver.add(Distinct(list(animal_vars.values())))

# Map names to houses
for name, var in name_vars.items():
    solver.add(var == houses[names.index(name)])

# Map house styles to houses
for style, var in house_style_vars.items():
    solver.add(var == houses[house_styles.index(style)])

# Map mothers to houses
for mother, var in mother_vars.items():
    solver.add(var == houses[mothers.index(mother)])

# Map phone models to houses
for model, var in phone_model_vars.items():
    solver.add(var == houses[phone_models.index(model)])

# Map drinks to houses
for drink, var in drink_vars.items():
    solver.add(var == houses[drinks.index(drink)])

# Map animals to houses
for animal, var in animal_vars.items():
    solver.add(var == houses[animals.index(animal)])

# Add clues as constraints
solver.add(phone_model_vars["google pixel 6"] != 1)
solver.add(drink_vars["water"] == name_vars["Alice"])
solver.add(house_style_vars["colonial"] > phone_model_vars["huawei p50"])
solver.add(animal_vars["horse"] == phone_model_vars["oneplus 9"])
solver.add(house_style_vars["ranch"] == mother_vars["Kailyn"])
solver.add(drink_vars["root beer"] == animal_vars["cat"])
solver.add(house_style_vars["colonial"] != 4)
solver.add(animal_vars["bird"] == 4)
solver.add(drink_vars["tea"] == name_vars["Bob"])
solver.add(drink_vars["tea"] > mother_vars["Kailyn"])
solver.add(drink_vars["root beer"] < mother_vars["Kailyn"])
solver.add(animal_vars["horse"] == house_style_vars["modern"])
solver.add(phone_model_vars["iphone 13"] == drink_vars["milk"])
solver.add(animal_vars["dog"] == drink_vars["milk"])
solver.add(phone_model_vars["google pixel 6"] == house_style_vars["craftsman"])
solver.add(name_vars["Eric"] != 2)
solver.add(drink_vars["tea"] == 4)
solver.add(animal_vars["horse"] == 3)
solver.add(house_style_vars["modern"] == mother_vars["Penny"])
solver.add(drink_vars["root beer"] == name_vars["Peter"])
solver.add(mother_vars["Aniya"] != 4)
solver.add(mother_vars["Janelle"] == drink_vars["water"])

# Check if the problem is solvable
if solver.check() == sat:
    m = solver.model()
    result = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "Mother", "PhoneModel", "Drink", "Animal"],
            "rows": []
        }
    }
    for i in range(1, 6):
        house_info = [str(i)]
        for d, vars_dict in zip([names, house_styles, mothers, phone_models, drinks, animals],
                               [name_vars, house_style_vars, mother_vars, phone_model_vars, drink_vars, animal_vars]):
            for key, var in vars_dict.items():
                if m.evaluate(var) == i:
                    house_info.append(key)
        result["solution"]["rows"].append(house_info)
    import json
    print(json.dumps(result))
else:
    print("No solution found")