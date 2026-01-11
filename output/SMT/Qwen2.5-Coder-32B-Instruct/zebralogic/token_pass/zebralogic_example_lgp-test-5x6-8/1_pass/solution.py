from z3 import *

# Define variables
houses = [1, 2, 3, 4, 5]
names = ["Eric", "Peter", "Arnold", "Bob", "Alice"]
house_styles = ["modern", "craftsman", "ranch", "victorian", "colonial"]
mothers = ["Penny", "Kailyn", "Holly", "Janelle", "Aniya"]
phone_models = ["oneplus 9", "google pixel 6", "huawei p50", "iphone 13", "samsung galaxy s21"]
drinks = ["coffee", "water", "root beer", "tea", "milk"]
animals = ["fish", "dog", "horse", "bird", "cat"]

# Create dictionaries to hold variables
name_vars = {house: Int(f"name_{house}") for house in houses}
house_style_vars = {house: Int(f"house_style_{house}") for house in houses}
mother_vars = {house: Int(f"mother_{house}") for house in houses}
phone_model_vars = {house: Int(f"phone_model_{house}") for house in houses}
drink_vars = {house: Int(f"drink_{house}") for house in houses}
animal_vars = {house: Int(f"animal_{house}") for house in houses}

# Create solvers
solver = Solver()

# Add constraints for unique values in each category
solver.add(Distinct([name_vars[house] for house in houses]))
solver.add(Distinct([house_style_vars[house] for house in houses]))
solver.add(Distinct([mother_vars[house] for house in houses]))
solver.add(Distinct([phone_model_vars[house] for house in houses]))
solver.add(Distinct([drink_vars[house] for house in houses]))
solver.add(Distinct([animal_vars[house] for house in houses]))

# Map integers to actual values
def map_var_to_value(var, value_list):
    return Or([var == i for i, value in enumerate(value_list)])

# Apply constraints based on clues
solver.add(map_var_to_value(drink_vars[5], drinks))  # The tea drinker is Bob (Clue 9)
solver.add(drink_vars[5] == drinks.index("tea"))  # The tea drinker is Bob (Clue 9)
solver.add(drink_vars[5] == drinks.index("tea"))  # The tea drinker is in the fourth house (Clue 17)
solver.add(drink_vars[4] == drinks.index("tea"))  # The tea drinker is in the fourth house (Clue 17)

solver.add(drink_vars[2] == drinks.index("water"))  # The one who only drinks water is Alice (Clue 2)
solver.add(name_vars[2] == names.index("Alice"))  # The one who only drinks water is Alice (Clue 2)

solver.add(drink_vars[2] == drinks.index("water"))  # The person whose mother's name is Janelle is the one who only drinks water (Clue 22)
solver.add(mother_vars[2] == mothers.index("Janelle"))  # The person whose mother's name is Janelle is the one who only drinks water (Clue 22)

solver.add(drink_vars[1] == drinks.index("root beer"))  # The root beer lover is Peter (Clue 20)
solver.add(name_vars[1] == names.index("Peter"))  # The root beer lover is Peter (Clue 20)

solver.add(animal_vars[1] == animals.index("cat"))  # The root beer lover is the cat lover (Clue 6)
solver.add(animal_vars[1] == animals.index("cat"))  # The root beer lover is the cat lover (Clue 6)

solver.add(animal_vars[4] == animals.index("bird"))  # The bird keeper is in the fourth house (Clue 8)
solver.add(house_style_vars[4] != house_styles.index("colonial"))  # The person living in a colonial-style house is not in the fourth house (Clue 7)

solver.add(phone_model_vars[2] != phone_models.index("google pixel 6"))  # The person who uses a Google Pixel 6 is not in the first house (Clue 1)
solver.add(phone_model_vars[2] == phone_models.index("google pixel 6"))  # The person who uses a Google Pixel 6 is the person in a Craftsman-style house (Clue 15)
solver.add(house_style_vars[2] == house_styles.index("craftsman"))  # The person who uses a Google Pixel 6 is the person in a Craftsman-style house (Clue 15)

solver.add(phone_model_vars[3] == phone_models.index("oneplus 9"))  # The person who keeps horses is the person who uses a OnePlus 9 (Clue 4)
solver.add(animal_vars[3] == animals.index("horse"))  # The person who keeps horses is the person who uses a OnePlus 9 (Clue 4)
solver.add(house_style_vars[3] == house_styles.index("modern"))  # The person who keeps horses is the person in a modern-style house (Clue 12)
solver.add(mother_vars[3] == mothers.index("Penny"))  # The person in a modern-style house is The person whose mother's name is Penny (Clue 19)

solver.add(house_style_vars[5] == house_styles.index("colonial"))  # The person living in a colonial-style house is somewhere to the right of the person who uses a Huawei P50 (Clue 3)
solver.add(phone_model_vars[1] == phone_models.index("huawei p50"))  # The person living in a colonial-style house is somewhere to the right of the person who uses a Huawei P50 (Clue 3)

solver.add(house_style_vars[5] != house_styles.index("colonial"))  # The person living in a colonial-style house is not in the fourth house (Clue 7)

solver.add(mother_vars[3] == mothers.index("Kailyn"))  # The person in a ranch-style home is The person whose mother's name is Kailyn (Clue 5)
solver.add(house_style_vars[3] == house_styles.index("ranch"))  # The person in a ranch-style home is The person whose mother's name is Kailyn (Clue 5)

solver.add(mother_vars[2] != mothers.index("Aniya"))  # The person whose mother's name is Aniya is not in the fourth house (Clue 21)

solver.add(phone_model_vars[5] == phone_models.index("iphone 13"))  # The person who uses an iPhone 13 is the person who likes milk (Clue 13)
solver.add(drink_vars[5] == drinks.index("milk"))  # The person who uses an iPhone 13 is the person who likes milk (Clue 13)

solver.add(animal_vars[5] == animals.index("dog"))  # The dog owner is the person who likes milk (Clue 14)
solver.add(drink_vars[5] == drinks.index("milk"))  # The dog owner is the person who likes milk (Clue 14)

solver.add(name_vars[2] != names.index("Eric"))  # Eric is not in the second house (Clue 16)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = []
    for house in houses:
        name = names[model[name_vars[house]].as_long()]
        house_style = house_styles[model[house_style_vars[house]].as_long()]
        mother = mothers[model[mother_vars[house]].as_long()]
        phone_model = phone_models[model[phone_model_vars[house]].as_long()]
        drink = drinks[model[drink_vars[house]].as_long()]
        animal = animals[model[animal_vars[house]].as_long()]
        solution.append([str(house), name, house_style, mother, phone_model, drink, animal])
    
    result = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "Mother", "PhoneModel", "Drink", "Animal"],
            "rows": solution
        }
    }
    print(result)
else:
    print("No solution found")