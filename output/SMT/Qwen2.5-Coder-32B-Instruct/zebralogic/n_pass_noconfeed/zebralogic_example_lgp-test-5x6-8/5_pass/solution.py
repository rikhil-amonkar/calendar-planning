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
house_vars = [[Bool(f"{attr}_{house}_{value}") for value in values] for attr, values in 
              zip(["name", "house_style", "mother", "phone_model", "drink", "animal"], 
                  [names, house_styles, mothers, phone_models, drinks, animals])]

# Each house must have exactly one name, one house style, one mother, one phone model, one drink, and one animal
for house in range(5):
    solver.add(Or(house_vars[attr][house][value] for value in range(5)) for attr in range(6))
    solver.add(And(Not(And(house_vars[attr][house][value1], house_vars[attr][house][value2])) for attr in range(6) for value1 in range(5) for value2 in range(value1 + 1, 5)))

# Each name, house style, mother, phone model, drink, and animal must be assigned to exactly one house
for attr in range(6):
    for value in range(5):
        solver.add(Or(house_vars[attr][house][value] for house in range(5)))
        solver.add(And(Not(And(house_vars[attr][house1][value], house_vars[attr][house2][value])) for house1 in range(5) for house2 in range(house1 + 1, 5)))

# Add clues as constraints
solver.add(Not(house_vars[3][0][1]))  # The person with the Google Pixel 6 does not live in the first house.
solver.add(house_vars[4][names.index("Alice")][1])  # Alice drinks water.
solver.add(house_vars[1][house_styles.index("colonial")][0] > house_vars[3][phone_models.index("huawei p50")][0])  # The colonial house is to the right of the Huawei P50 house.
solver.add(house_vars[5][animals.index("horse")][0] == house_vars[3][phone_models.index("oneplus 9")][0])  # The person with the OnePlus 9 has a horse.
solver.add(house_vars[1][house_styles.index("ranch")][0] == house_vars[2][mothers.index("Kailyn")][0])  # Kailyn lives in the ranch house.
solver.add(house_vars[4][animals.index("cat")][0] == house_vars[4][drinks.index("root beer")][0])  # The person who has a cat drinks root beer.
solver.add(house_vars[1][house_styles.index("colonial")][0] != 4)  # The colonial house is not the fourth house.
solver.add(house_vars[5][animals.index("bird")][0] == 4)  # The bird is in the fourth house.
solver.add(house_vars[4][names.index("Bob")][0] == house_vars[4][drinks.index("tea")][0])  # Bob drinks tea.
solver.add(house_vars[4][names.index("Bob")][0] > house_vars[2][mothers.index("Kailyn")][0])  # Bob drinks tea after Kailyn.
solver.add(house_vars[4][animals.index("cat")][0] < house_vars[2][mothers.index("Kailyn")][0])  # The person who drinks root beer lives before Kailyn.
solver.add(house_vars[5][animals.index("horse")][0] == house_vars[1][house_styles.index("modern")][0])  # The person with the horse lives in the modern house.
solver.add(house_vars[3][phone_models.index("iphone 13")][0] == house_vars[4][drinks.index("milk")][0])  # The person with the iPhone 13 drinks milk.
solver.add(house_vars[4][drinks.index("milk")][0] == house_vars[5][animals.index("dog")][0])  # The person who drinks milk has a dog.
solver.add(house_vars[3][phone_models.index("google pixel 6")][0] == house_vars[1][house_styles.index("craftsman")][0])  # The person with the Google Pixel 6 lives in the craftsman house.
solver.add(Not(house_vars[0][1][0]))  # Eric does not live in the second house.
solver.add(house_vars[5][animals.index("horse")][0] == 3)  # The horse is in the third house.
solver.add(house_vars[1][house_styles.index("modern")][0] == house_vars[2][mothers.index("Penny")][0])  # Penny lives in the modern house.
solver.add(house_vars[4][names.index("Peter")][0] == house_vars[4][drinks.index("root beer")][0])  # Peter drinks root beer.
solver.add(Not(house_vars[2][mothers.index("Aniya")][0] == 4))  # Aniya does not live in the fourth house.

# Check if the problem is solvable
if solver.check() == sat:
    m = solver.model()
    result = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "Mother", "PhoneModel", "Drink", "Animal"],
            "rows": []
        }
    }
    for house in range(5):
        house_info = [str(house + 1)]
        for attr, values in enumerate([names, house_styles, mothers, phone_models, drinks, animals]):
            for value_index, value in enumerate(values):
                if m.evaluate(house_vars[attr][house][value_index]):
                    house_info.append(value)
        result["solution"]["rows"].append(house_info)
    import json
    print(json.dumps(result))
else:
    print("No solution found")