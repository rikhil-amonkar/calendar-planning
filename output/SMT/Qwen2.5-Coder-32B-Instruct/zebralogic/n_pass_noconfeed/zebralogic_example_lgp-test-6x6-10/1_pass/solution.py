from z3 import *

def solve_puzzle():
    # Define the domains
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Arnold", "Bob", "Peter", "Alice", "Carol", "Eric"]
    foods = ["stew", "grilled cheese", "stir fry", "soup", "pizza", "spaghetti"]
    heights = ["tall", "average", "super tall", "very short", "very tall", "short"]
    drinks = ["root beer", "boba tea", "coffee", "water", "tea", "milk"]
    pets = ["hamster", "fish", "cat", "dog", "bird", "rabbit"]
    phones = ["samsung galaxy s21", "xiaomi mi 11", "google pixel 6", "iphone 13", "huawei p50", "oneplus 9"]

    # Create variables
    name_vars = {house: Int(f"name_{house}") for house in houses}
    food_vars = {house: Int(f"food_{house}") for house in houses}
    height_vars = {house: Int(f"height_{house}") for house in houses}
    drink_vars = {house: Int(f"drink_{house}") for house in houses}
    pet_vars = {house: Int(f"pet_{house}") for house in houses}
    phone_vars = {house: Int(f"phone_{house}") for house in houses}

    # Create solver
    solver = Solver()

    # Add domain constraints
    for house in houses:
        solver.add(name_vars[house] >= 0)
        solver.add(name_vars[house] < len(names))
        solver.add(food_vars[house] >= 0)
        solver.add(food_vars[house] < len(foods))
        solver.add(height_vars[house] >= 0)
        solver.add(height_vars[house] < len(heights))
        solver.add(drink_vars[house] >= 0)
        solver.add(drink_vars[house] < len(drinks))
        solver.add(pet_vars[house] >= 0)
        solver.add(pet_vars[house] < len(pets))
        solver.add(phone_vars[house] >= 0)
        solver.add(phone_vars[house] < len(phones))

    # All values must be unique
    solver.add(Distinct([name_vars[house] for house in houses]))
    solver.add(Distinct([food_vars[house] for house in houses]))
    solver.add(Distinct([height_vars[house] for house in houses]))
    solver.add(Distinct([drink_vars[house] for house in houses]))
    solver.add(Distinct([pet_vars[house] for house in houses]))
    solver.add(Distinct([phone_vars[house] for house in houses]))

    # Clue constraints
    solver.add(phone_vars[3] == phones.index("iphone 13"))
    solver.add(name_vars[bob_house] == names.index("Bob") for bob_house in houses if height_vars[bob_house] == heights.index("tall"))
    solver.add(food_vars[2] == foods.index("soup"))
    solver.add(drink_vars[i] == drinks.index("root beer") for i in range(5) if phone_vars[i + 1] == phones.index("xiaomi mi 11"))
    solver.add(phone_vars[i] == phones.index("huawei p50") for i in range(5) if food_vars[i + 1] == foods.index("grilled cheese"))
    solver.add(food_vars[i] == foods.index("stir fry") for i in houses if drink_vars[i] == drinks.index("milk"))
    solver.add(food_vars[i] == foods.index("grilled cheese") for i in houses if height_vars[i] == heights.index("tall"))
    solver.add(phone_vars[i] == phones.index("xiaomi mi 11") for i in houses if drink_vars[i] == drinks.index("coffee"))
    solver.add(name_vars[i] == names.index("Arnold") for i in houses if phone_vars[i] == phones.index("oneplus 9"))
    solver.add(pet_vars[i] != pets.index("rabbit") for i in [4])
    solver.add(pet_vars[i] == pets.index("hamster") for i in range(1, 6) if phone_vars[j] == phones.index("google pixel 6") for j in range(i + 1, 7))
    solver.add(height_vars[i] == heights.index("super tall") for i in houses if pet_vars[i] == pets.index("fish"))
    solver.add(pet_vars[i] == pets.index("fish") for i in houses if name_vars[i] == names.index("Alice"))
    solver.add(drink_vars[i] == drinks.index("tea") for i in range(5) if food_vars[i + 1] == foods.index("pizza"))
    solver.add(name_vars[i] == names.index("Carol") for i in houses if phone_vars[i] == phones.index("samsung galaxy s21"))
    solver.add(food_vars[i] == foods.index("pizza") for i in houses if height_vars[i] == heights.index("short"))
    solver.add(name_vars[i] == names.index("Arnold") for i in houses if height_vars[i] == heights.index("very tall"))
    solver.add(food_vars[i] == foods.index("spaghetti") for i in houses if phone_vars[i] == phones.index("google pixel 6"))
    solver.add(drink_vars[i] == drinks.index("boba tea") for i in range(1, 6) if food_vars[j] == foods.index("soup") for j in range(i + 1, 7))
    solver.add(pet_vars[i] != pets.index("hamster") for i in [4])
    solver.add(height_vars[i] != heights.index("very tall") for i in [1])
    solver.add(height_vars[i] == heights.index("super tall") for i in range(5) if name_vars[j] == names.index("Peter") for j in range(i + 1, 6))
    solver.add(height_vars[i] == heights.index("very short") for i in houses if food_vars[i] == foods.index("spaghetti"))
    solver.add(pet_vars[i] == pets.index("bird") for i in range(5) if food_vars[j] == foods.index("spaghetti") for j in range(i + 1, 6))
    solver.add(pet_vars[i] == pets.index("fish") for i in range(5) if name_vars[i + 1] == names.index("Eric"))
    solver.add(pet_vars[i] == pets.index("dog") for i in houses if drink_vars[i] == drinks.index("milk"))

    # Solve the problem
    if solver.check() == sat:
        model = solver.model()
        solution = {
            "solution": {
                "header": ["House", "Name", "Food", "Height", "Drink", "Pet", "PhoneModel"],
                "rows": []
            }
        }
        for house in houses:
            name = names[model.evaluate(name_vars[house]).as_long()]
            food = foods[model.evaluate(food_vars[house]).as_long()]
            height = heights[model.evaluate(height_vars[house]).as_long()]
            drink = drinks[model.evaluate(drink_vars[house]).as_long()]
            pet = pets[model.evaluate(pet_vars[house]).as_long()]
            phone = phones[model.evaluate(phone_vars[house]).as_long()]
            solution["solution"]["rows"].append([str(house), name, food, height, drink, pet, phone])
        return solution
    else:
        return None

# Output the solution as JSON
import json
print(json.dumps(solve_puzzle(), indent=2))