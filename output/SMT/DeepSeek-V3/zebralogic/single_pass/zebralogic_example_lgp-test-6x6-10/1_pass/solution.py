import json
from z3 import *

def solve_scheduling_problem():
    # Initialize the solver
    s = Solver()

    # Define the houses
    houses = [1, 2, 3, 4, 5, 6]

    # Define the attributes
    names = ["Arnold", "Bob", "Peter", "Alice", "Carol", "Eric"]
    foods = ["stew", "grilled cheese", "stir fry", "soup", "pizza", "spaghetti"]
    heights = ["tall", "average", "super tall", "very short", "very tall", "short"]
    drinks = ["root beer", "boba tea", "coffee", "water", "tea", "milk"]
    pets = ["hamster", "fish", "cat", "dog", "bird", "rabbit"]
    phone_models = ["samsung galaxy s21", "xiaomi mi 11", "google pixel 6", "iphone 13", "huawei p50", "oneplus 9"]

    # Create variables for each attribute in each house
    name = {h: String(f"name_{h}") for h in houses}
    food = {h: String(f"food_{h}") for h in houses}
    height = {h: String(f"height_{h}") for h in houses}
    drink = {h: String(f"drink_{h}") for h in houses}
    pet = {h: String(f"pet_{h}") for h in houses}
    phone_model = {h: String(f"phone_model_{h}") for h in houses}

    # Add constraints that each attribute is unique within its category
    s.add(Distinct([name[h] for h in houses]))
    s.add(Distinct([food[h] for h in houses]))
    s.add(Distinct([height[h] for h in houses]))
    s.add(Distinct([drink[h] for h in houses]))
    s.add(Distinct([pet[h] for h in houses]))
    s.add(Distinct([phone_model[h] for h in houses]))

    # Each attribute must be one of the allowed values
    for h in houses:
        s.add(Or([name[h] == n for n in names]))
        s.add(Or([food[h] == f for f in foods]))
        s.add(Or([height[h] == ht for ht in heights]))
        s.add(Or([drink[h] == d for d in drinks]))
        s.add(Or([pet[h] == p for p in pets]))
        s.add(Or([phone_model[h] == pm for pm in phone_models]))

    # Apply the clues
    # Clue 1: The person who uses an iPhone 13 is in the third house.
    s.add(phone_model[3] == "iphone 13")

    # Clue 2: Bob is the person who is tall.
    for h in houses:
        s.add(Implies(name[h] == "Bob", height[h] == "tall"))

    # Clue 3: The person who loves the soup is in the second house.
    s.add(food[2] == "soup")

    # Clue 4: The root beer lover is directly left of the person who uses a Xiaomi Mi 11.
    for h in range(1, 6):
        s.add(Implies(drink[h] == "root beer", phone_model[h+1] == "xiaomi mi 11"))

    # Clue 5: The person who uses a Huawei P50 is directly left of the person who loves eating grilled cheese.
    for h in range(1, 6):
        s.add(Implies(phone_model[h] == "huawei p50", food[h+1] == "grilled cheese"))

    # Clue 6: The person who loves stir fry is the person who likes milk.
    for h in houses:
        s.add(Implies(food[h] == "stir fry", drink[h] == "milk"))

    # Clue 7: The person who loves eating grilled cheese is the person who is tall.
    for h in houses:
        s.add(Implies(food[h] == "grilled cheese", height[h] == "tall"))

    # Clue 8: The person who uses a Xiaomi Mi 11 is the coffee drinker.
    for h in houses:
        s.add(Implies(phone_model[h] == "xiaomi mi 11", drink[h] == "coffee"))

    # Clue 9: The person who uses a OnePlus 9 is Arnold.
    for h in houses:
        s.add(Implies(phone_model[h] == "oneplus 9", name[h] == "Arnold"))

    # Clue 10: The person who owns a rabbit is not in the fifth house.
    s.add(pet[5] != "rabbit")

    # Clue 11: The person with a pet hamster is somewhere to the right of the person who uses a Google Pixel 6.
    # This means Google Pixel 6 is left of hamster
    for h in range(1, 6):
        for h2 in range(h+1, 7):
            s.add(Implies(phone_model[h] == "google pixel 6", pet[h2] == "hamster"))

    # Clue 12: The person who is super tall is the person with an aquarium of fish.
    for h in houses:
        s.add(Implies(height[h] == "super tall", pet[h] == "fish"))

    # Clue 13: The person with an aquarium of fish is Alice.
    for h in houses:
        s.add(Implies(pet[h] == "fish", name[h] == "Alice"))

    # Clue 14: The tea drinker is directly left of the person who is a pizza lover.
    for h in range(1, 6):
        s.add(Implies(drink[h] == "tea", food[h+1] == "pizza"))

    # Clue 15: The person who uses a Samsung Galaxy S21 is Carol.
    for h in houses:
        s.add(Implies(phone_model[h] == "samsung galaxy s21", name[h] == "Carol"))

    # Clue 16: The person who is a pizza lover is the person who is short.
    for h in houses:
        s.add(Implies(food[h] == "pizza", height[h] == "short"))

    # Clue 17: Arnold is the person who is very tall.
    for h in houses:
        s.add(Implies(name[h] == "Arnold", height[h] == "very tall"))

    # Clue 18: The person who loves the spaghetti eater is the person who uses a Google Pixel 6.
    for h in houses:
        s.add(Implies(food[h] == "spaghetti", phone_model[h] == "google pixel 6"))

    # Clue 19: The boba tea drinker is somewhere to the right of the person who loves the soup.
    # Soup is in house 2, so boba tea is in house 3-6
    for h in range(3, 7):
        s.add(Implies(drink[h] == "boba tea", h > 2))

    # Clue 20: The person with a pet hamster is not in the fifth house.
    s.add(pet[5] != "hamster")

    # Clue 21: The person who is very tall is not in the second house.
    s.add(height[2] != "very tall")

    # Clue 22: The person who is super tall is somewhere to the left of Peter.
    # Find the house of super tall and ensure it's left of Peter's house
    super_tall_house = Int("super_tall_house")
    peter_house = Int("peter_house")
    s.add(Or([And(height[h] == "super tall", super_tall_house == h) for h in houses]))
    s.add(Or([And(name[h] == "Peter", peter_house == h) for h in houses]))
    s.add(super_tall_house < peter_house)

    # Clue 23: The person who is very short is the person who loves the spaghetti eater.
    for h in houses:
        s.add(Implies(height[h] == "very short", food[h] == "spaghetti"))

    # Clue 24: The person who keeps a pet bird is somewhere to the left of the person who loves the spaghetti eater.
    # Find spaghetti house and ensure bird is left of it
    spaghetti_house = Int("spaghetti_house")
    s.add(Or([And(food[h] == "spaghetti", spaghetti_house == h) for h in houses]))
    for h in houses:
        s.add(Implies(pet[h] == "bird", h < spaghetti_house))

    # Clue 25: The person with an aquarium of fish is directly left of Eric.
    for h in range(1, 6):
        s.add(Implies(pet[h] == "fish", name[h+1] == "Eric"))

    # Clue 26: The person who owns a dog is the person who likes milk.
    for h in houses:
        s.add(Implies(pet[h] == "dog", drink[h] == "milk"))

    # Check if the solver can find a solution
    if s.check() == sat:
        m = s.model()
        solution = {
            "solution": {
                "header": ["House", "Name", "Food", "Height", "Drink", "Pet", "PhoneModel"],
                "rows": []
            }
        }
        for h in houses:
            row = [
                str(h),
                str(m.evaluate(name[h])),
                str(m.evaluate(food[h])),
                str(m.evaluate(height[h])),
                str(m.evaluate(drink[h])),
                str(m.evaluate(pet[h])),
                str(m.evaluate(phone_model[h]))
            ]
            solution["solution"]["rows"].append(row)
        return solution
    else:
        return {"solution": {"header": [], "rows": []}}

# Solve the problem and print the solution as JSON
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))