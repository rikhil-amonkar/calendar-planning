from z3 import *

# Create a solver instance
solver = Solver()

# Define variables
houses = range(1, 7)
names = ["Arnold", "Bob", "Peter", "Alice", "Carol", "Eric"]
foods = ["stew", "grilled cheese", "stir fry", "soup", "pizza", "spaghetti"]
heights = ["tall", "average", "super tall", "very short", "very tall", "short"]
drinks = ["root beer", "boba tea", "coffee", "water", "tea", "milk"]
pets = ["hamster", "fish", "cat", "dog", "bird", "rabbit"]
phones = ["samsung galaxy s21", "xiaomi mi 11", "google pixel 6", "iphone 13", "huawei p50", "oneplus 9"]

# Declare variables for each attribute
name_vars = {house: Int(f"name_{house}") for house in houses}
food_vars = {house: Int(f"food_{house}") for house in houses}
height_vars = {house: Int(f"height_{house}") for house in houses}
drink_vars = {house: Int(f"drink_{house}") for house in houses}
pet_vars = {house: Int(f"pet_{house}") for house in houses}
phone_vars = {house: Int(f"phone_{house}") for house in houses}

# Add constraints for unique values within each category
for house in houses:
    solver.add(name_vars[house] >= 0, name_vars[house] < len(names))
    solver.add(food_vars[house] >= 0, food_vars[house] < len(foods))
    solver.add(height_vars[house] >= 0, height_vars[house] < len(heights))
    solver.add(drink_vars[house] >= 0, drink_vars[house] < len(drinks))
    solver.add(pet_vars[house] >= 0, pet_vars[house] < len(pets))
    solver.add(phone_vars[house] >= 0, phone_vars[house] < len(phones))

solver.add(Distinct([name_vars[house] for house in houses]))
solver.add(Distinct([food_vars[house] for house in houses]))
solver.add(Distinct([height_vars[house] for house in houses]))
solver.add(Distinct([drink_vars[house] for house in houses]))
solver.add(Distinct([pet_vars[house] for house in houses]))
solver.add(Distinct([phone_vars[house] for house in houses]))

# Apply clues
# 1. The person who uses an iPhone 13 is in the third house.
solver.add(phone_vars[3] == phones.index("iphone 13"))

# 2. Bob is the person who is tall.
solver.add(name_vars[bob_house] == names.index("Bob") for bob_house in houses if height_vars[bob_house] == heights.index("tall"))

# 3. The person who loves the soup is in the second house.
solver.add(food_vars[2] == foods.index("soup"))

# 4. The root beer lover is directly left of the person who uses a Xiaomi Mi 11.
for house in range(1, 6):
    solver.add(Or(drink_vars[house] != drinks.index("root beer"), phone_vars[house + 1] != phones.index("xiaomi mi 11")))

# 5. The person who uses a Huawei P50 is directly left of the person who loves eating grilled cheese.
for house in range(1, 6):
    solver.add(Or(phone_vars[house] != phones.index("huawei p50"), food_vars[house + 1] != foods.index("grilled cheese")))

# 6. The person who loves stir fry is the person who likes milk.
solver.add(food_vars[milk_house] == foods.index("stir fry") for milk_house in houses if drink_vars[milk_house] == drinks.index("milk"))

# 7. The person who loves eating grilled cheese is the person who is tall.
solver.add(food_vars[tall_house] == foods.index("grilled cheese") for tall_house in houses if height_vars[tall_house] == heights.index("tall"))

# 8. The person who uses a Xiaomi Mi 11 is the coffee drinker.
solver.add(phone_vars[xiaomi_house] == phones.index("xiaomi mi 11") for xiaomi_house in houses if drink_vars[xiaomi_house] == drinks.index("coffee"))

# 9. The person who uses a OnePlus 9 is Arnold.
solver.add(phone_vars[arnold_house] == phones.index("oneplus 9") for arnold_house in houses if name_vars[arnold_house] == names.index("Arnold"))

# 10. The person who owns a rabbit is not in the fifth house.
solver.add(pet_vars[5] != pets.index("rabbit"))

# 11. The person with a pet hamster is somewhere to the right of the person who uses a Google Pixel 6.
for house in range(1, 6):
    solver.add(Or(phone_vars[house] != phones.index("google pixel 6"), pet_vars[right_house] != pets.index("hamster")) for right_house in range(house + 1, 7))

# 12. The person who is super tall is the person with an aquarium of fish.
solver.add(height_vars[fish_house] == heights.index("super tall") for fish_house in houses if pet_vars[fish_house] == pets.index("fish"))

# 13. The person with an aquarium of fish is Alice.
solver.add(pet_vars[alice_house] == pets.index("fish") for alice_house in houses if name_vars[alice_house] == names.index("Alice"))

# 14. The tea drinker is directly left of the person who is a pizza lover.
for house in range(1, 6):
    solver.add(Or(drink_vars[house] != drinks.index("tea"), food_vars[house + 1] != foods.index("pizza")))

# 15. The person who uses a Samsung Galaxy S21 is Carol.
solver.add(phone_vars[carol_house] == phones.index("samsung galaxy s21") for carol_house in houses if name_vars[carol_house] == names.index("Carol"))

# 16. The person who is a pizza lover is the person who is short.
solver.add(food_vars[short_house] == foods.index("pizza") for short_house in houses if height_vars[short_house] == heights.index("short"))

# 17. Arnold is the person who is very tall.
solver.add(name_vars[arnold_house] == names.index("Arnold") for arnold_house in houses if height_vars[arnold_house] == heights.index("very tall"))

# 18. The person who loves the spaghetti eater is the person who uses a Google Pixel 6.
solver.add(food_vars[spaghetti_house] == foods.index("spaghetti") for spaghetti_house in houses if phone_vars[spaghetti_house] == phones.index("google pixel 6"))

# 19. The boba tea drinker is somewhere to the right of the person who loves the soup.
for house in range(1, 6):
    solver.add(Or(food_vars[house] != foods.index("soup"), drink_vars[right_house] != drinks.index("boba tea")) for right_house in range(house + 1, 7))

# 20. The person with a pet hamster is not in the fifth house.
solver.add(pet_vars[5] != pets.index("hamster"))

# 21. The person who is very tall is not in the second house.
solver.add(Not(height_vars[2] == heights.index("very tall")))

# 22. The person who is super tall is somewhere to the left of Peter.
for house in range(1, 6):
    solver.add(Or(height_vars[house] != heights.index("super tall"), name_vars[right_house] != names.index("Peter")) for right_house in range(house + 1, 7))

# 23. The person who is very short is the person who loves the spaghetti eater.
solver.add(height_vars[spaghetti_house] == heights.index("very short") for spaghetti_house in houses if food_vars[spaghetti_house] == foods.index("spaghetti"))

# 24. The person who keeps a pet bird is somewhere to the left of the person who loves the spaghetti eater.
for house in range(1, 6):
    solver.add(Or(pet_vars[house] != pets.index("bird"), food_vars[right_house] != foods.index("spaghetti")) for right_house in range(house + 1, 7))

# 25. The person with an aquarium of fish is directly left of Eric.
for house in range(1, 6):
    solver.add(Or(pet_vars[house] != pets.index("fish"), name_vars[house + 1] != names.index("Eric")))

# 26. The person who owns a dog is the person who likes milk.
solver.add(pet_vars[milk_house] == pets.index("dog") for milk_house in houses if drink_vars[milk_house] == drinks.index("milk"))

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    solution = []
    for house in houses:
        name = names[model[name_vars[house]].as_long()]
        food = foods[model[food_vars[house]].as_long()]
        height = heights[model[height_vars[house]].as_long()]
        drink = drinks[model[drink_vars[house]].as_long()]
        pet = pets[model[pet_vars[house]].as_long()]
        phone = phones[model[phone_vars[house]].as_long()]
        solution.append([str(house), name, food, height, drink, pet, phone])
    
    result = {
        "solution": {
            "header": ["House", "Name", "Food", "Height", "Drink", "Pet", "PhoneModel"],
            "rows": solution
        }
    }
    print(json.dumps(result, indent=2))
else:
    print("No solution found")