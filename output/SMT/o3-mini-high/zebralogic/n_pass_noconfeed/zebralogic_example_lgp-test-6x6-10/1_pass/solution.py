#!/usr/bin/env python3
import json
from z3 import *

def main():
    solver = Solver()

    # There are 6 houses; we use indices 0 through 5.
    n = 6

    # Define variables for each attribute for every house.
    names   = [Int(f"name_{i}") for i in range(n)]
    foods   = [Int(f"food_{i}") for i in range(n)]
    heights = [Int(f"height_{i}") for i in range(n)]
    drinks  = [Int(f"drink_{i}") for i in range(n)]
    pets    = [Int(f"pet_{i}") for i in range(n)]
    phones  = [Int(f"phone_{i}") for i in range(n)]

    # Domain for each variable: they take values 0..5.
    for lst in [names, foods, heights, drinks, pets, phones]:
        for var in lst:
            solver.add(var >= 0, var < 6)

    # All attributes must be assigned uniquely (each list is a permutation).
    solver.add(Distinct(names))
    solver.add(Distinct(foods))
    solver.add(Distinct(heights))
    solver.add(Distinct(drinks))
    solver.add(Distinct(pets))
    solver.add(Distinct(phones))

    # Mappings (orderings):
    # Names: 0: Arnold, 1: Bob, 2: Peter, 3: Alice, 4: Carol, 5: Eric
    # Foods: 0: stew, 1: grilled cheese, 2: stir fry, 3: soup, 4: pizza, 5: spaghetti
    # Heights: 0: tall, 1: average, 2: super tall, 3: very short, 4: very tall, 5: short
    # Drinks: 0: root beer, 1: boba tea, 2: coffee, 3: water, 4: tea, 5: milk
    # Pets: 0: hamster, 1: fish, 2: cat, 3: dog, 4: bird, 5: rabbit
    # Phones: 0: samsung galaxy s21, 1: xiaomi mi 11, 2: google pixel 6, 3: iphone 13, 4: huawei p50, 5: oneplus 9

    # ---------------------------------------------------------------------------
    # Add the constraints from the puzzle clues.

    # 1. The person who uses an iPhone 13 is in the third house.
    solver.add(phones[2] == 3)

    # 2. Bob is the person who is tall.
    for i in range(n):
        solver.add(Implies(names[i] == 1, heights[i] == 0))

    # 3. The person who loves the soup is in the second house.
    solver.add(foods[1] == 3)

    # 4. The root beer lover is directly left of the person who uses a Xiaomi Mi 11.
    solver.add(Or([And(drinks[i] == 0, phones[i+1] == 1) for i in range(n-1)]))

    # 5. The person who uses a Huawei P50 is directly left of the person who loves eating grilled cheese.
    solver.add(Or([And(phones[i] == 4, foods[i+1] == 1) for i in range(n-1)]))

    # 6. The person who loves stir fry is the person who likes milk.
    for i in range(n):
        solver.add((foods[i] == 2) == (drinks[i] == 5))

    # 7. The person who loves eating grilled cheese is the person who is tall.
    for i in range(n):
        solver.add((foods[i] == 1) == (heights[i] == 0))

    # 8. The person who uses a Xiaomi Mi 11 is the coffee drinker.
    for i in range(n):
        solver.add((phones[i] == 1) == (drinks[i] == 2))

    # 9. The person who uses a OnePlus 9 is Arnold.
    for i in range(n):
        solver.add((phones[i] == 5) == (names[i] == 0))

    # 10. The person who owns a rabbit is not in the fifth house.
    solver.add(pets[4] != 5)

    # 11. The person with a pet hamster is somewhere to the right of the person who uses a Google Pixel 6.
    for i in range(n):
        for j in range(n):
            solver.add(Implies(And(phones[i] == 2, pets[j] == 0), j > i))

    # 12. The person who is super tall is the person with an aquarium of fish.
    for i in range(n):
        solver.add((heights[i] == 2) == (pets[i] == 1))

    # 13. The person with an aquarium of fish is Alice.
    for i in range(n):
        solver.add((pets[i] == 1) == (names[i] == 3))

    # 14. The tea drinker is directly left of the person who is a pizza lover.
    solver.add(Or([And(drinks[i] == 4, foods[i+1] == 4) for i in range(n-1)]))

    # 15. The person who uses a Samsung Galaxy S21 is Carol.
    for i in range(n):
        solver.add((phones[i] == 0) == (names[i] == 4))

    # 16. The person who is a pizza lover is the person who is short.
    for i in range(n):
        solver.add((foods[i] == 4) == (heights[i] == 5))

    # 17. Arnold is the person who is very tall.
    for i in range(n):
        solver.add((names[i] == 0) == (heights[i] == 4))

    # 18. The person who loves the spaghetti eater is the person who uses a Google Pixel 6.
    # Interpreting "loves the spaghetti" (spaghetti is food index 5)
    for i in range(n):
        solver.add((foods[i] == 5) == (phones[i] == 2))

    # 19. The boba tea drinker is somewhere to the right of the person who loves the soup.
    # Since the soup lover is in the second house (index 1), any boba tea drinker must be in a house with index > 1.
    for j in range(n):
        solver.add(Implies(drinks[j] == 1, j > 1))

    # 20. The person with a pet hamster is not in the fifth house.
    solver.add(pets[4] != 0)

    # 21. The person who is very tall is not in the second house.
    solver.add(heights[1] != 4)

    # 22. The person who is super tall is somewhere to the left of Peter.
    for i in range(n):
        for j in range(n):
            solver.add(Implies(And(heights[i] == 2, names[j] == 2), i < j))

    # 23. The person who is very short is the person who loves the spaghetti eater.
    # Interpret as: very short (height index 3) <-> loves spaghetti (food index 5)
    for i in range(n):
        solver.add((heights[i] == 3) == (foods[i] == 5))

    # 24. The person who keeps a pet bird is somewhere to the left of the person who loves the spaghetti eater.
    for i in range(n):
        for j in range(n):
            solver.add(Implies(And(pets[i] == 4, foods[j] == 5), i < j))

    # 25. The person with an aquarium of fish is directly left of Eric.
    solver.add(Or([And(pets[i] == 1, names[i+1] == 5) for i in range(n-1)]))

    # 26. The person who owns a dog is the person who likes milk.
    for i in range(n):
        solver.add((pets[i] == 3) == (drinks[i] == 5))

    # ---------------------------------------------------------------------------
    # Solve the puzzle.
    if solver.check() == sat:
        model = solver.model()

        # Mappings for output conversion.
        name_map   = ["Arnold", "Bob", "Peter", "Alice", "Carol", "Eric"]
        food_map   = ["stew", "grilled cheese", "stir fry", "soup", "pizza", "spaghetti"]
        height_map = ["tall", "average", "super tall", "very short", "very tall", "short"]
        drink_map  = ["root beer", "boba tea", "coffee", "water", "tea", "milk"]
        pet_map    = ["hamster", "fish", "cat", "dog", "bird", "rabbit"]
        phone_map  = ["samsung galaxy s21", "xiaomi mi 11", "google pixel 6", "iphone 13", "huawei p50", "oneplus 9"]

        # Build the solution rows.
        rows = []
        for i in range(n):
            row = [
                str(i+1),
                name_map[model.evaluate(names[i]).as_long()],
                food_map[model.evaluate(foods[i]).as_long()],
                height_map[model.evaluate(heights[i]).as_long()],
                drink_map[model.evaluate(drinks[i]).as_long()],
                pet_map[model.evaluate(pets[i]).as_long()],
                phone_map[model.evaluate(phones[i]).as_long()]
            ]
            rows.append(row)

        solution = {
            "solution": {
                "header": ["House", "Name", "Food", "Height", "Drink", "Pet", "PhoneModel"],
                "rows": rows
            }
        }

        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"solution": "No solution found"}))

if __name__ == "__main__":
    main()