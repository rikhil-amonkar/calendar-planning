import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Arnold", "Bob", "Peter", "Alice", "Carol", "Eric"]
    foods = ["stew", "grilled cheese", "stir fry", "soup", "pizza", "spaghetti"]
    heights = ["tall", "average", "super tall", "very short", "very tall", "short"]
    drinks = ["root beer", "boba tea", "coffee", "water", "tea", "milk"]
    pets = ["hamster", "fish", "cat", "dog", "bird", "rabbit"]
    phones = ["samsung galaxy s21", "xiaomi mi 11", "google pixel 6", "iphone 13", "huawei p50", "oneplus 9"]

    # Generate all possible permutations
    permutations = list(itertools.permutations(range(6)))

    def is_valid_solution(name_order, food_order, height_order, drink_order, pet_order, phone_order):
        # Create reverse mappings for quick lookup
        name_to_index = {name: idx for idx, name in enumerate(names)}
        food_to_index = {food: idx for idx, food in enumerate(foods)}
        height_to_index = {height: idx for idx, height in enumerate(heights)}
        drink_to_index = {drink: idx for idx, drink in enumerate(drinks)}
        pet_to_index = {pet: idx for idx, pet in enumerate(pets)}
        phone_to_index = {phone: idx for idx, phone in enumerate(phones)}

        # Apply all clues
        if phone_order[2] != phone_to_index["iphone 13"]:
            return False
        if height_order[name_to_index.get("Bob", -1)] != height_to_index.get("tall", -1):
            return False
        if food_order[1] != food_to_index.get("soup", -1):
            return False
        if drink_order[phone_to_index.get("xiaomi mi 11", -1) - 1] != drink_to_index.get("root beer", -1):
            return False
        if phone_order[drink_to_index.get("grilled cheese", -1) - 1] != phone_to_index.get("huawei p50", -1):
            return False
        if food_order[drink_to_index.get("milk", -1)] != food_to_index.get("stir fry", -1):
            return False
        if food_order[height_to_index.get("tall", -1)] != food_to_index.get("grilled cheese", -1):
            return False
        if drink_order[phone_to_index.get("xiaomi mi 11", -1)] != drink_to_index.get("coffee", -1):
            return False
        if phone_order[name_to_index.get("Arnold", -1)] != phone_to_index.get("oneplus 9", -1):
            return False
        if pet_order[4] == pet_to_index.get("rabbit", -1):
            return False
        if pet_order[phone_to_index.get("google pixel 6", -1) + 1] != pet_to_index.get("hamster", -1):
            return False
        if height_order[pet_to_index.get("fish", -1)] != height_to_index.get("super tall", -1):
            return False
        if pet_order[height_to_index.get("super tall", -1)] != pet_to_index.get("fish", -1):
            return False
        if name_order[height_to_index.get("super tall", -1)] != name_to_index.get("Alice", -1):
            return False
        if drink_order[food_to_index.get("pizza", -1) - 1] != drink_to_index.get("tea", -1):
            return False
        if phone_order[name_to_index.get("Carol", -1)] != phone_to_index.get("samsung galaxy s21", -1):
            return False
        if food_order[height_to_index.get("short", -1)] != food_to_index.get("pizza", -1):
            return False
        if height_order[name_to_index.get("Arnold", -1)] != height_to_index.get("very tall", -1):
            return False
        if food_order[phone_to_index.get("google pixel 6", -1)] != food_to_index.get("spaghetti", -1):
            return False
        if drink_order[food_to_index.get("spaghetti", -1)] != drink_to_index.get("milk", -1):
            return False
        if height_order[name_to_index.get("Arnold", -1)] == height_to_index.get("tall", -1):
            return False
        if height_order[pet_to_index.get("fish", -1) + 1] != height_to_index.get("super tall", -1):
            return False
        if height_order[food_to_index.get("spaghetti", -1)] != height_to_index.get("very short", -1):
            return False
        if pet_order[food_to_index.get("spaghetti", -1) - 1] != pet_to_index.get("bird", -1):
            return False
        if name_order[height_to_index.get("super tall", -1)] != name_to_index.get("Eric", -1):
            return False
        if pet_order[drink_to_index.get("milk", -1)] != pet_to_index.get("dog", -1):
            return False
        return True

    for name_order in permutations:
        for food_order in permutations:
            for height_order in permutations:
                for drink_order in permutations:
                    for pet_order in permutations:
                        for phone_order in permutations:
                            if is_valid_solution(name_order, food_order, height_order, drink_order, pet_order, phone_order):
                                solution = []
                                for house in range(6):
                                    solution.append([
                                        str(house + 1),
                                        names[name_order[house]],
                                        foods[food_order[house]],
                                        heights[height_order[house]],
                                        drinks[drink_order[house]],
                                        pets[pet_order[house]],
                                        phones[phone_order[house]]
                                    ])
                                return {
                                    "solution": {
                                        "header": ["House", "Name", "Food", "Height", "Drink", "Pet", "PhoneModel"],
                                        "rows": solution
                                    }
                                }

# Solve the puzzle and print the solution as JSON
print(json.dumps(solve_puzzle(), indent=2))