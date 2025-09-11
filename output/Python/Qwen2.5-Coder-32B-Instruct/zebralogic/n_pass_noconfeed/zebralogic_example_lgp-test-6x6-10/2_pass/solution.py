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
        # Apply all clues
        if phone_order[2] != phones.index("iphone 13"):
            return False
        if height_order[name_order.index("Bob")] != heights.index("tall"):
            return False
        if food_order[1] != foods.index("soup"):
            return False
        if drink_order[phone_order.index("xiaomi mi 11") - 1] != drinks.index("root beer"):
            return False
        if phone_order[drink_order.index("grilled cheese") - 1] != phones.index("huawei p50"):
            return False
        if food_order[drinks.index("milk")] != foods.index("stir fry"):
            return False
        if food_order[height_order.index("tall")] != foods.index("grilled cheese"):
            return False
        if drink_order[phone_order.index("xiaomi mi 11")] != drinks.index("coffee"):
            return False
        if phone_order[name_order.index("Arnold")] != phones.index("oneplus 9"):
            return False
        if pet_order[4] == pets.index("rabbit"):
            return False
        if pet_order[phone_order.index("google pixel 6") + 1] != pets.index("hamster"):
            return False
        if height_order[pet_order.index("fish")] != heights.index("super tall"):
            return False
        if pet_order[height_order.index("super tall")] != pets.index("fish"):
            return False
        if name_order[height_order.index("super tall")] != names.index("Alice"):
            return False
        if drink_order[food_order.index("pizza") - 1] != drinks.index("tea"):
            return False
        if phone_order[name_order.index("Carol")] != phones.index("samsung galaxy s21"):
            return False
        if food_order[height_order.index("short")] != foods.index("pizza"):
            return False
        if height_order[name_order.index("Arnold")] != heights.index("very tall"):
            return False
        if food_order[phone_order.index("google pixel 6")] != foods.index("spaghetti"):
            return False
        if drink_order[foods.index("spaghetti")] != drinks.index("milk"):
            return False
        if height_order[name_order.index("Arnold")] == heights.index("tall"):
            return False
        if height_order[pet_order.index("fish") + 1] != heights.index("super tall"):
            return False
        if height_order[food_order.index("spaghetti")] != heights.index("very short"):
            return False
        if pet_order[food_order.index("spaghetti") - 1] != pets.index("bird"):
            return False
        if name_order[height_order.index("super tall")] != names.index("Eric"):
            return False
        if pet_order[drinks.index("milk")] != pets.index("dog"):
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