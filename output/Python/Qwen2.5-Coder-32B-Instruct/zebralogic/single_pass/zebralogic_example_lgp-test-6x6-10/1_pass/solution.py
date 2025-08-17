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
    for name_perm in itertools.permutations(names):
        for food_perm in itertools.permutations(foods):
            for height_perm in itertools.permutations(heights):
                for drink_perm in itertools.permutations(drinks):
                    for pet_perm in itertools.permutations(pets):
                        for phone_perm in itertools.permutations(phones):
                            # Check all constraints
                            if (phone_perm[2] == "iphone 13" and
                                name_perm[heights.index("tall")] == "Bob" and
                                food_perm[1] == "soup" and
                                drink_perm[phones.index("xiaomi mi 11") - 1] == "root beer" and
                                phone_perm[drinks.index("grilled cheese") - 1] == "huawei p50" and
                                food_perm[drinks.index("milk")] == "stir fry" and
                                name_perm[heights.index("tall")] == name_perm[foods.index("grilled cheese")] and
                                drink_perm[phones.index("xiaomi mi 11")] == "coffee" and
                                name_perm[phones.index("oneplus 9")] == "Arnold" and
                                pet_perm[4] != "rabbit" and
                                pet_perm.index("hamster") > phone_perm.index("google pixel 6") and
                                name_perm[heights.index("super tall")] == name_perm[pets.index("fish")] and
                                name_perm[pets.index("fish")] == "Alice" and
                                drink_perm[food_perm.index("pizza") - 1] == "tea" and
                                name_perm[phones.index("samsung galaxy s21")] == "Carol" and
                                name_perm[heights.index("short")] == name_perm[foods.index("pizza")] and
                                name_perm[heights.index("very tall")] == "Arnold" and
                                name_perm[phones.index("google pixel 6")] == name_perm[foods.index("spaghetti")] and
                                drink_perm[food_perm.index("soup") + 1] == "boba tea" and
                                pet_perm[4] != "hamster" and
                                name_perm[heights.index("very tall")] != name_perm[1] and
                                name_perm[heights.index("super tall")] < name_perm.index("Peter") and
                                name_perm[heights.index("very short")] == name_perm[foods.index("spaghetti")] and
                                pet_perm.index("bird") < food_perm.index("spaghetti") and
                                name_perm[pets.index("fish")] == name_perm[foods.index("spaghetti") - 1] and
                                name_perm[pets.index("dog")] == name_perm[drinks.index("milk")]):
                                
                                solution = {
                                    "solution": {
                                        "header": ["House", "Name", "Food", "Height", "Drink", "Pet", "PhoneModel"],
                                        "rows": []
                                    }
                                }
                                for i in range(6):
                                    solution["solution"]["rows"].append([
                                        str(houses[i]),
                                        name_perm[i],
                                        food_perm[i],
                                        height_perm[i],
                                        drink_perm[i],
                                        pet_perm[i],
                                        phone_perm[i]
                                    ])
                                return json.dumps(solution, indent=2)

print(solve_puzzle())