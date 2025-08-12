import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Arnold", "Bob", "Peter", "Alice", "Carol", "Eric"]
    lunches = ["stew", "grilled cheese", "stir fry", "soup", "pizza", "spaghetti"]
    heights = ["tall", "average", "super tall", "very short", "very tall", "short"]
    drinks = ["root beer", "boba tea", "coffee", "water", "tea", "milk"]
    pets = ["hamster", "fish", "cat", "dog", "bird", "rabbit"]
    phones = ["samsung galaxy s21", "xiaomi mi 11", "google pixel 6", "iphone 13", "huawei p50", "oneplus 9"]

    # Generate all possible permutations for each category
    all_permutations = list(itertools.permutations(range(6)))

    # Check all combinations
    for name_order in all_permutations:
        for lunch_order in all_permutations:
            for height_order in all_permutations:
                for drink_order in all_permutations:
                    for pet_order in all_permutations:
                        for phone_order in all_permutations:
                            # Create a dictionary to store the current assignment
                            assignment = {
                                "name": {names[i]: i for i in range(6)},
                                "lunch": {lunches[i]: i for i in range(6)},
                                "height": {heights[i]: i for i in range(6)},
                                "drink": {drinks[i]: i for i in range(6)},
                                "pet": {pets[i]: i for i in range(6)},
                                "phone": {phones[i]: i for i in range(6)}
                            }

                            # Apply the clues
                            if (assignment["phone"]["iphone 13"] == 2 and
                                assignment["name"]["Bob"] == assignment["height"]["tall"] and
                                assignment["lunch"]["soup"] == 1 and
                                assignment["drink"]["root beer"] + 1 == assignment["phone"]["xiaomi mi 11"] and
                                assignment["phone"]["huawei p50"] + 1 == assignment["lunch"]["grilled cheese"] and
                                assignment["lunch"]["stir fry"] == assignment["drink"]["milk"] and
                                assignment["lunch"]["grilled cheese"] == assignment["height"]["tall"] and
                                assignment["phone"]["xiaomi mi 11"] == assignment["drink"]["coffee"] and
                                assignment["name"]["Arnold"] == assignment["phone"]["oneplus 9"] and
                                assignment["pet"]["rabbit"] != 4 and
                                assignment["pet"]["hamster"] > assignment["phone"]["google pixel 6"] and
                                assignment["height"]["super tall"] == assignment["pet"]["fish"] and
                                assignment["pet"]["fish"] == assignment["name"]["Alice"] and
                                assignment["drink"]["tea"] + 1 == assignment["lunch"]["pizza"] and
                                assignment["name"]["Carol"] == assignment["phone"]["samsung galaxy s21"] and
                                assignment["lunch"]["pizza"] == assignment["height"]["short"] and
                                assignment["name"]["Arnold"] == assignment["height"]["very tall"] and
                                assignment["lunch"]["spaghetti"] == assignment["phone"]["google pixel 6"] and
                                assignment["drink"]["boba tea"] > assignment["lunch"]["soup"] and
                                assignment["pet"]["hamster"] != 4 and
                                assignment["height"]["very tall"] != 1 and
                                assignment["height"]["super tall"] < assignment["name"]["Peter"] and
                                assignment["height"]["very short"] == assignment["lunch"]["spaghetti"] and
                                assignment["pet"]["bird"] < assignment["lunch"]["spaghetti"] and
                                assignment["pet"]["fish"] + 1 == assignment["name"]["Eric"] and
                                assignment["pet"]["dog"] == assignment["drink"]["milk"]):
                                
                                # If all clues are satisfied, construct the solution
                                solution = []
                                for house in range(6):
                                    name = names[name_order[house]]
                                    lunch = lunches[lunch_order[house]]
                                    height = heights[height_order[house]]
                                    drink = drinks[drink_order[house]]
                                    pet = pets[pet_order[house]]
                                    phone = phones[phone_order[house]]
                                    solution.append([str(house + 1), name, lunch, height, drink, pet, phone])
                                
                                # Return the solution in JSON format
                                return json.dumps({
                                    "solution": {
                                        "header": ["House", "Name", "Lunch", "Height", "Drink", "Pet", "Phone"],
                                        "rows": solution
                                    }
                                }, indent=2)

# Solve the puzzle and print the result
print(solve_puzzle())