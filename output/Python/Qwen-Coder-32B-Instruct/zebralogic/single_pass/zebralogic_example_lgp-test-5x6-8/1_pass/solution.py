import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Eric", "Peter", "Arnold", "Bob", "Alice"]
    house_styles = ["modern", "craftsman", "ranch", "victorian", "colonial"]
    mothers_names = ["Penny", "Kailyn", "Holly", "Janelle", "Aniya"]
    phone_models = ["oneplus 9", "google pixel 6", "huawei p50", "iphone 13", "samsung galaxy s21"]
    drinks = ["coffee", "water", "root beer", "tea", "milk"]
    animals = ["fish", "dog", "horse", "bird", "cat"]

    # Generate all possible permutations
    all_permutations = list(itertools.permutations(range(5)))

    # Check each permutation against the clues
    for names_order in all_permutations:
        for styles_order in all_permutations:
            for mothers_names_order in all_permutations:
                for phones_order in all_permutations:
                    for drinks_order in all_permutations:
                        for animals_order in all_permutations:
                            # Create dictionaries for quick lookup
                            name_to_house = {name: i for i, name in enumerate(names_order)}
                            style_to_house = {style: i for i, style in enumerate(styles_order)}
                            mother_to_house = {mother: i for i, mother in enumerate(mothers_names_order)}
                            phone_to_house = {phone: i for i, phone in enumerate(phones_order)}
                            drink_to_house = {drink: i for i, drink in enumerate(drinks_order)}
                            animal_to_house = {animal: i for i, animal in enumerate(animals_order)}

                            # Check each clue
                            if (
                                # Clue 1
                                phone_to_house["google pixel 6"] != 0 and
                                # Clue 2
                                drink_to_house["water"] == name_to_house["Alice"] and
                                # Clue 3
                                style_to_house["colonial"] > phone_to_house["huawei p50"] and
                                # Clue 4
                                animal_to_house["horse"] == phone_to_house["oneplus 9"] and
                                # Clue 5
                                style_to_house["ranch"] == mother_to_house["Kailyn"] and
                                # Clue 6
                                drink_to_house["root beer"] == animal_to_house["cat"] and
                                # Clue 7
                                style_to_house["colonial"] != 3 and
                                # Clue 8
                                animal_to_house["bird"] == 3 and
                                # Clue 9
                                drink_to_house["tea"] == name_to_house["Bob"] and
                                # Clue 10
                                drink_to_house["tea"] > mother_to_house["Kailyn"] and
                                # Clue 11
                                drink_to_house["root beer"] < mother_to_house["Kailyn"] and
                                # Clue 12
                                animal_to_house["horse"] == style_to_house["modern"] and
                                # Clue 13
                                phone_to_house["iphone 13"] == drink_to_house["milk"] and
                                # Clue 14
                                animal_to_house["dog"] == drink_to_house["milk"] and
                                # Clue 15
                                phone_to_house["google pixel 6"] == style_to_house["craftsman"] and
                                # Clue 16
                                name_to_house["Eric"] != 1 and
                                # Clue 17
                                drink_to_house["tea"] == 3 and
                                # Clue 18
                                animal_to_house["horse"] == 2 and
                                # Clue 19
                                style_to_house["modern"] == mother_to_house["Penny"] and
                                # Clue 20
                                drink_to_house["root beer"] == name_to_house["Peter"] and
                                # Clue 21
                                mother_to_house["Aniya"] != 3 and
                                # Clue 22
                                mother_to_house["Janelle"] == drink_to_house["water"]
                            ):
                                # If all clues are satisfied, construct the solution
                                solution = {
                                    "solution": {
                                        "header": ["House", "Name", "Style", "Mother's Name", "Phone Model", "Drink", "Animal"],
                                        "rows": []
                                    }
                                }
                                for house in range(5):
                                    solution["solution"]["rows"].append([
                                        str(house + 1),
                                        names[names_order[house]],
                                        house_styles[styles_order[house]],
                                        mothers_names[mothers_names_order[house]],
                                        phone_models[phones_order[house]],
                                        drinks[drinks_order[house]],
                                        animals[animals_order[house]]
                                    ])
                                return json.dumps(solution, indent=2)

# Run the solver and print the result
print(solve_puzzle())