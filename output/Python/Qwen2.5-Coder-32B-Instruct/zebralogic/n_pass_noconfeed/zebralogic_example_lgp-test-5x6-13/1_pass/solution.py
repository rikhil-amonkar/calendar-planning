import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]
    names = ["Eric", "Peter", "Arnold", "Alice", "Bob"]
    foods = ["stir fry", "spaghetti", "stew", "grilled cheese", "pizza"]
    cars = ["ford f150", "tesla model 3", "bmw 3 series", "toyota camry", "honda civic"]
    phones = ["iphone 13", "google pixel 6", "samsung galaxy s21", "oneplus 9", "huawei p50"]
    occupations = ["teacher", "lawyer", "doctor", "artist", "engineer"]
    drinks = ["tea", "milk", "water", "root beer", "coffee"]

    # Generate all possible permutations
    permutations = list(itertools.permutations(houses))
    solutions = []

    for name_order in permutations:
        for food_order in permutations:
            for car_order in permutations:
                for phone_order in permutations:
                    for occupation_order in permutations:
                        for drink_order in permutations:
                            # Create a dictionary to store the current configuration
                            config = {
                                "name": {house: name_order[i] for i, house in enumerate(houses)},
                                "food": {house: food_order[i] for i, house in enumerate(houses)},
                                "car": {house: car_order[i] for i, house in enumerate(houses)},
                                "phone": {house: phone_order[i] for i, house in enumerate(houses)},
                                "occupation": {house: occupation_order[i] for i, house in enumerate(houses)},
                                "drink": {house: drink_order[i] for i, house in enumerate(houses)}
                            }

                            # Check all the clues
                            if (config["drink"][config["car"]["honda civic"]] == "root beer" and
                                config["drink"][config["food"]["grilled cheese"] - 1] == "milk" and
                                config["phone"][config["name"]["Alice"]] == "samsung galaxy s21" and
                                config["food"][config["name"]["Alice"]] == "stir fry" and
                                config["drink"][5] != "tea" and
                                config["car"]["bmw 3 series"] < config["drink"]["tea"] and
                                config["occupation"][config["name"]["Arnold"]] == "doctor" and
                                config["phone"][config["drink"]["coffee"]] == "iphone 13" and
                                config["occupation"][config["car"]["bmw 3 series"]] == "engineer" and
                                config["food"][config["phone"]["iphone 13"]] == "stew" and
                                config["occupation"][config["name"]["Arnold"] + 1] == "lawyer" and
                                config["car"]["honda civic"] < config["food"]["spaghetti"] and
                                config["phone"][config["drink"]["tea"]] == "google pixel 6" and
                                config["occupation"][config["name"]["Alice"]] == "artist" and
                                abs(config["name"]["Alice"] - config["car"]["ford f150"]) == 2 and
                                config["car"][config["name"]["Arnold"]] == "toyota camry" and
                                config["name"][4] == "Eric" and
                                config["phone"][config["occupation"]["lawyer"]] == "oneplus 9" and
                                config["food"][config["name"]["Peter"]] == "grilled cheese"):
                                
                                solutions.append(config)

    # Convert the solution to the required format
    if solutions:
        solution = solutions[0]
        result = {
            "solution": {
                "header": ["House", "Name", "Food", "CarModel", "PhoneModel", "Occupation", "Drink"],
                "rows": []
            }
        }
        for house in houses:
            row = [
                str(house),
                solution["name"][house],
                solution["food"][house],
                solution["car"][house],
                solution["phone"][house],
                solution["occupation"][house],
                solution["drink"][house]
            ]
            result["solution"]["rows"].append(row)
        return json.dumps(result, indent=2)
    else:
        return json.dumps({"solution": {"header": [], "rows": []}})

if __name__ == "__main__":
    print(solve_puzzle())