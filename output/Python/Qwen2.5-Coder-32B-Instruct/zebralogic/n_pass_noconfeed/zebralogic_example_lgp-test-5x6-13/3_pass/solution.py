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
                            try:
                                honda_civic_house = next(house for house, car in config["car"].items() if car == "honda civic")
                                grilled_cheese_house = next(house for house, food in config["food"].items() if food == "grilled cheese")
                                alice_house = next(house for house, name in config["name"].items() if name == "Alice")
                                arnold_house = next(house for house, name in config["name"].items() if name == "Arnold")
                                tea_house = next(house for house, drink in config["drink"].items() if drink == "tea")
                                coffee_house = next(house for house, drink in config["drink"].items() if drink == "coffee")
                                bmw_3_series_house = next(house for house, car in config["car"].items() if car == "bmw 3 series")
                                ford_f150_house = next(house for house, car in config["car"].items() if car == "ford f150")
                                lawyer_house = next(house for house, occupation in config["occupation"].items() if occupation == "lawyer")
                                peter_house = next(house for house, name in config["name"].items() if name == "Peter")

                                if (config["drink"][honda_civic_house] == "root beer" and
                                    config["drink"][grilled_cheese_house - 1] == "milk" and
                                    config["phone"][alice_house] == "samsung galaxy s21" and
                                    config["food"][alice_house] == "stir fry" and
                                    config["drink"][5] != "tea" and
                                    bmw_3_series_house < tea_house and
                                    config["occupation"][arnold_house] == "doctor" and
                                    config["phone"][coffee_house] == "iphone 13" and
                                    config["occupation"][bmw_3_series_house] == "engineer" and
                                    config["food"][config["phone"].get("iphone 13")] == "stew" and
                                    config["occupation"][arnold_house + 1] == "lawyer" and
                                    honda_civic_house < config["food"].get("spaghetti") and
                                    config["phone"][tea_house] == "google pixel 6" and
                                    config["occupation"][alice_house] == "artist" and
                                    abs(alice_house - ford_f150_house) == 2 and
                                    config["car"][arnold_house] == "toyota camry" and
                                    config["name"][4] == "Eric" and
                                    config["phone"][lawyer_house] == "oneplus 9" and
                                    config["food"][peter_house] == "grilled cheese"):
                                    
                                    solutions.append(config)
                            except StopIteration:
                                continue

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