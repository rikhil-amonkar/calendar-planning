import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Eric", "Peter", "Arnold", "Alice", "Bob"]
    lunches = ["stir fry", "spaghetti", "stew", "grilled cheese", "pizza"]
    cars = ["ford f150", "tesla model 3", "bmw 3 series", "toyota camry", "honda civic"]
    phones = ["iphone 13", "google pixel 6", "samsung galaxy s21", "oneplus 9", "huawei p50"]
    occupations = ["teacher", "lawyer", "doctor", "artist", "engineer"]
    drinks = ["tea", "milk", "water", "root beer", "coffee"]

    # Generate all possible permutations
    all_permutations = list(itertools.permutations(range(5)))

    # Check each permutation against the clues
    for name_order in all_permutations:
        for lunch_order in all_permutations:
            for car_order in all_permutations:
                for phone_order in all_permutations:
                    for occupation_order in all_permutations:
                        for drink_order in all_permutations:
                            # Create a dictionary to store the current configuration
                            config = {
                                "name": [names[i] for i in name_order],
                                "lunch": [lunches[i] for i in lunch_order],
                                "car": [cars[i] for i in car_order],
                                "phone": [phones[i] for i in phone_order],
                                "occupation": [occupations[i] for i in occupation_order],
                                "drink": [drinks[i] for i in drink_order]
                            }

                            # Apply the clues to check if the configuration is valid
                            if (config["drink"][car_order.index("honda civic")] == "root beer" and
                                config["drink"][lunch_order.index("grilled cheese") - 1] == "milk" and
                                config["phone"][name_order.index("Alice")] == "samsung galaxy s21" and
                                config["lunch"][name_order.index("Alice")] == "stir fry" and
                                config["drink"].index("tea") != 4 and
                                car_order.index("bmw 3 series") < config["drink"].index("tea") and
                                config["occupation"][name_order.index("Arnold")] == "doctor" and
                                config["phone"][drink_order.index("coffee")] == "iphone 13" and
                                config["occupation"][car_order.index("bmw 3 series")] == "engineer" and
                                config["phone"][lunch_order.index("stew")] == "iphone 13" and
                                name_order.index("Arnold") + 1 == phone_order.index("oneplus 9") and
                                car_order.index("honda civic") + 1 == lunch_order.index("spaghetti") and
                                config["phone"][drink_order.index("tea")] == "google pixel 6" and
                                config["occupation"][name_order.index("Alice")] == "artist" and
                                abs(name_order.index("Alice") - car_order.index("ford f150")) == 2 and
                                config["car"][name_order.index("Arnold")] == "toyota camry" and
                                name_order[3] == "Eric" and
                                phone_order.index("oneplus 9") == occupation_order.index("lawyer") and
                                config["lunch"][name_order.index("Peter")] == "grilled cheese"):
                                
                                # If all clues are satisfied, construct the solution
                                solution = {
                                    "solution": {
                                        "header": ["House", "Name", "Lunch", "Car", "Phone", "Occupation", "Drink"],
                                        "rows": []
                                    }
                                }
                                for house in range(5):
                                    solution["solution"]["rows"].append([
                                        str(house + 1),
                                        config["name"][house],
                                        config["lunch"][house],
                                        config["car"][house],
                                        config["phone"][house],
                                        config["occupation"][house],
                                        config["drink"][house]
                                    ])
                                return json.dumps(solution, indent=2)

# Solve the puzzle and print the result
print(solve_puzzle())