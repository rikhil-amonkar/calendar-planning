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

    for name_perm in itertools.permutations(names):
        for food_perm in itertools.permutations(foods):
            for car_perm in itertools.permutations(cars):
                for phone_perm in itertools.permutations(phones):
                    for occupation_perm in itertools.permutations(occupations):
                        for drink_perm in itertools.permutations(drinks):
                            # Apply clues
                            if (
                                # Clue 1
                                drink_perm[car_perm.index("honda civic")] == "root beer" and
                                # Clue 2
                                drink_perm.index("milk") + 1 == food_perm.index("grilled cheese") and
                                # Clue 3
                                phone_perm[name_perm.index("Alice")] == "samsung galaxy s21" and
                                # Clue 4
                                food_perm[name_perm.index("Alice")] == "stir fry" and
                                # Clue 5
                                drink_perm[-1] != "tea" and
                                # Clue 6
                                car_perm.index("bmw 3 series") < drink_perm.index("tea") and
                                # Clue 7
                                occupation_perm[name_perm.index("Arnold")] == "doctor" and
                                # Clue 8
                                drink_perm[phone_perm.index("iphone 13")] == "coffee" and
                                # Clue 9
                                occupation_perm[car_perm.index("bmw 3 series")] == "engineer" and
                                # Clue 10
                                drink_perm[phone_perm.index("iphone 13")] == "stew" and
                                # Clue 11
                                occupation_perm.index("doctor") + 1 == phone_perm.index("oneplus 9") and
                                # Clue 12
                                car_perm.index("honda civic") + 1 == food_perm.index("spaghetti") and
                                # Clue 13
                                drink_perm[phone_perm.index("google pixel 6")] == "tea" and
                                # Clue 14
                                occupation_perm[name_perm.index("Alice")] == "artist" and
                                # Clue 15
                                abs(name_perm.index("Alice") - car_perm.index("ford f150")) == 2 and
                                # Clue 16
                                car_perm[name_perm.index("Arnold")] == "toyota camry" and
                                # Clue 17
                                name_perm[3] == "Eric" and
                                # Clue 18
                                occupation_perm[phone_perm.index("oneplus 9")] == "lawyer" and
                                # Clue 19
                                food_perm[name_perm.index("Peter")] == "grilled cheese"
                            ):
                                solution = {
                                    "solution": {
                                        "header": ["House", "Name", "Food", "CarModel", "PhoneModel", "Occupation", "Drink"],
                                        "rows": [
                                            [str(houses[i]), name_perm[i], food_perm[i], car_perm[i], phone_perm[i], occupation_perm[i], drink_perm[i]]
                                            for i in range(5)
                                        ]
                                    }
                                }
                                return json.dumps(solution)

print(solve_puzzle())