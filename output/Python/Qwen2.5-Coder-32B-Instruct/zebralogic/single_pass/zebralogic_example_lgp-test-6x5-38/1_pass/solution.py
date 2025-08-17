import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Arnold", "Carol", "Eric", "Bob", "Alice", "Peter"]
    birthdays = ["feb", "mar", "sept", "jan", "may", "april"]
    foods = ["stew", "soup", "grilled cheese", "stir fry", "spaghetti", "pizza"]
    heights = ["very short", "average", "super tall", "short", "very tall", "tall"]
    cars = ["chevrolet silverado", "ford f150", "bmw 3 series", "tesla model 3", "toyota camry", "honda civic"]

    for name_perm in itertools.permutations(names):
        for birthday_perm in itertools.permutations(birthdays):
            for food_perm in itertools.permutations(foods):
                for height_perm in itertools.permutations(heights):
                    for car_perm in itertools.permutations(cars):
                        # Apply constraints
                        if (car_perm[house_index(name_perm, "Honda Civic")] == "short" and
                            car_perm[4] == "ford f150" and
                            house_index(food_perm, "stir fry") < house_index(name_perm, "Eric") and
                            house_index(birthday_perm, "may") < house_index(name_perm, "Carol") and
                            house_index(height_perm, "very short") < house_index(birthday_perm, "april") and
                            car_perm[2] != "bmw 3 series" and
                            abs(house_index(food_perm, "stir fry") - house_index(food_perm, "pizza")) == 2 and
                            house_index(food_perm, "soup") + 1 == house_index(name_perm, "Eric") and
                            abs(house_index(food_perm, "spaghetti") - house_index(birthday_perm, "may")) == 1 and
                            house_index(name_perm, "Alice") + 1 == house_index(car_perm, "bmw 3 series") and
                            car_perm[house_index(name_perm, "Tesla Model 3")] < house_index(height_perm, "tall") and
                            car_perm[house_index(height_perm, "very tall")] == "toyota camry" and
                            house_index(name_perm, "Peter") + 1 == house_index(food_perm, "pizza") and
                            food_perm[2] != "stew" and
                            abs(house_index(birthday_perm, "sept") - house_index(height_perm, "very short")) == 1 and
                            abs(house_index(birthday_perm, "mar") - house_index(height_perm, "super tall")) == 1 and
                            name_perm[house_index(height_perm, "tall")] == "Bob" and
                            house_index(birthday_perm, "may") > house_index(name_perm, "Alice") and
                            height_perm[3] == "very short" and
                            birthday_perm[house_index(height_perm, "short")] == "mar" and
                            car_perm[house_index(name_perm, "Carol")] == "tesla model 3" and
                            birthday_perm[house_index(name_perm, "Eric")] == "jan"):
                            
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Birthday", "Food", "Height", "CarModel"],
                                    "rows": [
                                        [str(houses[i]), name_perm[i], birthday_perm[i], food_perm[i], height_perm[i], car_perm[i]]
                                        for i in range(6)
                                    ]
                                }
                            }
                            return json.dumps(solution, indent=2)

def house_index(lst, value):
    return lst.index(value)

print(solve_puzzle())