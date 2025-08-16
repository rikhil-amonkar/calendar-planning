#!/usr/bin/env python3
import itertools
import json
import sys

# Domains for each attribute.
NAMES = ["Arnold", "Carol", "Eric", "Bob", "Alice", "Peter"]
BIRTHDAYS = ["feb", "mar", "sept", "jan", "may", "april"]
FOODS = ["stew", "soup", "grilled cheese", "stir fry", "spaghetti", "pizza"]
HEIGHTS = ["very short", "average", "super tall", "short", "very tall", "tall"]
CARS = ["chevrolet silverado", "ford f150", "bmw 3 series", "tesla model 3", "toyota camry", "honda civic"]

# The function that checks all constraints on the (partial) assignment.
def valid(houses):
    # houses is a list of 6 dicts or None (for unassigned houses).
    # Houses are indexed 0..5 corresponding to House numbers 1..6.
    # Helper: check constraints for each assigned house.
    for i, house in enumerate(houses):
        if house is None:
            continue
        # Constraint 1: The person who owns a Honda Civic is the person who is short.
        if house.get("CarModel") == "honda civic":
            if house.get("Height") is not None and house.get("Height") != "short":
                return False
        if house.get("Height") == "short":
            if house.get("CarModel") is not None and house.get("CarModel") != "honda civic":
                return False
        # Constraint 2: The person who owns a Ford F-150 is in the fifth house.
        if house.get("CarModel") == "ford f150":
            if i != 4:
                return False
        if i == 4 and house.get("CarModel") is not None:
            if house.get("CarModel") != "ford f150":
                return False
        # Constraint 6: The person who owns a BMW 3 Series is not in the third house.
        if i == 2 and house.get("CarModel") == "bmw 3 series":
            return False
        # Constraint 14: The person who loves the stew is not in the third house.
        if i == 2 and house.get("Food") == "stew":
            return False
        # Constraint 19: The person who is very short is in the fourth house.
        if i == 3:
            if house.get("Height") is not None and house.get("Height") != "very short":
                return False
        # Constraint 17: The person who is tall is Bob.
        if house.get("Name") == "Bob":
            if house.get("Height") is not None and house.get("Height") != "tall":
                return False
        if house.get("Height") == "tall":
            if house.get("Name") is not None and house.get("Name") != "Bob":
                return False
        # Constraint 21: Carol is the person who owns a Tesla Model 3.
        if house.get("Name") == "Carol":
            if house.get("CarModel") is not None and house.get("CarModel") != "tesla model 3":
                return False
        if house.get("CarModel") == "tesla model 3":
            if house.get("Name") is not None and house.get("Name") != "Carol":
                return False
        # Constraint 22: Eric is the person whose birthday is in January.
        if house.get("Name") == "Eric":
            if house.get("Birthday") is not None and house.get("Birthday") != "jan":
                return False
        if house.get("Birthday") == "jan":
            if house.get("Name") is not None and house.get("Name") != "Eric":
                return False
        # Constraint 20: The person whose birthday is in March is the person who is short.
        if house.get("Birthday") == "mar":
            if house.get("Height") is not None and house.get("Height") != "short":
                return False
        if house.get("Height") == "short":
            if house.get("Birthday") is not None and house.get("Birthday") != "mar":
                return False
        # Constraint 12: The person who is very tall is the person who owns a Toyota Camry.
        if house.get("Height") == "very tall":
            if house.get("CarModel") is not None and house.get("CarModel") != "toyota camry":
                return False
        if house.get("CarModel") == "toyota camry":
            if house.get("Height") is not None and house.get("Height") != "very tall":
                return False

    # Constraint 8: The person who loves the soup is directly left of Eric.
    for i in range(1, 6):
        if houses[i] is not None and houses[i].get("Name") == "Eric":
            if houses[i-1] is not None and houses[i-1].get("Food") is not None:
                if houses[i-1].get("Food") != "soup":
                    return False
        if houses[i-1] is not None and houses[i-1].get("Food") == "soup":
            if houses[i] is not None and houses[i].get("Name") is not None:
                if houses[i].get("Name") != "Eric":
                    return False

    # Constraint 10: Alice is directly left of the person who owns a BMW 3 Series.
    for i in range(0, 5):
        if houses[i] is not None and houses[i].get("Name") == "Alice":
            if houses[i+1] is not None and houses[i+1].get("CarModel") is not None:
                if houses[i+1].get("CarModel") != "bmw 3 series":
                    return False
        if houses[i+1] is not None and houses[i+1].get("CarModel") == "bmw 3 series":
            if houses[i] is not None and houses[i].get("Name") is not None:
                if houses[i].get("Name") != "Alice":
                    return False

    # Constraint 13: Peter is directly left of the person who is a pizza lover.
    for i in range(0, 5):
        if houses[i] is not None and houses[i].get("Name") == "Peter":
            if houses[i+1] is not None and houses[i+1].get("Food") is not None:
                if houses[i+1].get("Food") != "pizza":
                    return False
        if houses[i+1] is not None and houses[i+1].get("Food") == "pizza":
            if houses[i] is not None and houses[i].get("Name") is not None:
                if houses[i].get("Name") != "Peter":
                    return False

    # Helper to get index of a unique assignment for a given key/value.
    def get_index(key, value):
        indices = [i for i, h in enumerate(houses) if h is not None and h.get(key) == value]
        if len(indices) == 1:
            return indices[0]
        return None

    # Constraint 3: The person who loves stir fry is somewhere to the left of Eric.
    idx_stir = get_index("Food", "stir fry")
    idx_eric = get_index("Name", "Eric")
    if idx_stir is not None and idx_eric is not None:
        if idx_stir >= idx_eric:
            return False

    # Constraint 4: The person whose birthday is in May is somewhere to the left of Carol.
    idx_may = get_index("Birthday", "may")
    idx_carol = get_index("Name", "Carol")
    if idx_may is not None and idx_carol is not None:
        if idx_may >= idx_carol:
            return False

    # Constraint 5: The person who is very short is somewhere to the left of the person whose birthday is in April.
    idx_vshort = get_index("Height", "very short")
    idx_april = get_index("Birthday", "april")
    if idx_vshort is not None and idx_april is not None:
        if idx_vshort >= idx_april:
            return False

    # Constraint 7: There are two houses between the person who loves stir fry and the person who is a pizza lover.
    idx_stir = get_index("Food", "stir fry")
    idx_pizza = get_index("Food", "pizza")
    if idx_stir is not None and idx_pizza is not None:
        if abs(idx_stir - idx_pizza) != 3:
            return False

    # Constraint 9: The person who loves the spaghetti and the person whose birthday is in May are next to each other.
    idx_spaghetti = get_index("Food", "spaghetti")
    if idx_spaghetti is not None and idx_may is not None:
        if abs(idx_spaghetti - idx_may) != 1:
            return False

    # Constraint 11: The person who owns a Tesla Model 3 is somewhere to the left of the person who is tall.
    idx_tesla = get_index("CarModel", "tesla model 3")
    idx_tall = get_index("Height", "tall")
    if idx_tesla is not None and idx_tall is not None:
        if idx_tesla >= idx_tall:
            return False

    # Constraint 15: There is one house between the person whose birthday is in September and the person who is very short.
    idx_sept = get_index("Birthday", "sept")
    if idx_sept is not None and idx_vshort is not None:
        if abs(idx_sept - idx_vshort) != 2:
            return False

    # Constraint 16: There is one house between the person whose birthday is in March and the person who is super tall.
    idx_mar = get_index("Birthday", "mar")
    idx_supertall = get_index("Height", "super tall")
    if idx_mar is not None and idx_supertall is not None:
        if abs(idx_mar - idx_supertall) != 2:
            return False

    # Constraint 18: The person whose birthday is in May is somewhere to the right of Alice.
    idx_alice = get_index("Name", "Alice")
    if idx_alice is not None and idx_may is not None:
        if idx_alice >= idx_may:
            return False

    return True

# Backtracking search function.
def search_solution(house_index, houses, names, birthdays, foods, heights, cars):
    if house_index == 6:
        if valid(houses):
            # Return a deep copy of the solution.
            yield [dict(h) for h in houses]
        return

    # Iterate over all possible candidate combinations for the current house.
    for cand in itertools.product(names, birthdays, foods, heights, cars):
        cand_name, cand_birthday, cand_food, cand_height, cand_car = cand
        
        # Fixed positions:
        # House 4 (index 3) must be very short.
        if house_index == 3 and cand_height != "very short":
            continue
        # House 5 (index 4) must own Ford F-150.
        if house_index == 4 and cand_car != "ford f150":
            continue

        # Cross-attribute immediate constraints:
        if cand_name == "Eric" and cand_birthday != "jan":
            continue
        if cand_birthday == "jan" and cand_name != "Eric":
            continue
        if cand_height == "short" and cand_birthday != "mar":
            continue
        if cand_birthday == "mar" and cand_height != "short":
            continue
        if cand_name == "Carol" and cand_car != "tesla model 3":
            continue
        if cand_car == "tesla model 3" and cand_name != "Carol":
            continue
        if cand_name == "Bob" and cand_height != "tall":
            continue
        if cand_height == "tall" and cand_name != "Bob":
            continue
        if cand_car == "honda civic" and cand_height != "short":
            continue
        if cand_height == "short" and cand_car != "honda civic":
            continue
        if cand_car == "toyota camry" and cand_height != "very tall":
            continue
        if cand_height == "very tall" and cand_car != "toyota camry":
            continue
        if house_index == 2 and cand_food == "stew":
            continue

        candidate = {
            "House": str(house_index + 1),
            "Name": cand_name,
            "Birthday": cand_birthday,
            "Food": cand_food,
            "Height": cand_height,
            "CarModel": cand_car
        }
        houses[house_index] = candidate

        if not valid(houses):
            houses[house_index] = None
            continue

        # Create new remaining lists (remove the chosen items).
        new_names = names.copy()
        new_names.remove(cand_name)
        new_birthdays = birthdays.copy()
        new_birthdays.remove(cand_birthday)
        new_foods = foods.copy()
        new_foods.remove(cand_food)
        new_heights = heights.copy()
        new_heights.remove(cand_height)
        new_cars = cars.copy()
        new_cars.remove(cand_car)

        yield from search_solution(house_index + 1, houses, new_names, new_birthdays, new_foods, new_heights, new_cars)
        houses[house_index] = None

def main():
    # Initialize the houses list.
    houses = [None] * 6
    sols = list(search_solution(0, houses, NAMES, BIRTHDAYS, FOODS, HEIGHTS, CARS))
    if not sols:
        sys.exit("No solution found.")
    # Use the first solution found.
    solution = sols[0]
    # Prepare output in the required JSON format.
    output = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Food", "Height", "CarModel"],
            "rows": [
                [house["House"], house["Name"], house["Birthday"], house["Food"], house["Height"], house["CarModel"]]
                for house in solution
            ]
        }
    }
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()