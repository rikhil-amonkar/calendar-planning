#!/usr/bin/env python3
import json
import sys

# Define the lists of possible attributes
NAMES = ["Eric", "Peter", "Arnold", "Alice", "Bob"]
FOODS = ["stir fry", "spaghetti", "stew", "grilled cheese", "pizza"]
CAR_MODELS = ["ford f150", "tesla model 3", "bmw 3 series", "toyota camry", "honda civic"]
PHONE_MODELS = ["iphone 13", "google pixel 6", "samsung galaxy s21", "oneplus 9", "huawei p50"]
OCCUPATIONS = ["teacher", "lawyer", "doctor", "artist", "engineer"]
DRINKS = ["tea", "milk", "water", "root beer", "coffee"]

# This function checks if the current (partial or complete) assignment satisfies all constraints.
def constraints_ok(houses):
    # houses: list of length 5, each either a dict with keys "Name", "Food", "CarModel", "PhoneModel", "Occupation", "Drink" or None.
    n = len(houses)
    # Check constraints that can be verified for each assigned house and with its neighbor when applicable.
    for i in range(n):
        h = houses[i]
        if h is None:
            continue
        
        # Constraint 17: Eric is in the fourth house (index 3)
        if i == 3 and h["Name"] != "Eric":
            return False

        # Constraint 1: The root beer lover is the person who owns a Honda Civic.
        if h["Drink"] == "root beer" and h["CarModel"] != "honda civic":
            return False
        if h["CarModel"] == "honda civic" and h["Drink"] != "root beer":
            return False

        # Constraint 3 & 4 & 14: Alice must use Samsung Galaxy S21, love stir fry, and be an artist.
        if h["Name"] == "Alice":
            if h["PhoneModel"] != "samsung galaxy s21":
                return False
            if h["Food"] != "stir fry":
                return False
            if h["Occupation"] != "artist":
                return False

        # Constraint 19: The person who loves eating grilled cheese is Peter.
        if h["Food"] == "grilled cheese" and h["Name"] != "Peter":
            return False
        if h["Name"] == "Peter" and h["Food"] != "grilled cheese":
            return False

        # Constraint 7 & 16: The doctor is Arnold & Arnold owns a Toyota Camry.
        if h["Name"] == "Arnold":
            if h["Occupation"] != "doctor":
                return False
            if h["CarModel"] != "toyota camry":
                return False
        if h["Occupation"] == "doctor" and h["Name"] != "Arnold":
            return False

        # Constraint 5: The tea drinker is not in the fifth house.
        if i == 4 and h["Drink"] == "tea":
            return False

        # Constraint 8 and 10: The person who uses an iPhone 13 is the coffee drinker and loves stew.
        if h["PhoneModel"] == "iphone 13":
            if h["Drink"] != "coffee":
                return False
            if h["Food"] != "stew":
                return False
        if h["Drink"] == "coffee" and h["PhoneModel"] != "iphone 13":
            return False
        if h["Food"] == "stew" and h["PhoneModel"] != "iphone 13":
            return False

        # Constraint 9: The engineer is the person who owns a BMW 3 Series.
        if h["Occupation"] == "engineer" and h["CarModel"] != "bmw 3 series":
            return False
        if h["CarModel"] == "bmw 3 series" and h["Occupation"] != "engineer":
            return False

        # Constraint 11: The doctor is directly left of the person who uses a OnePlus 9.
        if i < n - 1 and houses[i+1] is not None:
            if h["Occupation"] == "doctor" and houses[i+1]["PhoneModel"] != "oneplus 9":
                return False
            if houses[i+1]["PhoneModel"] == "oneplus 9" and h["Occupation"] != "doctor":
                return False

        # Constraint 12: The person who owns a Honda Civic is directly left of the person who loves spaghetti.
        if i < n - 1 and houses[i+1] is not None:
            if h["CarModel"] == "honda civic" and houses[i+1]["Food"] != "spaghetti":
                return False
            if houses[i+1]["Food"] == "spaghetti" and h["CarModel"] != "honda civic":
                return False

        # Constraint 13: The person who uses a Google Pixel 6 is the tea drinker.
        if h["PhoneModel"] == "google pixel 6" and h["Drink"] != "tea":
            return False
        if h["Drink"] == "tea" and h["PhoneModel"] != "google pixel 6":
            return False

        # Constraint 18: The person who uses a OnePlus 9 is the lawyer.
        if h["PhoneModel"] == "oneplus 9" and h["Occupation"] != "lawyer":
            return False
        if h["Occupation"] == "lawyer" and h["PhoneModel"] != "oneplus 9":
            return False

        # Constraint 2: The person who likes milk is directly left of the person who loves grilled cheese.
        if i < n - 1 and houses[i+1] is not None:
            if h["Drink"] == "milk" and houses[i+1]["Food"] != "grilled cheese":
                return False
            if houses[i+1]["Food"] == "grilled cheese" and h["Drink"] != "milk":
                return False

    # Global cross-house constraints that involve non-adjacent houses:
    bmw_index = None
    tea_index = None
    alice_index = None
    ford_index = None
    for idx, h in enumerate(houses):
        if h is None:
            continue
        if h["CarModel"] == "bmw 3 series":
            bmw_index = idx
        if h["Drink"] == "tea":
            tea_index = idx
        if h["Name"] == "Alice":
            alice_index = idx
        if h["CarModel"] == "ford f150":
            ford_index = idx

    # Constraint 6: The person who owns a BMW 3 Series is somewhere to the left of the tea drinker.
    if bmw_index is not None and tea_index is not None:
        if bmw_index >= tea_index:
            return False

    # Constraint 15: There is one house between Alice and the person who owns a Ford F-150.
    if alice_index is not None and ford_index is not None:
        if abs(alice_index - ford_index) != 2:
            return False

    return True

# Backtracking search: assign each house (index 0 to 4) a complete set of attributes.
def backtrack(i, houses, used):
    if i == 5:
        if constraints_ok(houses):
            # Return a deep copy of houses
            return [dict(h) for h in houses]
        return None

    # For house i, determine available options by category.
    # For each attribute, available options are those not used yet.
    available_names = [name for name in NAMES if name not in used["Name"]]
    available_foods = [food for food in FOODS if food not in used["Food"]]
    available_cars = [car for car in CAR_MODELS if car not in used["CarModel"]]
    available_phones = [phone for phone in PHONE_MODELS if phone not in used["PhoneModel"]]
    available_occupations = [occ for occ in OCCUPATIONS if occ not in used["Occupation"]]
    available_drinks = [drink for drink in DRINKS if drink not in used["Drink"]]

    # House index 3 (fourth house) must be Eric (Constraint 17)
    if i == 3:
        name_options = ["Eric"] if "Eric" in available_names else []
    else:
        name_options = available_names

    for name in name_options:
        # Prepare forced attribute values based on the name.
        # For Alice:
        if name == "Alice":
            food_opts = ["stir fry"] if "stir fry" in available_foods else []
            phone_opts = ["samsung galaxy s21"] if "samsung galaxy s21" in available_phones else []
            occ_opts = ["artist"] if "artist" in available_occupations else []
        # For Peter:
        elif name == "Peter":
            food_opts = ["grilled cheese"] if "grilled cheese" in available_foods else []
            phone_opts = available_phones[:]  # no forced phone for Peter
            occ_opts = available_occupations[:]
        # For Arnold:
        elif name == "Arnold":
            food_opts = available_foods[:]
            phone_opts = available_phones[:]
            occ_opts = ["doctor"] if "doctor" in available_occupations else []
        else:
            food_opts = available_foods[:]
            phone_opts = available_phones[:]
            occ_opts = available_occupations[:]

        for food in food_opts:
            for car in (["toyota camry"] if name == "Arnold" and "toyota camry" in available_cars 
                        else available_cars):
                for phone in phone_opts:
                    for occ in occ_opts:
                        for drink in available_drinks:
                            house_assignment = {
                                "Name": name,
                                "Food": food,
                                "CarModel": car,
                                "PhoneModel": phone,
                                "Occupation": occ,
                                "Drink": drink
                            }
                            houses[i] = house_assignment

                            # Update used sets
                            used["Name"].add(name)
                            used["Food"].add(food)
                            used["CarModel"].add(car)
                            used["PhoneModel"].add(phone)
                            used["Occupation"].add(occ)
                            used["Drink"].add(drink)

                            # Check partial constraints for houses assigned so far.
                            if constraints_ok(houses):
                                result = backtrack(i + 1, houses, used)
                                if result is not None:
                                    return result
                            
                            # Backtrack: remove the current assignment from used sets.
                            used["Name"].remove(name)
                            used["Food"].remove(food)
                            used["CarModel"].remove(car)
                            used["PhoneModel"].remove(phone)
                            used["Occupation"].remove(occ)
                            used["Drink"].remove(drink)
                            houses[i] = None
    return None

def main():
    # Initialize houses and used sets per category.
    houses = [None] * 5
    used = {
        "Name": set(),
        "Food": set(),
        "CarModel": set(),
        "PhoneModel": set(),
        "Occupation": set(),
        "Drink": set()
    }

    solution = backtrack(0, houses, used)
    if solution is None:
        sys.exit("No solution found.")

    # Prepare the JSON output in the required format.
    header = ["House", "Name", "Food", "CarModel", "PhoneModel", "Occupation", "Drink"]
    rows = []
    for idx, house in enumerate(solution):
        # House number as string (1-indexed)
        row = [
            str(idx + 1),
            house["Name"],
            house["Food"],
            house["CarModel"],
            house["PhoneModel"],
            house["Occupation"],
            house["Drink"]
        ]
        rows.append(row)

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()