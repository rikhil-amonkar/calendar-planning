#!/usr/bin/env python3
import itertools
import json

def check_constraints(houses):
    # houses is a list of dicts, where index 0 is House "1", index 1 is House "2", etc.
    
    # Constraint 1:
    # The person living in a colonial-style house is somewhere to the left of the person who likes milk.
    colonial_index = None
    milk_index = None
    for i, house in enumerate(houses):
        if house["HouseStyle"] == "colonial":
            colonial_index = i
        if house["Drink"] == "milk":
            milk_index = i
    if colonial_index is None or milk_index is None or colonial_index >= milk_index:
        return False

    # Constraint 2:
    # The person who prefers city breaks is directly left of the person residing in a Victorian house.
    city_index = None
    for i, house in enumerate(houses):
        if house["Vacation"] == "city":
            city_index = i
            break
    if city_index is None or city_index == len(houses) - 1:
        return False
    if houses[city_index + 1]["HouseStyle"] != "victorian":
        return False

    # Constraint 3:
    # The person whose birthday is in January is directly left of the cat lover.
    jan_index = None
    for i, house in enumerate(houses):
        if house["Birthday"] == "jan":
            jan_index = i
            break
    if jan_index is None or jan_index == len(houses) - 1:
        return False
    if houses[jan_index + 1]["Animal"] != "cat":
        return False

    # Constraint 4:
    # The one who only drinks water is the person who enjoys mountain retreats.
    for house in houses:
        if house["Drink"] == "water" and house["Vacation"] != "mountain":
            return False
        if house["Vacation"] == "mountain" and house["Drink"] != "water":
            return False

    # Constraint 5:
    # The person who keeps horses is Peter.
    for house in houses:
        if house["Animal"] == "horse" and house["Name"] != "Peter":
            return False
        if house["Name"] == "Peter" and house["Animal"] != "horse":
            return False

    # Constraint 6:
    # The person residing in a Victorian house is somewhere to the right of the person who loves beach vacations.
    victorian_index = None
    beach_index = None
    for i, house in enumerate(houses):
        if house["HouseStyle"] == "victorian":
            victorian_index = i
        if house["Vacation"] == "beach":
            beach_index = i
    if victorian_index is None or beach_index is None or beach_index >= victorian_index:
        return False

    # Constraint 7:
    # Peter is the person who prefers city breaks.
    for house in houses:
        if house["Name"] == "Peter" and house["Vacation"] != "city":
            return False
        if house["Vacation"] == "city" and house["Name"] != "Peter":
            return False

    # Constraint 8:
    # The person who enjoys mountain retreats is the person whose birthday is in April.
    for house in houses:
        if house["Vacation"] == "mountain" and house["Birthday"] != "april":
            return False
        if house["Birthday"] == "april" and house["Vacation"] != "mountain":
            return False

    # Constraint 9:
    # Eric is the one who only drinks water.
    for house in houses:
        if house["Name"] == "Eric" and house["Drink"] != "water":
            return False

    return True

def solve_puzzle():
    houses_num = 3
    names = ["Eric", "Peter", "Arnold"]
    drinks = ["milk", "water", "tea"]
    vacations = ["mountain", "city", "beach"]
    house_styles = ["colonial", "victorian", "ranch"]
    animals = ["cat", "bird", "horse"]
    birthdays = ["jan", "sept", "april"]

    # Using brute-force search over permutations
    for names_perm in itertools.permutations(names):
        for drinks_perm in itertools.permutations(drinks):
            for vac_perm in itertools.permutations(vacations):
                for style_perm in itertools.permutations(house_styles):
                    for animal_perm in itertools.permutations(animals):
                        for bday_perm in itertools.permutations(birthdays):
                            houses = []
                            for i in range(houses_num):
                                house = {
                                    "House": str(i+1),
                                    "Name": names_perm[i],
                                    "Drink": drinks_perm[i],
                                    "Vacation": vac_perm[i],
                                    "HouseStyle": style_perm[i],
                                    "Animal": animal_perm[i],
                                    "Birthday": bday_perm[i]
                                }
                                houses.append(house)
                            if check_constraints(houses):
                                return houses
    return None

def main():
    solution = solve_puzzle()
    if solution is None:
        output = {"solution": {"header": ["House", "Name", "Drink", "Vacation", "HouseStyle", "Animal", "Birthday"], "rows": []}}
    else:
        # Sort by house number (they are in order by our generation, but we enforce it)
        solution_sorted = sorted(solution, key=lambda x: int(x["House"]))
        rows = []
        header = ["House", "Name", "Drink", "Vacation", "HouseStyle", "Animal", "Birthday"]
        for house in solution_sorted:
            row = [house[field] for field in header]
            rows.append(row)
        output = {"solution": {"header": header, "rows": rows}}
    print(json.dumps(output))

if __name__ == '__main__':
    main()