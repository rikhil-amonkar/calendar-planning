#!/usr/bin/env python3
import json

# Define the domains for each attribute
NAMES = ["Arnold", "Carol", "Eric", "Bob", "Alice", "Peter"]
BIRTHDAYS = ["feb", "mar", "sept", "jan", "may", "april"]
LUNCHES = ["stew", "soup", "grilled cheese", "stir fry", "spaghetti", "pizza"]
HEIGHTS = ["very short", "average", "super tall", "short", "very tall", "tall"]
CAR_MODELS = ["chevrolet silverado", "ford f150", "bmw 3 series", "tesla model 3", "toyota camry", "honda civic"]

# This function checks if the current partial (or full) assignment does not violate any constraints.
def check_constraints(assignment):
    n = len(assignment)
    # Build dictionaries mapping attribute value to house index for assigned houses.
    name_positions = {}
    birthday_positions = {}
    lunch_positions = {}
    height_positions = {}
    car_positions = {}
    for i, house in enumerate(assignment):
        name_positions[house["Name"]] = i
        birthday_positions[house["Birthday"]] = i
        lunch_positions[house["Lunch"]] = i
        height_positions[house["Height"]] = i
        car_positions[house["Car Model"]] = i

    # Constraint 1: The person who owns a Honda Civic is the person who is short.
    for house in assignment:
        if house["Car Model"] == "honda civic" and house["Height"] != "short":
            return False
        if house["Height"] == "short" and house["Car Model"] != "honda civic":
            return False

    # Constraint 20: The person whose birthday is in March is the person who is short.
    for house in assignment:
        if house["Birthday"] == "mar" and house["Height"] != "short":
            return False
        if house["Height"] == "short" and house["Birthday"] != "mar":
            return False

    # Constraint 2: The Ford F-150 is in the fifth house (house index 4) and no other house.
    for i, house in enumerate(assignment):
        if i == 4:
            if house["Car Model"] != "ford f150":
                return False
        else:
            if house["Car Model"] == "ford f150":
                return False

    # Constraint 3: The person who loves stir fry is somewhere to the left of Eric.
    i_sf = lunch_positions.get("stir fry")
    i_eric = name_positions.get("Eric")
    if i_sf is not None:
        if i_sf == 5:
            return False
        if i_eric is not None and not (i_sf < i_eric):
            return False

    # Constraint 4: The person whose birthday is in May is somewhere to the left of Carol.
    i_may = birthday_positions.get("may")
    i_carol = name_positions.get("Carol")
    if i_may is not None:
        if i_may == 5:  # cannot be last house because Carol must follow
            return False
    if i_may is not None and i_carol is not None:
        if not (i_may < i_carol):
            return False

    # Constraint 5: The person who is very short is somewhere to the left of the person whose birthday is in April.
    # We know from constraint 19 (below) that very short must be in house 4 (index 3).
    if "april" in birthday_positions:
        if birthday_positions["april"] <= 3:
            return False
    # Also if house index 3 is assigned, it must be "very short".
    if n > 3:
        if assignment[3]["Height"] != "very short":
            return False

    # Constraint 6: The BMW 3 Series is not in the third house (house index 2).
    if n > 2:
        if assignment[2]["Car Model"] == "bmw 3 series":
            return False

    # Constraint 7: There are two houses between the stir fry lover and the pizza lover.
    i_sf = lunch_positions.get("stir fry")
    i_pizza = lunch_positions.get("pizza")
    if i_sf is not None and i_pizza is not None:
        if abs(i_sf - i_pizza) != 3:
            return False
    # Partial check if only one is assigned.
    if i_sf is not None and i_pizza is None:
        possibles = []
        for pos in [i_sf - 3, i_sf + 3]:
            if 0 <= pos < 6:
                # If pos already assigned, it must eventually be pizza.
                if pos < n:
                    if assignment[pos]["Lunch"] == "pizza":
                        possibles.append(pos)
                else:
                    possibles.append(pos)
        if not possibles:
            return False
    if i_pizza is not None and i_sf is None:
        possibles = []
        for pos in [i_pizza - 3, i_pizza + 3]:
            if 0 <= pos < 6:
                if pos < n:
                    if assignment[pos]["Lunch"] == "stir fry":
                        possibles.append(pos)
                else:
                    possibles.append(pos)
        if not possibles:
            return False

    # Constraint 8: The person who loves the soup is directly left of Eric.
    i_soup = lunch_positions.get("soup")
    i_eric = name_positions.get("Eric")
    if i_soup is not None:
        if i_soup == 5:
            return False
        if i_soup < n - 1:
            if assignment[i_soup + 1]["Name"] != "Eric":
                return False
    if i_eric is not None:
        if i_eric == 0:
            return False
        # If the house immediately to the left of Eric is assigned, must be soup.
        if (i_eric - 1) < n:
            if assignment[i_eric - 1]["Lunch"] != "soup":
                return False

    # Constraint 9: The person who loves spaghetti and the person whose birthday is in May are next to each other.
    i_spaghetti = lunch_positions.get("spaghetti")
    i_may_bday = birthday_positions.get("may")
    if i_spaghetti is not None and i_may_bday is not None:
        if abs(i_spaghetti - i_may_bday) != 1:
            return False
    if i_spaghetti is not None and i_may_bday is None:
        possible = False
        for pos in [i_spaghetti - 1, i_spaghetti + 1]:
            if 0 <= pos < 6:
                if pos >= n:  # not assigned yet, so possibility remains
                    possible = True
                else:
                    if assignment[pos]["Birthday"] == "may":
                        possible = True
        # If spaghetti is at an edge and the only neighbor is assigned and not "may", then fail.
        if (i_spaghetti in [0, 5]) and not possible:
            return False
    if i_may_bday is not None and i_spaghetti is None:
        possible = False
        for pos in [i_may_bday - 1, i_may_bday + 1]:
            if 0 <= pos < 6:
                if pos >= n:
                    possible = True
                else:
                    if assignment[pos]["Lunch"] == "spaghetti":
                        possible = True
        if (i_may_bday in [0, 5]) and not possible:
            return False

    # Constraint 10: Alice is directly left of the person who owns a BMW 3 Series.
    for i, house in enumerate(assignment):
        if house["Name"] == "Alice":
            if i == 5:
                return False
            if i < n - 1:
                if assignment[i+1]["Car Model"] != "bmw 3 series":
                    return False
    for i, house in enumerate(assignment):
        if house["Car Model"] == "bmw 3 series":
            if i == 0:
                return False
            if i > 0:
                if assignment[i-1]["Name"] != "Alice":
                    return False

    # Constraint 11: The person who owns a Tesla Model 3 is somewhere to the left of the person who is tall.
    i_tesla = car_positions.get("tesla model 3")
    i_tall = None
    for i, house in enumerate(assignment):
        if house["Height"] == "tall":
            i_tall = i
            break
    if i_tesla is not None:
        if i_tesla == 5:
            return False
        if i_tall is not None and not (i_tesla < i_tall):
            return False
    if i_tall is not None:
        if i_tall == 0:
            return False

    # Constraint 12: The person who is very tall is the person who owns a Toyota Camry.
    for house in assignment:
        if house["Height"] == "very tall" and house["Car Model"] != "toyota camry":
            return False
        if house["Car Model"] == "toyota camry" and house["Height"] != "very tall":
            return False

    # Constraint 13: Peter is directly left of the person who is a pizza lover.
    for i, house in enumerate(assignment):
        if house["Name"] == "Peter":
            if i == 5:
                return False
            if i < n - 1:
                if assignment[i+1]["Lunch"] != "pizza":
                    return False
    for i, house in enumerate(assignment):
        if house["Lunch"] == "pizza":
            if i == 0:
                return False
            if i > 0:
                if assignment[i-1]["Name"] != "Peter":
                    return False

    # Constraint 14: The person who loves the stew is not in the third house (house index 2).
    if n > 2:
        if assignment[2]["Lunch"] == "stew":
            return False

    # Constraint 15: There is one house between the person whose birthday is in September and the person who is very short.
    # "Very short" is fixed to house index 3; therefore sept must be in house index 1 or 5.
    if "sept" in birthday_positions:
        if abs(birthday_positions["sept"] - 3) != 2:
            return False

    # Constraint 16: There is one house between the person whose birthday is in March and the person who is super tall.
    i_mar = birthday_positions.get("mar")
    i_super_tall = None
    for i, house in enumerate(assignment):
        if house["Height"] == "super tall":
            i_super_tall = i
            break
    if i_mar is not None and i_super_tall is not None:
        if abs(i_mar - i_super_tall) != 2:
            return False
    if i_mar is not None and i_super_tall is None:
        possible = False
        for pos in [i_mar - 2, i_mar + 2]:
            if 0 <= pos < 6:
                if pos >= n:
                    possible = True
                else:
                    if assignment[pos]["Height"] == "super tall":
                        possible = True
        if not possible:
            return False
    if i_super_tall is not None and i_mar is None:
        possible = False
        for pos in [i_super_tall - 2, i_super_tall + 2]:
            if 0 <= pos < 6:
                if pos >= n:
                    possible = True
                else:
                    if assignment[pos]["Birthday"] == "mar":
                        possible = True
        if not possible:
            return False

    # Constraint 17: The person who is tall is Bob.
    for house in assignment:
        if house["Name"] == "Bob" and house["Height"] != "tall":
            return False
        if house["Height"] == "tall" and house["Name"] != "Bob":
            return False

    # Constraint 18: The person whose birthday is in May is somewhere to the right of Alice.
    i_alice = name_positions.get("Alice")
    i_may_b = birthday_positions.get("may")
    if i_alice is not None:
        if i_alice == 5:
            return False
        if i_may_b is not None and not (i_may_b > i_alice):
            return False
    if i_may_b is not None:
        if i_may_b == 0:
            return False

    # Constraint 21: Carol is the person who owns a Tesla Model 3.
    for house in assignment:
        if house["Name"] == "Carol" and house["Car Model"] != "tesla model 3":
            return False
        if house["Car Model"] == "tesla model 3" and house["Name"] != "Carol":
            return False

    # Constraint 22: Eric is the person whose birthday is in January.
    for house in assignment:
        if house["Name"] == "Eric" and house["Birthday"] != "jan":
            return False
        if house["Birthday"] == "jan" and house["Name"] != "Eric":
            return False

    return True

# Backtracking function to try all assignments house by house.
def backtrack(index, assignment, used_names, used_birthdays, used_lunches, used_heights, used_cars):
    if index == 6:
        # Full assignment reached; if it satisfies constraints return it.
        if check_constraints(assignment):
            return assignment
        else:
            return None
    for name in [n for n in NAMES if n not in used_names]:
        for birthday in [b for b in BIRTHDAYS if b not in used_birthdays]:
            # Enforce Constraint 22: Eric <-> jan.
            if birthday == "jan" and name != "Eric":
                continue
            if name == "Eric" and birthday != "jan":
                continue
            for lunch in [l for l in LUNCHES if l not in used_lunches]:
                for height in [h for h in HEIGHTS if h not in used_heights]:
                    # Enforce fixed constraint: House 4 (index 3) must be very short.
                    if index == 3 and height != "very short":
                        continue
                    # Enforce constraint 11: tall cannot be in the first house.
                    if index == 0 and height == "tall":
                        continue
                    for car in [c for c in CAR_MODELS if c not in used_cars]:
                        # Fixed: House 5 (index 4) must be Ford F-150.
                        if index == 4 and car != "ford f150":
                            continue
                        # Constraint 6: House 3 (index 2) cannot have BMW 3 Series.
                        if index == 2 and car == "bmw 3 series":
                            continue
                        # Constraint 10: Alice cannot be in the last house.
                        if name == "Alice" and index == 5:
                            continue
                        # Constraint 13: Peter cannot be in the last house.
                        if name == "Peter" and index == 5:
                            continue
                        # Constraint 3: stir fry cannot be in the last house.
                        if lunch == "stir fry" and index == 5:
                            continue
                        # Constraint 4: birthday may cannot be in the last house.
                        if birthday == "may" and index == 5:
                            continue
                        # Create the candidate house assignment.
                        house = {
                            "House": str(index + 1),
                            "Name": name,
                            "Birthday": birthday,
                            "Lunch": lunch,
                            "Height": height,
                            "Car Model": car
                        }
                        assignment.append(house)
                        new_used_names = used_names | {name}
                        new_used_birthdays = used_birthdays | {birthday}
                        new_used_lunches = used_lunches | {lunch}
                        new_used_heights = used_heights | {height}
                        new_used_cars = used_cars | {car}
                        if check_constraints(assignment):
                            result = backtrack(index + 1, assignment, new_used_names, new_used_birthdays, new_used_lunches, new_used_heights, new_used_cars)
                            if result is not None:
                                return result
                        assignment.pop()
    return None

def main():
    solution = backtrack(0, [], set(), set(), set(), set(), set())
    if solution is None:
        output = {"solution": {"header": ["House", "Name", "Birthday", "Lunch", "Height", "Car Model"], "rows": []}}
    else:
        # Order the solution by house number (houses are added in order)
        rows = []
        for house in solution:
            rows.append([house["House"], house["Name"], house["Birthday"], house["Lunch"], house["Height"], house["Car Model"]])
        output = {"solution": {"header": ["House", "Name", "Birthday", "Lunch", "Height", "Car Model"], "rows": rows}}
    print(json.dumps(output, indent=2))

if __name__ == '__main__':
    main()