#!/usr/bin/env python3
import json

def global_check(houses):
    # houses is a list of 6 complete house assignments (dicts).
    # Constraint: There is one house between the house whose mother is Sarah and the house with a Toyota Camry.
    idx_sarah = next((i for i, h in enumerate(houses) if h["Mother"] == "Sarah"), None)
    idx_toyota = next((i for i, h in enumerate(houses) if h["CarModel"] == "toyota camry"), None)
    if idx_sarah is None or idx_toyota is None or abs(idx_sarah - idx_toyota) != 2:
        return False

    # Constraint: There is one house between the house whose mother is Sarah and the house that loves cooking.
    idx_cooking = next((i for i, h in enumerate(houses) if h["Hobby"] == "cooking"), None)
    if idx_cooking is None or abs(idx_sarah - idx_cooking) != 2:
        return False

    # Constraint: The person whose mother's name Penny is somewhere to the right of the person who enjoys knitting.
    idx_knitting = next((i for i, h in enumerate(houses) if h["Hobby"] == "knitting"), None)
    idx_penny = next((i for i, h in enumerate(houses) if h["Mother"] == "Penny"), None)
    if idx_knitting is not None and idx_penny is not None:
        if idx_penny <= idx_knitting:
            return False

    # Constraint: The person whose mother's name Aniya is somewhere to the right of the person who owns a Honda Civic.
    idx_civic = next((i for i, h in enumerate(houses) if h["CarModel"] == "honda civic"), None)
    idx_aniya = next((i for i, h in enumerate(houses) if h["Mother"] == "Aniya"), None)
    if idx_civic is None or idx_aniya is None or idx_aniya <= idx_civic:
        return False

    # Constraint: Alice is somewhere to the right of the person who owns a Ford F-150.
    idx_ford = next((i for i, h in enumerate(houses) if h["CarModel"] == "ford f150"), None)
    idx_alice = next((i for i, h in enumerate(houses) if h["Name"] == "Alice"), None)
    if idx_ford is None or idx_alice is None or idx_alice <= idx_ford:
        return False

    # Constraint: The woodworking hobbyist is somewhere to the left of the person who enjoys knitting.
    idx_wood = next((i for i, h in enumerate(houses) if h["Hobby"] == "woodworking"), None)
    if idx_knitting is not None and idx_wood is not None:
        if idx_wood >= idx_knitting:
            return False

    # Constraint: Eric (who is gardening) is directly left of the person who enjoys knitting 
    # and the house immediately to the left of a knitting house must have mother Holly.
    valid_adjacent = False
    for i in range(len(houses) - 1):
        if (houses[i]["Name"] == "Eric" and houses[i]["Mother"] == "Holly" and
            houses[i]["Hobby"] == "gardening" and houses[i+1]["Hobby"] == "knitting"):
            valid_adjacent = True
            break
    if not valid_adjacent:
        return False

    return True

def local_check(houses, index):
    current = houses[index]
    # Fixed-position constraints:
    # In the fourth house (index 3), the car must be Ford F-150 and the mother must be Sarah.
    if index == 3:
        if current["CarModel"] != "ford f150" or current["Mother"] != "Sarah":
            return False
    # In the sixth house (index 5), the car must be Toyota Camry and the mother must be Kailyn.
    if index == 5:
        if current["CarModel"] != "toyota camry" or current["Mother"] != "Kailyn":
            return False

    # "Alice" must be in a house numbered higher than house 4 (i.e. index > 3).
    if current["Name"] == "Alice" and index <= 3:
        return False

    # Local attribute implications:
    # Eric is the gardening enthusiast.
    if current["Name"] == "Eric" and current["Hobby"] != "gardening":
        return False
    # Carol is the photography enthusiast.
    if current["Name"] == "Carol" and current["Hobby"] != "photography":
        return False
    # The Honda Civic is owned by Arnold.
    if current["CarModel"] == "honda civic" and current["Name"] != "Arnold":
        return False
    # The BMW 3 Series is owned by Bob.
    if current["CarModel"] == "bmw 3 series" and current["Name"] != "Bob":
        return False
    # The Chevrolet Silverado is paired with mother Aniya.
    if current["CarModel"] == "chevrolet silverado" and current["Mother"] != "Aniya":
        return False
    if current["Mother"] == "Aniya" and current["CarModel"] != "chevrolet silverado":
        return False
    # The person who loves cooking must be either in the second house or the sixth house.
    if current["Hobby"] == "cooking" and index not in [1, 5]:
        return False

    # Adjacent constraints:
    # If a house’s hobby is knitting then the house immediately to its left must be occupied
    # by Eric (who is gardening) and whose mother is Holly.
    if index > 0:
        prev = houses[index - 1]
        if current["Hobby"] == "knitting":
            if not (prev["Name"] == "Eric" and prev["Mother"] == "Holly" and prev["Hobby"] == "gardening"):
                return False
        # Conversely, if the previous house is occupied by Eric (or has mother Holly), then
        # the current house must have knitting as its hobby.
        if prev["Name"] == "Eric" or prev["Mother"] == "Holly":
            if current["Hobby"] != "knitting":
                return False

    # For every house that has knitting assigned, there must be at least one earlier house with woodworking.
    for j in range(len(houses)):
        if houses[j]["Hobby"] == "knitting":
            if j == 0:
                return False
            if not any(houses[k]["Hobby"] == "woodworking" for k in range(j)):
                return False

    return True

def search(idx, houses, rem_names, rem_cars, rem_mothers, rem_hobbies):
    if idx == 6:
        # All 6 houses are assigned; now check the global (relative ordering) constraints.
        if global_check(houses):
            return houses
        return None

    for name in list(rem_names):
        for car in list(rem_cars):
            for mother in list(rem_mothers):
                for hobby in list(rem_hobbies):
                    # Enforce fixed-position choices:
                    if idx == 3 and (car != "ford f150" or mother != "Sarah"):
                        continue
                    if idx == 5 and (car != "toyota camry" or mother != "Kailyn"):
                        continue
                    # Enforce the cooking hobby’s allowed positions.
                    if hobby == "cooking" and idx not in [1, 5]:
                        continue

                    candidate = {
                        "House": str(idx + 1),
                        "Name": name,
                        "CarModel": car,
                        "Mother": mother,
                        "Hobby": hobby
                    }
                    houses.append(candidate)
                    new_rem_names = rem_names.copy()
                    new_rem_names.remove(name)
                    new_rem_cars = rem_cars.copy()
                    new_rem_cars.remove(car)
                    new_rem_mothers = rem_mothers.copy()
                    new_rem_mothers.remove(mother)
                    new_rem_hobbies = rem_hobbies.copy()
                    new_rem_hobbies.remove(hobby)

                    if not local_check(houses, idx):
                        houses.pop()
                        continue

                    result = search(idx + 1, houses, new_rem_names, new_rem_cars, new_rem_mothers, new_rem_hobbies)
                    if result is not None:
                        return result
                    houses.pop()
    return None

def main():
    names = {"Eric", "Bob", "Peter", "Alice", "Arnold", "Carol"}
    cars = {"ford f150", "honda civic", "toyota camry", "tesla model 3", "chevrolet silverado", "bmw 3 series"}
    mothers = {"Sarah", "Penny", "Holly", "Aniya", "Kailyn", "Janelle"}
    hobbies = {"photography", "cooking", "knitting", "gardening", "woodworking", "painting"}

    solution = search(0, [], names, cars, mothers, hobbies)
    if solution is None:
        output = {"solution": {"header": ["House", "Name", "CarModel", "Mother", "Hobby"], "rows": []}}
    else:
        rows = []
        for house in solution:
            row = [house["House"], house["Name"], house["CarModel"], house["Mother"], house["Hobby"]]
            rows.append(row)
        output = {"solution": {"header": ["House", "Name", "CarModel", "Mother", "Hobby"], "rows": rows}}
    print(json.dumps(output))

if __name__ == "__main__":
    main()