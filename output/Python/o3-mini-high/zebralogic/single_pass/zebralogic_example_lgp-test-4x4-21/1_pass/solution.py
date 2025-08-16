#!/usr/bin/env python3
import itertools
import json

def main():
    houses_count = 4
    names = ["Eric", "Peter", "Alice", "Arnold"]
    car_models = ["tesla model 3", "honda civic", "toyota camry", "ford f150"]
    birthdays = ["jan", "april", "sept", "feb"]
    hobbies = ["painting", "cooking", "gardening", "photography"]

    # Iterate over all possible assignments (permutations) for each attribute.
    for name_perm in itertools.permutations(names):
        for car_perm in itertools.permutations(car_models):
            for bday_perm in itertools.permutations(birthdays):
                for hobby_perm in itertools.permutations(hobbies):
                    # Constraint 1: The person whose birthday is in January is not in the second house.
                    if bday_perm[1] == "jan":
                        continue

                    # Constraint 2: The photography enthusiast is somewhere to the left of Eric.
                    try:
                        pos_photography = hobby_perm.index("photography")
                        pos_Eric = name_perm.index("Eric")
                    except ValueError:
                        continue
                    if not (pos_photography < pos_Eric):
                        continue

                    # Constraint 3: The photography enthusiast is somewhere to the left of Peter.
                    try:
                        pos_Peter = name_perm.index("Peter")
                    except ValueError:
                        continue
                    if not (pos_photography < pos_Peter):
                        continue

                    # Constraint 4: The person who owns a Honda Civic is directly left of the person who owns a Tesla Model 3.
                    valid_adjacent = False
                    for i in range(houses_count - 1):
                        if car_perm[i] == "honda civic" and car_perm[i+1] == "tesla model 3":
                            valid_adjacent = True
                            break
                    if not valid_adjacent:
                        continue

                    # Constraint 5: There is one house between the person who owns a Tesla Model 3 and the person who enjoys gardening.
                    try:
                        pos_tesla = car_perm.index("tesla model 3")
                        pos_gardening = hobby_perm.index("gardening")
                    except ValueError:
                        continue
                    if abs(pos_tesla - pos_gardening) != 2:
                        continue

                    # Constraint 6: The person who owns a Tesla Model 3 is Arnold.
                    if name_perm[pos_tesla] != "Arnold":
                        continue

                    # Constraint 7: The person whose birthday is in February is the person who loves cooking.
                    try:
                        pos_feb = bday_perm.index("feb")
                        pos_cooking = hobby_perm.index("cooking")
                    except ValueError:
                        continue
                    if pos_feb != pos_cooking:
                        continue

                    # Constraint 8: The person who owns a Toyota Camry is Peter.
                    try:
                        pos_camry = car_perm.index("toyota camry")
                    except ValueError:
                        continue
                    if name_perm[pos_camry] != "Peter":
                        continue

                    # Constraint 9: The person whose birthday is in April is Arnold.
                    try:
                        pos_april = bday_perm.index("april")
                    except ValueError:
                        continue
                    if name_perm[pos_april] != "Arnold":
                        continue

                    # Constraint 10: Alice is the photography enthusiast.
                    try:
                        pos_alice = name_perm.index("Alice")
                    except ValueError:
                        continue
                    if hobby_perm[pos_alice] != "photography":
                        continue

                    # Constraint 11: Peter is the person whose birthday is in January.
                    if bday_perm[pos_Peter] != "jan":
                        continue

                    # Found a valid solution. Prepare output in the required JSON structure.
                    rows = []
                    for i in range(houses_count):
                        # Convert house number (1-indexed) and include all attributes as strings.
                        row = [str(i+1), name_perm[i], car_perm[i], bday_perm[i], hobby_perm[i]]
                        rows.append(row)
                        
                    result = {
                        "solution": {
                            "header": ["House", "Name", "CarModel", "Birthday", "Hobby"],
                            "rows": rows
                        }
                    }
                    print(json.dumps(result))
                    return

if __name__ == "__main__":
    main()