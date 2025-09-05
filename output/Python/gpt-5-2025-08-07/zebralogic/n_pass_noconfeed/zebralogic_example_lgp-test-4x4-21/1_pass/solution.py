import itertools
import json

def solve_puzzle():
    # Houses are numbered 1 to 4 from left to right
    houses = [1, 2, 3, 4]

    # Attributes
    names = ["Eric", "Peter", "Alice", "Arnold"]
    cars = ["tesla model 3", "honda civic", "toyota camry", "ford f150"]
    birthdays = ["jan", "april", "sept", "feb"]
    hobbies = ["painting", "cooking", "gardening", "photography"]

    solutions = []

    for name_perm in itertools.permutations(names):
        # Pre-calc positions for efficiency
        pos_name = {name_perm[i]: i + 1 for i in range(4)}

        # Constraint 10: Alice is the photography enthusiast (will be checked after hobbies permutation)
        # Constraint 2,3: photography left of Eric and Peter (after hobbies permutation)

        for car_perm in itertools.permutations(cars):
            pos_car = {car_perm[i]: i + 1 for i in range(4)}

            # Constraint 4: Honda Civic directly left of Tesla Model 3
            if pos_car["honda civic"] != pos_car["tesla model 3"] - 1:
                continue

            # Constraint 6: Tesla Model 3 owner is Arnold
            if pos_car["tesla model 3"] != pos_name["Arnold"]:
                continue

            # Constraint 8: Toyota Camry is Peter
            if pos_car["toyota camry"] != pos_name["Peter"]:
                continue

            for bday_perm in itertools.permutations(birthdays):
                pos_bday = {bday_perm[i]: i + 1 for i in range(4)}

                # Constraint 11: Peter is January
                if pos_bday["jan"] != pos_name["Peter"]:
                    continue

                # Constraint 1: January not in second house
                if pos_bday["jan"] == 2:
                    continue

                # Constraint 9: April is Arnold
                if pos_bday["april"] != pos_name["Arnold"]:
                    continue

                for hobby_perm in itertools.permutations(hobbies):
                    pos_hobby = {hobby_perm[i]: i + 1 for i in range(4)}

                    # Constraint 10: Alice is the photography enthusiast
                    if pos_name["Alice"] != pos_hobby["photography"]:
                        continue

                    # Constraint 2: photography left of Eric
                    if not (pos_hobby["photography"] < pos_name["Eric"]):
                        continue

                    # Constraint 3: photography left of Peter
                    if not (pos_hobby["photography"] < pos_name["Peter"]):
                        continue

                    # Constraint 7: February is the person who loves cooking (equivalence)
                    if pos_bday["feb"] != pos_hobby["cooking"]:
                        continue

                    # Constraint 5: One house between Tesla Model 3 and gardening
                    if abs(pos_car["tesla model 3"] - pos_hobby["gardening"]) != 2:
                        continue

                    # All constraints satisfied; record solution
                    rows = []
                    for i in houses:
                        rows.append([
                            str(i),
                            name_perm[i - 1],
                            car_perm[i - 1],
                            bday_perm[i - 1],
                            hobby_perm[i - 1]
                        ])
                    solutions.append(rows)

    # Prepare output with the first solution (should be unique)
    result = {
        "solution": {
            "header": ["House", "Name", "CarModel", "Birthday", "Hobby"],
            "rows": solutions[0] if solutions else []
        }
    }
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))