import itertools
import json

def solve_puzzle():
    # Puzzle parameters
    houses = [1, 2, 3, 4]  # left to right
    names = ["Eric", "Peter", "Alice", "Arnold"]
    car_models = ["tesla model 3", "honda civic", "toyota camry", "ford f150"]
    birthdays = ["jan", "april", "sept", "feb"]
    hobbies = ["painting", "cooking", "gardening", "photography"]

    NAME = "Name"
    CAR = "CarModel"
    BDAY = "Birthday"
    HOBBY = "Hobby"

    # Helper to check adjacency left-of
    def is_direct_left(idx_left, idx_right):
        return idx_left + 1 == idx_right

    # Attempt all permutations for names across houses (0-based indices)
    for name_perm in itertools.permutations(names):
        # Positions by name
        pos = {name_perm[i]: i for i in range(4)}

        # Clue 11 + Clue 1: Peter is Jan and Jan is not in house 2 (index 1)
        if pos["Peter"] == 1:
            continue

        # Clue 10 + 2 + 3: Alice is photography; photography is left of Eric and Peter
        if not (pos["Alice"] < pos["Eric"] and pos["Alice"] < pos["Peter"]):
            continue

        # Clue 6 + 4: Arnold owns Tesla; Honda is directly left of Tesla
        # Therefore, Arnold cannot be in the first house
        if pos["Arnold"] == 0:
            continue

        # Car assignments
        cars = [None] * 4
        # Clue 6: Arnold has Tesla Model 3
        cars[pos["Arnold"]] = "tesla model 3"
        # Clue 4: Honda directly left of Tesla
        left_of_tesla = pos["Arnold"] - 1
        cars[left_of_tesla] = "honda civic"
        # Clue 8: Peter has Toyota Camry
        if cars[pos["Peter"]] is not None and cars[pos["Peter"]] != "toyota camry":
            continue
        if pos["Peter"] == left_of_tesla:
            # Would force Peter to have Honda, conflicting with Camry
            continue
        cars[pos["Peter"]] = "toyota camry"
        # Fill remaining car
        for i in range(4):
            if cars[i] is None:
                cars[i] = "ford f150"

        # Hobbies
        # Clue 10: Alice is photography
        base_hobbies = [None] * 4
        base_hobbies[pos["Alice"]] = "photography"

        # Clue 5: One house between Tesla and Gardening
        possible_garden_indices = []
        for gi in [pos["Arnold"] - 2, pos["Arnold"] + 2]:
            if 0 <= gi < 4:
                possible_garden_indices.append(gi)

        for gidx in possible_garden_indices:
            # Alice can't be gardening (she's photography)
            if gidx == pos["Alice"]:
                continue

            hobbies_assign = base_hobbies[:]
            hobbies_assign[gidx] = "gardening"

            remaining_hobby_indices = [i for i in range(4) if hobbies_assign[i] is None]
            # Remaining hobbies are painting and cooking
            for extra_hobbies in itertools.permutations(["painting", "cooking"], 2):
                temp_hobbies = hobbies_assign[:]
                for idx, hob in zip(remaining_hobby_indices, extra_hobbies):
                    temp_hobbies[idx] = hob

                # Birthdays
                bdays = [None] * 4
                # Clue 9: Arnold is April
                bdays[pos["Arnold"]] = "april"
                # Clue 11: Peter is January
                bdays[pos["Peter"]] = "jan"
                # Remaining months: sept and feb
                remaining_bday_indices = [i for i in range(4) if bdays[i] is None]
                for extra_bdays in itertools.permutations(["sept", "feb"], 2):
                    temp_bdays = bdays[:]
                    for idx, m in zip(remaining_bday_indices, extra_bdays):
                        temp_bdays[idx] = m

                    # Clue 7: February == Cooking
                    ok_feb_cooking = True
                    for i in range(4):
                        if temp_bdays[i] == "feb" and temp_hobbies[i] != "cooking":
                            ok_feb_cooking = False
                            break
                        if temp_hobbies[i] == "cooking" and temp_bdays[i] != "feb":
                            ok_feb_cooking = False
                            break
                    if not ok_feb_cooking:
                        continue

                    # Validate all clues comprehensively

                    # Clue 1: January not in second house (index 1)
                    if temp_bdays[1] == "jan":
                        continue

                    # Clue 2 and 3: Photography (Alice) left of Eric and Peter
                    if not (pos["Alice"] < pos["Eric"] and pos["Alice"] < pos["Peter"]):
                        continue

                    # Clue 4: Honda directly left of Tesla
                    honda_idx = cars.index("honda civic")
                    tesla_idx = cars.index("tesla model 3")
                    if not is_direct_left(honda_idx, tesla_idx):
                        continue

                    # Clue 5: One house between Tesla and Gardening
                    garden_idx = temp_hobbies.index("gardening")
                    if abs(tesla_idx - garden_idx) != 2:
                        continue

                    # Clue 6: Tesla owner is Arnold
                    if name_perm[tesla_idx] != "Arnold":
                        continue

                    # Clue 8: Toyota Camry owner is Peter
                    if cars[pos["Peter"]] != "toyota camry":
                        continue

                    # Clue 9: April is Arnold
                    if temp_bdays[pos["Arnold"]] != "april":
                        continue

                    # Clue 10: Alice is photography
                    if temp_hobbies[pos["Alice"]] != "photography":
                        continue

                    # Clue 11 handled above (Peter is January + not in house 2 already checked)

                    # All constraints satisfied, build solution
                    result_rows = []
                    for i in range(4):
                        result_rows.append([
                            str(houses[i]),
                            name_perm[i],
                            cars[i],
                            temp_bdays[i],
                            temp_hobbies[i]
                        ])

                    solution = {
                        "solution": {
                            "header": ["House", "Name", "CarModel", "Birthday", "Hobby"],
                            "rows": result_rows
                        }
                    }
                    return solution

    raise ValueError("No solution found")

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False))