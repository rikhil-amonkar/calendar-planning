import itertools
import json

names = ["Alice", "Arnold", "Eric", "Peter", "Bob", "Carol"]
cars = ["chevrolet silverado", "ford f150", "honda civic", "toyota camry", "bmw 3 series", "tesla model 3"]

solution = None

for name_perm in itertools.permutations(names):
    # Check Carol is to the right of Eric and not in house 6
    eric_pos = name_perm.index("Eric")
    carol_pos = name_perm.index("Carol")
    if carol_pos <= eric_pos or carol_pos == 5:
        continue

    arnold_pos = name_perm.index("Arnold")
    if arnold_pos == 0:
        continue  # no house to the left
    nurse_pos = arnold_pos - 1
    if nurse_pos == 4:  # house 5 (index 4) has ford f150, can't be nurse's car
        continue

    # Prepare remaining names for occupations
    remaining_names = []
    for i in range(6):
        if name_perm[i] in ["Alice", "Carol", "Peter"]:
            remaining_names.append((i, name_perm[i]))

    # Generate permutations for the remaining occupations
    for occ_perm in itertools.permutations(["teacher", "nurse", "lawyer"]):
        occupations = [None] * 6
        # Assign fixed occupations
        for i in range(6):
            if name_perm[i] == "Bob":
                occupations[i] = "engineer"
            elif name_perm[i] == "Arnold":
                occupations[i] = "artist"
            elif name_perm[i] == "Eric":
                occupations[i] = "doctor"
        # Assign remaining occupations
        for idx, (pos, _) in enumerate(remaining_names):
            occupations[pos] = occ_perm[idx]

        # Check if nurse is in the correct position
        if occupations[nurse_pos] != "nurse":
            continue

        # Check teacher is to the left of nurse
        teacher_pos = None
        for i in range(6):
            if occupations[i] == "teacher":
                teacher_pos = i
                break
        if teacher_pos >= nurse_pos:
            continue

        # Check lawyer not in house 5 (index 4)
        lawyer_pos = None
        for i in range(6):
            if occupations[i] == "lawyer":
                lawyer_pos = i
                break
        if lawyer_pos == 4:
            continue

        # Check Peter and lawyer are two apart
        peter_pos = name_perm.index("Peter")
        if abs(peter_pos - lawyer_pos) != 2:
            continue

        # Now handle cars
        # Fixed positions: ford f150 in 4 (house 5), toyota camry in nurse_pos
        fixed_positions = {4: "ford f150", nurse_pos: "toyota camry"}
        remaining_car_positions = [i for i in range(6) if i not in fixed_positions]
        remaining_cars = ["chevrolet silverado", "honda civic", "bmw 3 series", "tesla model 3"]

        for car_perm in itertools.permutations(remaining_cars):
            car_list = [""] * 6
            # Assign fixed positions
            car_list[4] = "ford f150"
            car_list[nurse_pos] = "toyota camry"
            # Assign remaining cars
            for i, pos in enumerate(remaining_car_positions):
                car_list[pos] = car_perm[i]

            # Check clue 2: chevrolet silverado not in house 2 (index 1)
            if car_list[1] == "chevrolet silverado":
                continue

            # Check clue 3: Honda Civic and Peter are adjacent
            honda_pos = car_list.index("honda civic")
            if abs(honda_pos - peter_pos) != 1:
                continue

            # Check clue 13: Tesla and Bob are two apart
            tesla_pos = car_list.index("tesla model 3")
            bob_pos = name_perm.index("Bob")
            if abs(tesla_pos - bob_pos) != 2:
                continue

            # All constraints satisfied
            solution_rows = []
            for i in range(6):
                house_num = str(i + 1)
                solution_rows.append([
                    house_num,
                    name_perm[i],
                    occupations[i],
                    car_list[i]
                ])
            solution = {
                "solution": {
                    "header": ["House", "Name", "Occupation", "CarModel"],
                    "rows": solution_rows
                }
            }
            print(json.dumps(solution, indent=2))
            exit()

print("No solution found")