#!/usr/bin/env python3
import itertools
import json

def main():
    houses = [1, 2]
    names = ["Eric", "Arnold"]
    mothers = ["Aniya", "Holly"]
    carModels = ["ford f150", "tesla model 3"]
    heights = ["short", "very short"]

    solution = None

    for name_perm in itertools.permutations(names):
        for mother_perm in itertools.permutations(mothers):
            for car_perm in itertools.permutations(carModels):
                for height_perm in itertools.permutations(heights):
                    # Constraint 2: Arnold is the person who is short.
                    try:
                        index_arnold = name_perm.index("Arnold")
                    except ValueError:
                        continue
                    if height_perm[index_arnold] != "short":
                        continue

                    # Constraint 1: The person who owns a Tesla Model 3 is somewhere to the right of Arnold.
                    try:
                        index_tesla = car_perm.index("tesla model 3")
                    except ValueError:
                        continue
                    if index_tesla <= index_arnold:
                        continue

                    # Constraint 3: The person whose mother's name is Holly is in the second house.
                    if mother_perm[1] != "Holly":
                        continue

                    # All constraints satisfied, record the solution.
                    current_solution = []
                    for i in range(len(houses)):
                        current_solution.append([
                            str(houses[i]),
                            name_perm[i],
                            mother_perm[i],
                            car_perm[i],
                            height_perm[i]
                        ])
                    solution = current_solution
                    break
                if solution:
                    break
            if solution:
                break
        if solution:
            break

    output = {
        "solution": {
            "header": ["House", "Name", "Mother", "CarModel", "Height"],
            "rows": solution
        }
    }
    print(json.dumps(output, indent=2))

if __name__ == '__main__':
    main()