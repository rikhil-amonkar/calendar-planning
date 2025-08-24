import itertools
import json

def solve_puzzle():
    # Houses numbered left (1) to right (2)
    houses = [1, 2]

    # Attributes
    Names = ["Eric", "Arnold"]
    Mothers = ["Aniya", "Holly"]
    CarModels = ["ford f150", "tesla model 3"]
    Heights = ["short", "very short"]

    solutions = []

    # Iterate over all permutations respecting uniqueness across houses
    for names_perm in itertools.permutations(Names):
        # Determine Arnold's house
        house_of_arnold = names_perm.index("Arnold")

        for mothers_perm in itertools.permutations(Mothers):
            # Clue 3: The person whose mother's name is Holly is in the second house.
            if mothers_perm[1] != "Holly":
                continue

            for cars_perm in itertools.permutations(CarModels):
                # Clue 1: The person who owns a Tesla Model 3 is somewhere to the right of Arnold.
                house_of_tesla = cars_perm.index("tesla model 3")
                if not (house_of_tesla > house_of_arnold):
                    continue

                for heights_perm in itertools.permutations(Heights):
                    # Clue 2: Arnold is the person who is short.
                    if heights_perm[house_of_arnold] != "short":
                        continue

                    # If all constraints satisfied, record solution
                    solution_rows = []
                    for i, house in enumerate(houses):
                        solution_rows.append([
                            str(house),
                            names_perm[i],
                            mothers_perm[i],
                            cars_perm[i],
                            heights_perm[i],
                        ])
                    solutions.append(solution_rows)

    # Ideally, there should be exactly one solution
    if not solutions:
        raise ValueError("No solution found with the given constraints.")
    # If multiple, choose the first (but puzzle is expected to be unique)
    final_rows = solutions[0]

    result = {
        "solution": {
            "header": ["House", "Name", "Mother", "CarModel", "Height"],
            "rows": final_rows
        }
    }
    return result

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))