import itertools
import json

def solve_puzzle():
    # Input variables
    houses = [1, 2]  # Left to right
    names = ["Arnold", "Eric"]
    birthdays = ["april", "sept"]
    mothers = ["Aniya", "Holly"]

    solutions = []

    # Enumerate all possible assignments (permutations) for each category
    for name_perm in itertools.permutations(names):
        name_by_house = {houses[i]: name_perm[i] for i in range(len(houses))}
        house_of_name = {v: k for k, v in name_by_house.items()}

        for birthday_perm in itertools.permutations(birthdays):
            birthday_by_house = {houses[i]: birthday_perm[i] for i in range(len(houses))}
            house_of_birthday = {v: k for k, v in birthday_by_house.items()}

            # Clue 2: The person whose birthday is in April is in the first house.
            if house_of_birthday["april"] != 1:
                continue

            for mother_perm in itertools.permutations(mothers):
                mother_by_house = {houses[i]: mother_perm[i] for i in range(len(houses))}
                house_of_mother = {v: k for k, v in mother_by_house.items()}

                # Clue 1: Eric is somewhere to the left of the person whose mother's name is Holly.
                if not (house_of_name["Eric"] < house_of_mother["Holly"]):
                    continue

                # If all constraints are satisfied, record the solution
                solution_rows = []
                for h in houses:
                    solution_rows.append([
                        str(h),
                        name_by_house[h],
                        birthday_by_house[h],
                        mother_by_house[h],
                    ])
                solutions.append(solution_rows)

    # Ensure at least one solution found
    if not solutions:
        raise ValueError("No solution found with the given constraints.")

    # If multiple solutions exist, choose the first (puzzle should be unique)
    final_rows = solutions[0]

    result = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Mother"],
            "rows": final_rows
        }
    }
    return result

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))