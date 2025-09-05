import json
import itertools

def solve_puzzle():
    # Input variables
    houses = [1, 2]  # left to right
    names = ["Arnold", "Eric"]
    birthdays = ["april", "sept"]
    mothers = ["Aniya", "Holly"]

    solutions = []

    # Enumerate all bijective assignments
    for name_perm in itertools.permutations(names):
        assign_name = dict(zip(houses, name_perm))

        for mother_perm in itertools.permutations(mothers):
            assign_mother = dict(zip(houses, mother_perm))

            # Clue 1: Eric is somewhere to the left of the person whose mother's name is Holly.
            house_of_eric = [h for h in houses if assign_name[h] == "Eric"][0]
            house_with_mother_holly = [h for h in houses if assign_mother[h] == "Holly"][0]
            if not (house_of_eric < house_with_mother_holly):
                continue

            for birthday_perm in itertools.permutations(birthdays):
                assign_birthday = dict(zip(houses, birthday_perm))

                # Clue 2: The person whose birthday is in April is in the first house.
                if assign_birthday[1] != "april":
                    continue

                # If all constraints satisfied, store solution
                solutions.append({
                    "Name": assign_name,
                    "Birthday": assign_birthday,
                    "Mother": assign_mother
                })

    if not solutions:
        raise ValueError("No solution found for the given puzzle.")
    if len(solutions) > 1:
        # In case of multiple solutions, select the first deterministically
        solution = solutions[0]
    else:
        solution = solutions[0]

    # Prepare output
    header = ["House", "Name", "Birthday", "Mother"]
    rows = []
    for h in houses:
        rows.append([
            str(h),
            solution["Name"][h],
            solution["Birthday"][h],
            solution["Mother"][h]
        ])

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))