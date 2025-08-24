import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]

    names = ["Bob", "Peter", "Alice", "Eric", "Carol", "Arnold"]
    vacations = ["mountain", "camping", "cruise", "city", "cultural", "beach"]

    solutions = []

    for name_perm in itertools.permutations(names):
        # Mapping helpers
        name_at_house = {house: name_perm[house - 1] for house in houses}
        house_of_name = {name: idx + 1 for idx, name in enumerate(name_perm)}

        # Apply name-related constraints
        # 2. Eric is somewhere to the right of Alice.
        if not (house_of_name["Eric"] > house_of_name["Alice"]):
            continue

        # 3. Eric is in the second house.
        if house_of_name["Eric"] != 2:
            continue

        # 5. Bob is directly left of Arnold.
        if not (house_of_name["Bob"] + 1 == house_of_name["Arnold"]):
            continue

        # Now iterate over vacation permutations with constraints
        for vac_perm in itertools.permutations(vacations):
            vac_at_house = {house: vac_perm[house - 1] for house in houses}
            house_of_vac = {v: idx + 1 for idx, v in enumerate(vac_perm)}

            # 4. The person who goes on cultural tours is in the third house.
            if house_of_vac["cultural"] != 3:
                continue

            # 9. The person who prefers city breaks is in the fourth house.
            if house_of_vac["city"] != 4:
                continue

            # 1. Cultural tours to the left of beach vacations.
            if not (house_of_vac["cultural"] < house_of_vac["beach"]):
                continue

            # 6. Camping not in the first house.
            if house_of_vac["camping"] == 1:
                continue

            # 7. The person who goes on cultural tours is Peter.
            if house_of_name["Peter"] != house_of_vac["cultural"]:
                continue

            # 8. The person who likes going on cruises is Bob.
            if house_of_vac["cruise"] != house_of_name["Bob"]:
                continue

            # If all constraints are satisfied, record solution
            solution_rows = []
            for h in houses:
                solution_rows.append([str(h), name_at_house[h], vac_at_house[h]])

            solutions.append({
                "solution": {
                    "header": ["House", "Name", "Vacation"],
                    "rows": solution_rows
                }
            })

    # Return the first solution (should be unique for this puzzle)
    if not solutions:
        raise ValueError("No solution found with the given constraints.")
    return solutions[0]

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))