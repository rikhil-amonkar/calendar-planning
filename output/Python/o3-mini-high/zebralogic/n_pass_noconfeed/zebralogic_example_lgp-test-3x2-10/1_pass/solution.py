import json
import itertools

def main():
    houses = [1, 2, 3]
    names = ["Eric", "Arnold", "Peter"]
    heights = ["short", "very short", "average"]

    solution = None

    # Iterate over all possible assignments for names and heights
    for name_perm in itertools.permutations(names):
        # Constraint 1: Eric is not in the first house.
        if name_perm[0] == "Eric":
            continue
        # Constraint 4: Arnold is not in the first house.
        if name_perm[0] == "Arnold":
            continue

        for height_perm in itertools.permutations(heights):
            # Constraint 3: The person who is very short is Eric.
            index_very_short = height_perm.index("very short")
            index_eric = name_perm.index("Eric")
            if index_very_short != index_eric:
                continue

            # Constraint 2: The person who is very short is somewhere to the left of the person who is short.
            index_short = height_perm.index("short")
            if not (index_eric < index_short):
                continue

            # When all constraints are satisfied, build the solution dictionary
            solution = {
                "solution": {
                    "header": ["House", "Name", "Height"],
                    "rows": []
                }
            }
            for i, house in enumerate(houses):
                solution["solution"]["rows"].append([str(house), name_perm[i], height_perm[i]])

            # Print the valid solution as formatted JSON and exit.
            print(json.dumps(solution, indent=2))
            return

if __name__ == "__main__":
    main()