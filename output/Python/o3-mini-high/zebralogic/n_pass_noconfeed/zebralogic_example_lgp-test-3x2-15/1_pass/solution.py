import itertools
import json

def solve_puzzle():
    # Define the available attributes
    names = ["Arnold", "Peter", "Eric"]
    heights = ["short", "average", "very short"]

    solutions = []

    # Houses are numbered 1,2,3 (but we'll use indices 0,1,2)
    for name_perm in itertools.permutations(names):
        for height_perm in itertools.permutations(heights):
            # Constraint 2: The person who is short is in the first house.
            if height_perm[0] != "short":
                continue

            # Constraint 3: There is one house between the person who is short and the person who is very short.
            try:
                index_short = height_perm.index("short")
                index_very_short = height_perm.index("very short")
            except ValueError:
                continue
            if abs(index_short - index_very_short) != 2:
                continue

            # Constraint 1: Peter is somewhere to the right of Eric.
            index_peter = name_perm.index("Peter")
            index_eric = name_perm.index("Eric")
            if index_peter <= index_eric:
                continue

            # Constraint 4: Arnold and the person who is very short are next to each other.
            index_arnold = name_perm.index("Arnold")
            if abs(index_arnold - index_very_short) != 1:
                continue

            # All constraints satisfied, record the solution.
            solution_rows = []
            for i in range(3):
                # House numbers are 1-indexed.
                solution_rows.append([str(i+1), name_perm[i], height_perm[i]])
            solutions.append(solution_rows)

    # Assuming a unique solution exists, take the first solution.
    if solutions:
        return solutions[0]
    else:
        return []

def main():
    solution_rows = solve_puzzle()
    result = {
        "solution": {
            "header": ["House", "Name", "Height"],
            "rows": solution_rows
        }
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()