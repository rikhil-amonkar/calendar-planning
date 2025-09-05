import json
from itertools import permutations

def solve_puzzle():
    # Houses are numbered 1..6, we'll use 0-based indices internally
    houses = list(range(6))

    # Attributes
    names = ["Bob", "Peter", "Alice", "Eric", "Carol", "Arnold"]
    vacations = ["mountain", "camping", "cruise", "city", "cultural", "beach"]

    solutions = []

    # Iterate over all possible assignments of names to houses
    for name_perm in permutations(names):
        # Clue 3: Eric is in the second house (index 1)
        if name_perm[1] != "Eric":
            continue

        # Clue 2: Eric is somewhere to the right of Alice
        if name_perm.index("Eric") <= name_perm.index("Alice"):
            continue

        # Clue 5: Bob is directly left of Arnold
        if name_perm.index("Arnold") != name_perm.index("Bob") + 1:
            continue

        # Iterate over all possible assignments of vacations to houses
        for vac_perm in permutations(vacations):
            # Clue 4: The person who goes on cultural tours is in the third house (index 2)
            if vac_perm[2] != "cultural":
                continue

            # Clue 9: The person who prefers city breaks is in the fourth house (index 3)
            if vac_perm[3] != "city":
                continue

            # Clue 1: cultural is somewhere to the left of beach
            if vac_perm.index("cultural") >= vac_perm.index("beach"):
                continue

            # Clue 6: camping not in first house (index 0)
            if vac_perm[0] == "camping":
                continue

            # Clue 7: The person who goes on cultural tours is Peter
            if name_perm.index("Peter") != vac_perm.index("cultural"):
                continue

            # Clue 8: The person who likes going on cruises is Bob
            if name_perm.index("Bob") != vac_perm.index("cruise"):
                continue

            # If all constraints satisfied, record solution
            solutions.append((name_perm, vac_perm))

    if not solutions:
        raise ValueError("No solution found.")
    # Assuming unique solution as per typical Zebra puzzles
    name_sol, vac_sol = solutions[0]

    result = {
        "solution": {
            "header": ["House", "Name", "Vacation"],
            "rows": [
                [str(i + 1), name_sol[i], vac_sol[i]] for i in range(6)
            ],
        }
    }
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False))