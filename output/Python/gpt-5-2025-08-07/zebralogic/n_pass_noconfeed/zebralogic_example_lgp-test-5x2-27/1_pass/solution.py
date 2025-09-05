import json
import itertools

def solve_puzzle():
    # Houses numbered 1..5 from left to right
    houses = [1, 2, 3, 4, 5]

    # Attributes
    names = ["Peter", "Alice", "Bob", "Eric", "Arnold"]
    heights = ["very tall", "average", "tall", "very short", "short"]

    # Helper functions for constraints
    def is_directly_left(pos_left, pos_right):
        return pos_left + 1 == pos_right

    def is_adjacent(pos1, pos2):
        return abs(pos1 - pos2) == 1

    # Brute-force with constraint checking
    for name_perm in itertools.permutations(names):
        # Map name -> house position (1-based)
        name_pos = {name_perm[i]: i + 1 for i in range(5)}

        # Clue 2: Peter is directly left of Bob.
        if not is_directly_left(name_pos["Peter"], name_pos["Bob"]):
            continue

        # Clue 3: Eric is somewhere to the left of Peter.
        if not (name_pos["Eric"] < name_pos["Peter"]):
            continue

        for height_perm in itertools.permutations(heights):
            # Map height -> house position (1-based)
            height_pos = {height_perm[i]: i + 1 for i in range(5)}

            # Clue 1: The person who is short is in the second house.
            if height_pos["short"] != 2:
                continue

            # Clue 7: The person who has an average height is in the fifth house.
            if height_pos["average"] != 5:
                continue

            # Clue 5: Alice is directly left of the person who has an average height.
            if not is_directly_left(name_pos["Alice"], height_pos["average"]):
                continue

            # Clue 4: The person who is very tall is directly left of Peter.
            if not is_directly_left(height_pos["very tall"], name_pos["Peter"]):
                continue

            # Clue 6: The person who is short and the person who is very short are next to each other.
            if not is_adjacent(height_pos["short"], height_pos["very short"]):
                continue

            # All constraints satisfied; build the solution rows
            rows = []
            for i in range(1, 6):
                rows.append([str(i), name_perm[i - 1], height_perm[i - 1]])

            solution = {
                "solution": {
                    "header": ["House", "Name", "Height"],
                    "rows": rows
                }
            }
            return solution

    # If no solution found (should not happen for a valid puzzle)
    return {
        "solution": {
            "header": ["House", "Name", "Height"],
            "rows": []
        }
    }

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result))