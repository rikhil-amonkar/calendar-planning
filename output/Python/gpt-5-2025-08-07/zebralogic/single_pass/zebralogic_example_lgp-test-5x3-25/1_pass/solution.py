import itertools
import json

def solve_puzzle():
    houses = [0, 1, 2, 3, 4]  # 0-based indices for houses 1..5
    Names = ["Arnold", "Bob", "Alice", "Eric", "Peter"]
    Heights = ["very tall", "average", "tall", "very short", "short"]
    Foods = ["stew", "grilled cheese", "spaghetti", "pizza", "stir fry"]

    solutions = []

    # Iterate over all possible assignments of people to houses (house -> name)
    for names in itertools.permutations(Names):
        # Clue 7 and 2: Eric is tall and the tall person is in the third house -> Eric is in house 3
        if names[2] != "Eric":
            continue

        idx_arnold = names.index("Arnold")
        idx_bob = names.index("Bob")
        idx_alice = names.index("Alice")
        idx_eric = 2  # from above

        # Clue 8: Bob is somewhere to the right of Arnold
        if not (idx_bob > idx_arnold):
            continue

        # Iterate over heights
        for heights in itertools.permutations(Heights):
            # Clue 2: The person who is tall is in the third house
            if heights[2] != "tall":
                continue

            # Clue 7: Eric is the person who is tall (already ensured by names[2] == "Eric" and heights[2] == "tall")

            # Clue 1: Alice is short
            if heights[idx_alice] != "short":
                continue

            # Clue 3: The person who has an average height is not in the second house
            if heights[1] == "average":
                continue

            # Clue 10: The person who is very short is somewhere to the left of Arnold
            if heights[heights.index("very short")] >= idx_arnold:
                continue

            # Iterate over foods
            for foods in itertools.permutations(Foods):
                # Clue 6: The person who is a pizza lover is the person who is tall -> house 3 has pizza
                if foods[2] != "pizza":
                    continue

                # Clue 5: The person who loves stir fry is Arnold
                if foods[idx_arnold] != "stir fry":
                    continue

                # Clue 9: The person who loves grilled cheese is somewhere to the right of Eric
                if foods.index("grilled cheese") <= idx_eric:
                    continue

                # Clue 4: The average height person is to the left of the person who loves stew
                if heights.index("average") >= foods.index("stew"):
                    continue

                # All constraints satisfied, record solution
                solutions.append((names, heights, foods))

    if not solutions:
        raise RuntimeError("No solution found")

    # Assuming unique solution; take the first
    names, heights, foods = solutions[0]

    result = {
        "solution": {
            "header": ["House", "Name", "Height", "Food"],
            "rows": [
                [str(i + 1), names[i], heights[i], foods[i]] for i in range(5)
            ],
        }
    }
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False))