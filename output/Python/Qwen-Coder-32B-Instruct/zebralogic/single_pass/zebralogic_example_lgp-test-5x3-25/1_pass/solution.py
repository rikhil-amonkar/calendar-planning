import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Arnold", "Bob", "Alice", "Eric", "Peter"]
    heights = ["very tall", "average", "tall", "very short", "short"]
    lunches = ["stew", "grilled cheese", "spaghetti", "pizza", "stir fry"]

    # Generate all possible permutations for each category
    permutations = list(itertools.permutations(names)) * \
                   list(itertools.permutations(heights)) * \
                   list(itertools.permutations(lunches))

    # Check each permutation against the clues
    for name_perm in itertools.permutations(names):
        for height_perm in itertools.permutations(heights):
            for lunch_perm in itertools.permutations(lunches):
                # Unpack the permutations
                n1, n2, n3, n4, n5 = name_perm
                h1, h2, h3, h4, h5 = height_perm
                l1, l2, l3, l4, l5 = lunch_perm

                # Apply the clues
                if (n3 == "Eric" and  # Clue 7
                    h3 == "tall" and  # Clue 6, 7
                    l3 == "pizza" and  # Clue 6
                    n5 != "Alice" and  # Clue 1
                    h2 != "average" and  # Clue 3
                    (h1 == "average" or h2 == "average" or h3 == "average" or h4 == "average") and  # Clue 3
                    (h1 == "average" and (l1 == "stew" or l2 == "stew" or l3 == "stew" or l4 == "stew")) or \
                    (h2 == "average" and (l2 == "stew" or l3 == "stew" or l4 == "stew")) or \
                    (h3 == "average" and (l3 == "stew" or l4 == "stew")) or \
                    (h4 == "average" and l4 == "stew") and  # Clue 4
                    n1 == "Arnold" or n2 == "Arnold" or n3 == "Arnold" or n4 == "Arnold" and  # Clue 5
                    l1 == "stir fry" or l2 == "stir fry" or l3 == "stir fry" or l4 == "stir fry" or l5 == "stir fry" and  # Clue 5
                    n1 == "Alice" and h1 == "short" and  # Clue 1
                    n2 != "Arnold" and n3 != "Arnold" and n4 != "Arnold" and n5 != "Arnold" and  # Clue 5
                    (n2 == "Arnold" or n3 == "Arnold" or n4 == "Arnold" or n5 == "Arnold") and  # Clue 5
                    (n2 == "Arnold" and (n3 == "Bob" or n4 == "Bob" or n5 == "Bob")) or \
                    (n3 == "Arnold" and (n4 == "Bob" or n5 == "Bob")) or \
                    (n4 == "Arnold" and n5 == "Bob") and  # Clue 8
                    (n2 == "Eric" and (n3 == "grilled cheese" or n4 == "grilled cheese" or n5 == "grilled cheese")) or \
                    (n3 == "Eric" and (n4 == "grilled cheese" or n5 == "grilled cheese")) or \
                    (n4 == "Eric" and n5 == "grilled cheese") and  # Clue 9
                    (n1 == "very short" and n2 == "Arnold" or n2 == "very short" and n3 == "Arnold" or n3 == "very short" and n4 == "Arnold" or n4 == "very short" and n5 == "Arnold")):  # Clue 10

                    # Construct the solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Height", "Lunch"],
                            "rows": [
                                ["1", n1, h1, l1],
                                ["2", n2, h2, l2],
                                ["3", n3, h3, l3],
                                ["4", n4, h4, l4],
                                ["5", n5, h5, l5]
                            ]
                        }
                    }

                    # Output the solution as JSON
                    print(json.dumps(solution, indent=2))
                    return

# Solve the puzzle
solve_puzzle()