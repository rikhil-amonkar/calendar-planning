#!/usr/bin/env python3
import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3]
    names = ["Eric", "Arnold", "Peter"]
    smoothies = ["desert", "watermelon", "cherry"]
    books = ["science fiction", "romance", "mystery"]
    
    solution = None

    for perm_names in itertools.permutations(names):
        # Clue 5: Peter is in the first house.
        if perm_names[0] != "Peter":
            continue
        for perm_smoothies in itertools.permutations(smoothies):
            for perm_books in itertools.permutations(books):
                # Clue 3: The person who loves science fiction books is not in the first house.
                if perm_books[0] == "science fiction":
                    continue

                # Clue 2: Arnold is the person who loves mystery books.
                idx_arnold = perm_names.index("Arnold")
                if perm_books[idx_arnold] != "mystery":
                    continue

                # Clue 1: The person who likes Cherry smoothies is somewhere to the left of the person who loves mystery books.
                idx_cherry = perm_smoothies.index("cherry")
                idx_mystery = perm_books.index("mystery")
                if idx_cherry >= idx_mystery:
                    continue

                # Clue 4: The Desert smoothie lover is directly left of the person who loves mystery books.
                idx_desert = perm_smoothies.index("desert")
                # Desert cannot be in the last house because it must have a house to its right.
                if idx_desert == len(houses) - 1:
                    continue
                # The house to the right of desert must have mystery books and (because of Clue 2) must be Arnold.
                if perm_books[idx_desert + 1] != "mystery" or perm_names[idx_desert + 1] != "Arnold":
                    continue

                # If all constraints are satisfied, we have a solution.
                solution = []
                for i in range(len(houses)):
                    # House numbers as strings
                    solution.append([
                        str(houses[i]),
                        perm_names[i],
                        perm_smoothies[i],
                        perm_books[i]
                    ])
                return solution
    return solution

if __name__ == "__main__":
    sol = solve_puzzle()
    output = {
      "solution": {
        "header": ["House", "Name", "Smoothie", "BookGenre"],
        "rows": sol
      }
    }
    print(json.dumps(output, indent=2))