#!/usr/bin/env python3
import itertools
import json

def solve():
    # Define the attributes
    names = ["Eric", "Arnold", "Peter"]
    smoothies = ["desert", "watermelon", "cherry"]
    book_genres = ["science fiction", "romance", "mystery"]

    solutions = []
    # Iterate over all possible assignments for names, smoothies, and book genres
    for perm_names in itertools.permutations(names):
        # Clue 5: Peter is in the first house.
        if perm_names[0] != "Peter":
            continue
        for perm_smoothies in itertools.permutations(smoothies):
            for perm_books in itertools.permutations(book_genres):
                # Clue 3: The person who loves science fiction books is not in the first house.
                if perm_books[0] == "science fiction":
                    continue
                # Clue 2: Arnold is the person who loves mystery books.
                # Find the house where Arnold resides, and check if that house's book is mystery.
                arnold_index = perm_names.index("Arnold")
                if perm_books[arnold_index] != "mystery":
                    continue
                # Also ensure that the house that has mystery for books is indeed Arnold.
                mystery_index = perm_books.index("mystery")
                if perm_names[mystery_index] != "Arnold":
                    continue
                # Clue 1: The person who likes Cherry smoothies is somewhere to the left of the person who loves mystery books.
                cherry_index = perm_smoothies.index("cherry")
                if cherry_index >= mystery_index:
                    continue
                # Clue 4: The Desert smoothie lover is directly left of the person who loves mystery books.
                # Ensure mystery is not in the first house and the house immediately to its left has the desert smoothie.
                if mystery_index == 0 or perm_smoothies[mystery_index - 1] != "desert":
                    continue

                # If all constraints are satisfied, record the solution.
                solution = []
                for i in range(3):
                    house_number = str(i + 1)
                    row = [house_number, perm_names[i], perm_smoothies[i], perm_books[i]]
                    solution.append(row)
                solutions.append(solution)

    # Assume the puzzle has a unique solution; if there are multiple, take the first one.
    final_solution = solutions[0] if solutions else []

    output = {
        "solution": {
            "header": ["House", "Name", "favorite smoothie", "favorite book genre"],
            "rows": final_solution
        }
    }
    print(json.dumps(output, indent=2))

if __name__ == '__main__':
    solve()