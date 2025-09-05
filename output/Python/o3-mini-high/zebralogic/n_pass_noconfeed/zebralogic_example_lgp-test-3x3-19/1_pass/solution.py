import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3]
    names = ["Eric", "Arnold", "Peter"]
    smoothies = ["desert", "watermelon", "cherry"]
    book_genres = ["science fiction", "romance", "mystery"]

    # Only consider name permutations where the first house is Peter (Clue 5)
    name_perms = [perm for perm in itertools.permutations(names) if perm[0] == "Peter"]

    for name_perm in name_perms:
        for smoothie_perm in itertools.permutations(smoothies):
            for book_perm in itertools.permutations(book_genres):
                # Clue 2: Arnold is the person who loves mystery books.
                valid = True
                for i in range(3):
                    if name_perm[i] == "Arnold" and book_perm[i] != "mystery":
                        valid = False
                        break
                if not valid:
                    continue

                # Clue 3: The person who loves science fiction books is not in the first house.
                if book_perm[0] == "science fiction":
                    continue

                # Clue 4: The Desert smoothie lover is directly left of the person who loves mystery books.
                try:
                    desert_index = smoothie_perm.index("desert")
                except ValueError:
                    continue
                # Desert smoothie cannot be in the last house.
                if desert_index == 2:
                    continue
                if book_perm[desert_index + 1] != "mystery":
                    continue

                # Clue 1: The person who likes Cherry smoothies is somewhere to the left of the person who loves mystery books.
                try:
                    cherry_index = smoothie_perm.index("cherry")
                except ValueError:
                    continue
                try:
                    mystery_index = book_perm.index("mystery")
                except ValueError:
                    continue
                if cherry_index >= mystery_index:
                    continue

                # All constraints satisfied, build the solution.
                solution_rows = []
                for i in range(3):
                    # House numbers as strings: "1", "2", "3"
                    solution_rows.append([str(i + 1), name_perm[i], smoothie_perm[i], book_perm[i]])
                
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Smoothie", "BookGenre"],
                        "rows": solution_rows
                    }
                }
                print(json.dumps(solution, indent=2))
                return

if __name__ == "__main__":
    solve_puzzle()