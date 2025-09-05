import json
from itertools import permutations

def solve_puzzle():
    # Define the sets of possible attributes.
    names = ["Arnold", "Eric", "Peter"]
    music_genres = ["pop", "rock", "classical"]
    children = ["Fred", "Meredith", "Bella"]
    book_genres = ["mystery", "romance", "science fiction"]

    solution = None

    # Try all possible assignments for each attribute across 3 houses.
    for nm in permutations(names):
        # Clue 2: Peter is in the first house.
        if nm[0] != "Peter":
            continue
        for mg in permutations(music_genres):
            for ch in permutations(children):
                for bg in permutations(book_genres):
                    valid = True

                    # Clue 1: The house whose child is Fred is directly left of the house that loves mystery books.
                    idx_fred = ch.index("Fred")
                    if idx_fred == 2 or bg[idx_fred + 1] != "mystery":
                        valid = False

                    if not valid:
                        continue

                    # Clue 3 and Clue 5: The person who loves mystery books also loves classical music, 
                    # and Eric is the person who loves mystery books.
                    try:
                        idx_mystery = bg.index("mystery")
                    except ValueError:
                        valid = False
                    else:
                        if nm[idx_mystery] != "Eric" or mg[idx_mystery] != "classical":
                            valid = False

                    if not valid:
                        continue

                    # Clue 4: The person who loves science fiction books has the child named Meredith.
                    idx_scifi = bg.index("science fiction")
                    if ch[idx_scifi] != "Meredith":
                        valid = False

                    if not valid:
                        continue

                    # Clue 6: The person who loves rock music is somewhere to the right of the person who loves romance books.
                    idx_rock = mg.index("rock")
                    idx_romance = bg.index("romance")
                    if idx_rock <= idx_romance:
                        valid = False

                    if not valid:
                        continue

                    # If all constraints are satisfied, record the solution.
                    current_solution = []
                    for i in range(3):
                        # House numbers are strings "1", "2", "3" in left to right order.
                        current_solution.append([str(i+1), nm[i], mg[i], ch[i], bg[i]])
                    solution = current_solution
                    break
                if solution:
                    break
            if solution:
                break
        if solution:
            break

    return solution

def main():
    sol = solve_puzzle()
    output = {
        "solution": {
            "header": ["House", "Name", "MusicGenre", "Children", "BookGenre"],
            "rows": sol if sol else []
        }
    }
    print(json.dumps(output))

if __name__ == "__main__":
    main()