import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Arnold", "Eric"]
    book_genres = ["science fiction", "mystery"]
    vacations = ["mountain", "beach"]
    animals = ["cat", "horse"]
    music_genres = ["rock", "pop"]

    # Generate all possible permutations for the two houses
    all_permutations = list(itertools.permutations(names)) * \
                       list(itertools.permutations(book_genres)) * \
                       list(itertools.permutations(vacations)) * \
                       list(itertools.permutations(animals)) * \
                       list(itertools.permutations(music_genres))

    # Define the constraints
    def is_valid_solution(solution):
        # Unpack the solution into separate lists for each category
        name1, name2 = solution[0]
        book_genre1, book_genre2 = solution[1]
        vacation1, vacation2 = solution[2]
        animal1, animal2 = solution[3]
        music_genre1, music_genre2 = solution[4]

        # Apply the clues
        if vacation2 == "beach" and name2 != "Eric":
            return False
        if vacation2 == "beach" and music_genre2 != "pop":
            return False
        if music_genre1 == "rock" and book_genre1 != "mystery":
            return False
        if animal2 == "cat":
            return False
        if book_genre1 != "mystery":
            return False

        return True

    # Find the valid solution
    for perm in all_permutations:
        if is_valid_solution(perm):
            # Format the solution as required
            solution = {
                "solution": {
                    "header": ["House", "Name", "BookGenre", "Vacation", "Animal", "MusicGenre"],
                    "rows": [
                        ["1", perm[0][0], perm[1][0], perm[2][0], perm[3][0], perm[4][0]],
                        ["2", perm[0][1], perm[1][1], perm[2][1], perm[3][1], perm[4][1]]
                    ]
                }
            }
            return json.dumps(solution, indent=2)

# Solve the puzzle and print the result
print(solve_puzzle())