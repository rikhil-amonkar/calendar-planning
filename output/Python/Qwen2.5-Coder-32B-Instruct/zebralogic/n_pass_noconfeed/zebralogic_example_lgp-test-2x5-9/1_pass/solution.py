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

    # Function to check if a permutation satisfies all the clues
    def is_valid_solution(permutation):
        name1, name2 = permutation[0]
        book_genre1, book_genre2 = permutation[1]
        vacation1, vacation2 = permutation[2]
        animal1, animal2 = permutation[3]
        music_genre1, music_genre2 = permutation[4]

        # Check clue 1: The person who loves beach vacations is Eric.
        if vacation1 == "beach" and name1 != "Eric":
            return False
        if vacation2 == "beach" and name2 != "Eric":
            return False

        # Check clue 2: The person who loves pop music is the person who loves beach vacations.
        if vacation1 == "beach" and music_genre1 != "pop":
            return False
        if vacation2 == "beach" and music_genre2 != "pop":
            return False

        # Check clue 3: The person who loves rock music is the person who loves mystery books.
        if music_genre1 == "rock" and book_genre1 != "mystery":
            return False
        if music_genre2 == "rock" and book_genre2 != "mystery":
            return False

        # Check clue 4: The cat lover is not in the second house.
        if animal2 == "cat":
            return False

        # Check clue 5: The person who loves mystery books is in the first house.
        if book_genre1 != "mystery":
            return False

        return True

    # Find the valid solution
    for permutation in all_permutations:
        if is_valid_solution(permutation):
            name1, name2 = permutation[0]
            book_genre1, book_genre2 = permutation[1]
            vacation1, vacation2 = permutation[2]
            animal1, animal2 = permutation[3]
            music_genre1, music_genre2 = permutation[4]
            solution = {
                "solution": {
                    "header": ["House", "Name", "BookGenre", "Vacation", "Animal", "MusicGenre"],
                    "rows": [
                        ["1", name1, book_genre1, vacation1, animal1, music_genre1],
                        ["2", name2, book_genre2, vacation2, animal2, music_genre2]
                    ]
                }
            }
            print(json.dumps(solution, indent=2))
            return

# Run the solver
solve_puzzle()