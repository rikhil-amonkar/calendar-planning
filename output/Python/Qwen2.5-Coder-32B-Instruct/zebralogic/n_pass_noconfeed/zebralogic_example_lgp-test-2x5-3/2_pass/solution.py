import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Eric", "Arnold"]
    hobbies = ["gardening", "photography"]
    book_genres = ["science fiction", "mystery"]
    music_genres = ["rock", "pop"]
    birthdays = ["april", "sept"]

    # Generate all possible combinations of permutations for the two houses
    all_combinations = list(itertools.product(
        itertools.permutations(names),
        itertools.permutations(hobbies),
        itertools.permutations(book_genres),
        itertools.permutations(music_genres),
        itertools.permutations(birthdays)
    ))

    # Function to check if a permutation satisfies all the clues
    def is_valid(combination):
        name1, name2 = combination[0]
        hobby1, hobby2 = combination[1]
        book_genre1, book_genre2 = combination[2]
        music_genre1, music_genre2 = combination[3]
        birthday1, birthday2 = combination[4]

        # Clue 1: The person who loves mystery books is the person who loves rock music.
        if book_genre1 == "mystery" and music_genre1 != "rock":
            return False
        if book_genre2 == "mystery" and music_genre2 != "rock":
            return False

        # Clue 2: Arnold is not in the first house.
        if name1 == "Arnold":
            return False

        # Clue 3: The person who loves mystery books is the person who enjoys gardening.
        if book_genre1 == "mystery" and hobby1 != "gardening":
            return False
        if book_genre2 == "mystery" and hobby2 != "gardening":
            return False

        # Clue 4: The person whose birthday is in April is Arnold.
        if birthday1 == "april" and name1 != "Arnold":
            return False
        if birthday2 == "april" and name2 != "Arnold":
            return False

        # Clue 5: The person who loves mystery books is in the first house.
        if book_genre2 == "mystery":
            return False

        return True

    # Find the valid combination
    for combination in all_combinations:
        if is_valid(combination):
            name1, name2 = combination[0]
            hobby1, hobby2 = combination[1]
            book_genre1, book_genre2 = combination[2]
            music_genre1, music_genre2 = combination[3]
            birthday1, birthday2 = combination[4]
            break

    # Prepare the solution in the required JSON format
    solution = {
        "solution": {
            "header": ["House", "Name", "Hobby", "BookGenre", "MusicGenre", "Birthday"],
            "rows": [
                ["1", name1, hobby1, book_genre1, music_genre1, birthday1],
                ["2", name2, hobby2, book_genre2, music_genre2, birthday2]
            ]
        }
    }

    # Output the solution as JSON
    print(json.dumps(solution, indent=2))

# Run the solver
solve_puzzle()