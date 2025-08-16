import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Eric", "Arnold"]
    book_genres = ["science fiction", "mystery"]
    birthdays = ["april", "sept"]
    animals = ["horse", "cat"]

    # Generate all possible permutations for the two houses
    all_permutations = list(itertools.permutations(names)) * \
                       list(itertools.permutations(book_genres)) * \
                       list(itertools.permutations(birthdays)) * \
                       list(itertools.permutations(animals))

    # Check each permutation against the clues
    for names_perm, book_genres_perm, birthdays_perm, animals_perm in itertools.product(
        itertools.permutations(names),
        itertools.permutations(book_genres),
        itertools.permutations(birthdays),
        itertools.permutations(animals)
    ):
        # Unpack the permutations
        name_house1, name_house2 = names_perm
        book_genre_house1, book_genre_house2 = book_genres_perm
        birthday_house1, birthday_house2 = birthdays_perm
        animal_house1, animal_house2 = animals_perm

        # Apply the clues
        if (name_house1 == "Eric" and
            birthday_house1 == "sept" and
            book_genre_house2 == "science fiction" and
            birthday_house1 == "sept" == birthdays[1] and
            animal_house1 == "horse"):
            # If all clues are satisfied, construct the solution
            solution = {
                "solution": {
                    "header": ["House", "Name", "BookGenre", "Birthday", "Animal"],
                    "rows": [
                        ["1", name_house1, book_genre_house1, birthday_house1, animal_house1],
                        ["2", name_house2, book_genre_house2, birthday_house2, animal_house2]
                    ]
                }
            }
            return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())