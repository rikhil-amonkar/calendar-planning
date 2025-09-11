import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Arnold", "Eric", "Peter"]
    music_genres = ["pop", "rock", "classical"]
    children = ["Fred", "Meredith", "Bella"]
    book_genres = ["mystery", "romance", "science fiction"]

    # Generate all possible permutations for each category
    all_permutations = list(itertools.permutations(names)) * \
                       list(itertools.permutations(music_genres)) * \
                       list(itertools.permutations(children)) * \
                       list(itertools.permutations(book_genres))

    # Check each permutation against the clues
    for names_perm, music_perm, children_perm, book_perm in itertools.product(
            itertools.permutations(names),
            itertools.permutations(music_genres),
            itertools.permutations(children),
            itertools.permutations(book_genres)
    ):
        # Unpack the permutations for easier reference
        name1, name2, name3 = names_perm
        music1, music2, music3 = music_perm
        child1, child2, child3 = children_perm
        book1, book2, book3 = book_perm

        # Apply the clues
        if (
            # Clue 1: The person's child is named Fred is directly left of the person who loves mystery books.
            ((child1 == "Fred" and book2 == "mystery") or
             (child2 == "Fred" and book3 == "mystery")) and
            # Clue 2: Peter is in the first house.
            name1 == "Peter" and
            # Clue 3: The person who loves mystery books is the person who loves classical music.
            ((book1 == "mystery" and music1 == "classical") or
             (book2 == "mystery" and music2 == "classical") or
             (book3 == "mystery" and music3 == "classical")) and
            # Clue 4: The person who loves science fiction books is the person's child is named Meredith.
            ((book1 == "science fiction" and child1 == "Meredith") or
             (book2 == "science fiction" and child2 == "Meredith") or
             (book3 == "science fiction" and child3 == "Meredith")) and
            # Clue 5: Eric is the person who loves mystery books.
            ((name1 == "Eric" and book1 == "mystery") or
             (name2 == "Eric" and book2 == "mystery") or
             (name3 == "Eric" and book3 == "mystery")) and
            # Clue 6: The person who loves rock music is somewhere to the right of the person who loves romance books.
            ((music1 == "romance" and (music2 == "rock" or music3 == "rock")) or
             (music2 == "romance" and music3 == "rock"))
        ):
            # If all clues are satisfied, construct the solution
            solution = {
                "solution": {
                    "header": ["House", "Name", "MusicGenre", "Children", "BookGenre"],
                    "rows": [
                        ["1", name1, music1, child1, book1],
                        ["2", name2, music2, child2, book2],
                        ["3", name3, music3, child3, book3]
                    ]
                }
            }
            return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())