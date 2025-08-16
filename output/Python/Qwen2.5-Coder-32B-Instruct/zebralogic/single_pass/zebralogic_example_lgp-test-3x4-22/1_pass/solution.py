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

    # Iterate over all possible combinations
    for names_perm, music_perm, children_perm, book_perm in itertools.product(
            itertools.permutations(names),
            itertools.permutations(music_genres),
            itertools.permutations(children),
            itertools.permutations(book_genres)
    ):
        # Unpack the permutations
        name1, name2, name3 = names_perm
        music1, music2, music3 = music_perm
        child1, child2, child3 = children_perm
        book1, book2, book3 = book_perm

        # Apply the clues
        if (child1 == "Fred" and book2 == "mystery" and
            name2 == "Eric" and book2 == "mystery" and music2 == "classical" and
            child3 == "Meredith" and book3 == "science fiction" and
            name1 == "Peter" and
            (music2 == "rock" and (music1 == "romance" or music3 == "romance"))):
            # If all conditions are satisfied, construct the solution
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
            return json.dumps(solution)

# Print the solution
print(solve_puzzle())