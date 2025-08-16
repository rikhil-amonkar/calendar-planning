import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Peter", "Arnold", "Eric"]
    book_genres = ["science fiction", "mystery", "romance"]
    smoothies = ["watermelon", "desert", "cherry"]
    birthdays = ["april", "jan", "sept"]
    heights = ["average", "very short", "short"]

    # Generate all possible permutations for each category
    all_permutations = list(itertools.permutations(names)) * \
                       list(itertools.permutations(book_genres)) * \
                       list(itertools.permutations(smoothies)) * \
                       list(itertools.permutations(birthdays)) * \
                       list(itertools.permutations(heights))

    # Define the constraints
    def is_valid_solution(permutation):
        name_perm, book_genre_perm, smoothie_perm, birthday_perm, height_perm = permutation

        # Constraint 1: The person who likes Cherry smoothies is not in the second house.
        if smoothie_perm[1] == "cherry":
            return False

        # Constraint 2: Arnold is the person who loves mystery books.
        if name_perm[book_genre_perm.index("mystery")] != "Arnold":
            return False

        # Constraint 3: The person whose birthday is in January is not in the first house.
        if birthday_perm[0] == "jan":
            return False

        # Constraint 4: The person who is very short is the person who loves romance books.
        if height_perm[book_genre_perm.index("romance")] != "very short":
            return False

        # Constraint 5: The person who loves mystery books is the person whose birthday is in September.
        if birthday_perm[book_genre_perm.index("mystery")] != "sept":
            return False

        # Constraint 6: The person who has an average height is the Desert smoothie lover.
        if height_perm[smoothie_perm.index("desert")] != "average":
            return False

        # Constraint 7: Eric is in the first house.
        if name_perm[0] != "Eric":
            return False

        # Constraint 8: The Watermelon smoothie lover is the person who is short.
        if height_perm[smoothie_perm.index("watermelon")] != "short":
            return False

        # Constraint 9: The Watermelon smoothie lover is Eric.
        if name_perm[smoothie_perm.index("watermelon")] != "Eric":
            return False

        return True

    # Find the valid solution
    for permutation in itertools.product(
        itertools.permutations(names),
        itertools.permutations(book_genres),
        itertools.permutations(smoothies),
        itertools.permutations(birthdays),
        itertools.permutations(heights)
    ):
        if is_valid_solution(permutation):
            name_perm, book_genre_perm, smoothie_perm, birthday_perm, height_perm = permutation
            break

    # Prepare the solution in the required format
    solution = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Smoothie", "Birthday", "Height"],
            "rows": [
                ["1", name_perm[0], book_genre_perm[0], smoothie_perm[0], birthday_perm[0], height_perm[0]],
                ["2", name_perm[1], book_genre_perm[1], smoothie_perm[1], birthday_perm[1], height_perm[1]],
                ["3", name_perm[2], book_genre_perm[2], smoothie_perm[2], birthday_perm[2], height_perm[2]]
            ]
        }
    }

    # Output the solution as JSON
    print(json.dumps(solution, indent=2))

# Run the function to solve the puzzle
solve_puzzle()