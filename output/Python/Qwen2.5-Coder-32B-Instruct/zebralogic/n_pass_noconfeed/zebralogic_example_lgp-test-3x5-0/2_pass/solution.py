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
    name_perms = list(itertools.permutations(names))
    book_genre_perms = list(itertools.permutations(book_genres))
    smoothie_perms = list(itertools.permutations(smoothies))
    birthday_perms = list(itertools.permutations(birthdays))
    height_perms = list(itertools.permutations(heights))

    # Generate the Cartesian product of all permutations
    all_combinations = itertools.product(name_perms, book_genre_perms, smoothie_perms, birthday_perms, height_perms)

    # Define the constraints
    def is_valid_solution(solution):
        # Unpack the solution
        names_sol, book_genres_sol, smoothies_sol, birthdays_sol, heights_sol = solution

        # Constraint 1: The person who likes Cherry smoothies is not in the second house.
        if smoothies_sol[1] == "cherry":
            return False

        # Constraint 2: Arnold is the person who loves mystery books.
        if names_sol[book_genres_sol.index("mystery")] != "Arnold":
            return False

        # Constraint 3: The person whose birthday is in January is not in the first house.
        if birthdays_sol[0] == "jan":
            return False

        # Constraint 4: The person who is very short is the person who loves romance books.
        if heights_sol[book_genres_sol.index("romance")] != "very short":
            return False

        # Constraint 5: The person who loves mystery books is the person whose birthday is in September.
        if birthdays_sol[book_genres_sol.index("mystery")] != "sept":
            return False

        # Constraint 6: The person who has an average height is the Desert smoothie lover.
        if heights_sol[smoothies_sol.index("desert")] != "average":
            return False

        # Constraint 7: Eric is in the first house.
        if names_sol[0] != "Eric":
            return False

        # Constraint 8: The Watermelon smoothie lover is the person who is short.
        if heights_sol[smoothies_sol.index("watermelon")] != "short":
            return False

        # Constraint 9: The Watermelon smoothie lover is Eric.
        if smoothies_sol[names_sol.index("Eric")] != "watermelon":
            return False

        return True

    # Find the valid solution
    for comb in all_combinations:
        if is_valid_solution(comb):
            names_sol, book_genres_sol, smoothies_sol, birthdays_sol, heights_sol = comb
            break

    # Prepare the solution in the required format
    solution = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Smoothie", "Birthday", "Height"],
            "rows": [
                ["1", names_sol[0], book_genres_sol[0], smoothies_sol[0], birthdays_sol[0], heights_sol[0]],
                ["2", names_sol[1], book_genres_sol[1], smoothies_sol[1], birthdays_sol[1], heights_sol[1]],
                ["3", names_sol[2], book_genres_sol[2], smoothies_sol[2], birthdays_sol[2], heights_sol[2]]
            ]
        }
    }

    # Output the solution as JSON
    print(json.dumps(solution, indent=2))

if __name__ == "__main__":
    solve_puzzle()