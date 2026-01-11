import itertools
import json

def solve_puzzle():
    # Define the attributes
    houses = [1, 2, 3]
    names = ['Eric', 'Arnold', 'Peter']
    smoothies = ['desert', 'watermelon', 'cherry']
    book_genres = ['science fiction', 'romance', 'mystery']

    # Generate all possible permutations for each attribute
    all_permutations = list(itertools.permutations(names)) + \
                       list(itertools.permutations(smoothies)) + \
                       list(itertools.permutations(book_genres))

    # Function to check if a configuration satisfies all constraints
    def is_valid_configuration(config):
        name_config, smoothie_config, book_genre_config = config

        # Constraint 1: The person who likes Cherry smoothies is somewhere to the left of the person who loves mystery books.
        cherry_index = smoothie_config.index('cherry')
        mystery_index = book_genre_config.index('mystery')
        if cherry_index >= mystery_index:
            return False

        # Constraint 2: Arnold is the person who loves mystery books.
        arnold_index = name_config.index('Arnold')
        if book_genre_config[arnold_index] != 'mystery':
            return False

        # Constraint 3: The person who loves science fiction books is not in the first house.
        if book_genre_config[0] == 'science fiction':
            return False

        # Constraint 4: The Desert smoothie lover is directly left of the person who loves mystery books.
        desert_index = smoothie_config.index('desert')
        if desert_index + 1 != mystery_index:
            return False

        # Constraint 5: Peter is in the first house.
        if name_config[0] != 'Peter':
            return False

        return True

    # Try all combinations of permutations
    for name_perm in itertools.permutations(names):
        for smoothie_perm in itertools.permutations(smoothies):
            for book_genre_perm in itertools.permutations(book_genres):
                config = (name_perm, smoothie_perm, book_genre_perm)
                if is_valid_configuration(config):
                    # Format the solution as required
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Smoothie", "BookGenre"],
                            "rows": [
                                [str(houses[i]), name_perm[i], smoothie_perm[i], book_genre_perm[i]]
                                for i in range(len(houses))
                            ]
                        }
                    }
                    return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())