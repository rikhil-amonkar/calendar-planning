import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    houses = ['1', '2', '3']
    names = ['Eric', 'Arnold', 'Peter']
    smoothies = ['desert', 'watermelon', 'cherry']
    book_genres = ['science fiction', 'romance', 'mystery']

    # Generate all possible permutations for each category
    permutations = list(itertools.permutations(names)) * \
                   list(itertools.permutations(smoothies)) * \
                   list(itertools.permutations(book_genres))

    # Function to check if a permutation satisfies all the clues
    def is_valid_solution(name_perm, smoothie_perm, book_genre_perm):
        # Unpack the permutations
        eric, arnold, peter = name_perm
        desert, watermelon, cherry = smoothie_perm
        science_fiction, romance, mystery = book_genre_perm

        # Create a list of dictionaries representing each house
        house1 = {'Name': name_perm[0], 'Smoothie': smoothie_perm[0], 'BookGenre': book_genre_perm[0]}
        house2 = {'Name': name_perm[1], 'Smoothie': smoothie_perm[1], 'BookGenre': book_genre_perm[1]}
        house3 = {'Name': name_perm[2], 'Smoothie': smoothie_perm[2], 'BookGenre': book_genre_perm[2]}

        houses_dict = [house1, house2, house3]

        # Check each clue
        # Clue 1: The person who likes Cherry smoothies is somewhere to the left of the person who loves mystery books.
        if houses_dict.index({'Smoothie': 'cherry'}) > houses_dict.index({'BookGenre': 'mystery'}):
            return False

        # Clue 2: Arnold is the person who loves mystery books.
        if not any(house['Name'] == 'Arnold' and house['BookGenre'] == 'mystery' for house in houses_dict):
            return False

        # Clue 3: The person who loves science fiction books is not in the first house.
        if houses_dict[0]['BookGenre'] == 'science fiction':
            return False

        # Clue 4: The Desert smoothie lover is directly left of the person who loves mystery books.
        if houses_dict.index({'Smoothie': 'desert'}) + 1 != houses_dict.index({'BookGenre': 'mystery'}):
            return False

        # Clue 5: Peter is in the first house.
        if houses_dict[0]['Name'] != 'Peter':
            return False

        return True

    # Iterate over all possible combinations of permutations
    for name_perm in itertools.permutations(names):
        for smoothie_perm in itertools.permutations(smoothies):
            for book_genre_perm in itertools.permutations(book_genres):
                if is_valid_solution(name_perm, smoothie_perm, book_genre_perm):
                    # Create the solution in the required format
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Smoothie", "BookGenre"],
                            "rows": [
                                ["1", name_perm[0], smoothie_perm[0], book_genre_perm[0]],
                                ["2", name_perm[1], smoothie_perm[1], book_genre_perm[1]],
                                ["3", name_perm[2], smoothie_perm[2], book_genre_perm[2]]
                            ]
                        }
                    }
                    return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())