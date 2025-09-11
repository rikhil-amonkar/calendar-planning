import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    houses = ['1', '2', '3']
    names = ['Eric', 'Arnold', 'Peter']
    smoothies = ['desert', 'watermelon', 'cherry']
    book_genres = ['science fiction', 'romance', 'mystery']

    # Iterate over all possible combinations of permutations
    for names_perm, smoothies_perm, book_genres_perm in itertools.product(
            itertools.permutations(names),
            itertools.permutations(smoothies),
            itertools.permutations(book_genres)
    ):
        # Create a dictionary to map house numbers to attributes
        house_map = {
            '1': {'Name': names_perm[0], 'Smoothie': smoothies_perm[0], 'BookGenre': book_genres_perm[0]},
            '2': {'Name': names_perm[1], 'Smoothie': smoothies_perm[1], 'BookGenre': book_genres_perm[1]},
            '3': {'Name': names_perm[2], 'Smoothie': smoothies_perm[2], 'BookGenre': book_genres_perm[2]}
        }

        # Check the clues
        if (house_map['1']['Name'] == 'Peter' and
            house_map['1']['Smoothie'] == 'desert' and
            house_map['2']['BookGenre'] == 'mystery' and
            house_map['2']['Name'] == 'Arnold' and
            house_map['3']['BookGenre'] != 'science fiction' and
            house_map[houses[smoothies_perm.index('cherry')]]['BookGenre'] == 'mystery' and
            smoothies_perm.index('desert') + 1 == smoothies_perm.index('cherry')):
            # If all clues are satisfied, format the solution
            solution = {
                "solution": {
                    "header": ["House", "Name", "Smoothie", "BookGenre"],
                    "rows": [
                        [house, house_map[house]['Name'], house_map[house]['Smoothie'], house_map[house]['BookGenre']]
                        for house in houses
                    ]
                }
            }
            print(json.dumps(solution, indent=2))
            return

# Run the function to solve the puzzle
solve_puzzle()