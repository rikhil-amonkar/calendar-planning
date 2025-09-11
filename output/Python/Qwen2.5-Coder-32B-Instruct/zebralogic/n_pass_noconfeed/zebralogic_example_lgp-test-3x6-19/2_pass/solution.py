import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    houses = ['1', '2', '3']
    names = ['Arnold', 'Eric', 'Peter']
    cigars = ['pall mall', 'blue master', 'prince']
    animals = ['horse', 'cat', 'bird']
    children = ['Bella', 'Fred', 'Meredith']
    book_genres = ['science fiction', 'romance', 'mystery']
    phone_models = ['google pixel 6', 'iphone 13', 'samsung galaxy s21']

    # Generate all possible permutations for each category
    for names_perm in itertools.permutations(names):
        for cigars_perm in itertools.permutations(cigars):
            for animals_perm in itertools.permutations(animals):
                for children_perm in itertools.permutations(children):
                    for book_genres_perm in itertools.permutations(book_genres):
                        for phone_models_perm in itertools.permutations(phone_models):
                            # Create a dictionary to store the current permutation
                            current_solution = {
                                house: {
                                    "Name": name,
                                    "Cigar": cigar,
                                    "Animal": animal,
                                    "Children": child,
                                    "BookGenre": book_genre,
                                    "PhoneModel": phone_model
                                }
                                for house, name, cigar, animal, child, book_genre, phone_model in zip(
                                    houses, names_perm, cigars_perm, animals_perm, children_perm, book_genres_perm, phone_models_perm
                                )
                            }

                            # Check the clues
                            if (current_solution['1']['Children'] == 'Fred' and current_solution['1']['BookGenre'] == 'mystery' and
                                current_solution['2']['Animal'] == 'cat' and current_solution['2']['Name'] == 'Eric' and
                                current_solution['2']['Cigar'] == 'pall mall' and
                                current_solution['3']['Children'] == 'Meredith' and current_solution['3']['Animal'] == 'horse' and
                                current_solution['1']['Cigar'] == 'prince' and current_solution['1']['Children'] == 'Bella' and
                                current_solution['2']['PhoneModel'] == 'iphone 13' and current_solution['3']['PhoneModel'] == 'samsung galaxy s21' and
                                names_perm.index('Peter') < names_perm.index('Eric') and
                                current_solution['3']['BookGenre'] == 'science fiction' and
                                current_solution['2']['BookGenre'] != 'mystery'):
                                # If all clues are satisfied, format the solution
                                rows = [
                                    [house, current_solution[house]['Name'], current_solution[house]['Cigar'],
                                     current_solution[house]['Animal'], current_solution[house]['Children'],
                                     current_solution[house]['BookGenre'], current_solution[house]['PhoneModel']]
                                    for house in houses
                                ]

                                solution = {
                                    "solution": {
                                        "header": ["House", "Name", "Cigar", "Animal", "Children", "BookGenre", "PhoneModel"],
                                        "rows": rows
                                    }
                                }

                                # Output the solution as JSON
                                print(json.dumps(solution, indent=2))
                                return

# Run the solver
solve_puzzle()