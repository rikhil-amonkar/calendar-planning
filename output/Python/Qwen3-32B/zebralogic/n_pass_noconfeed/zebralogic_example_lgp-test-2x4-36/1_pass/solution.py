import itertools
import json

def solve_puzzle():
    # Define possible values for each category
    names = ['Eric', 'Arnold']
    book_genres = ['science fiction', 'mystery']
    birthdays = ['sept', 'april']
    animals = ['horse', 'cat']

    # Initialize houses with fixed attributes based on clues
    houses = [
        {'House': '1', 'Name': names[0], 'Birthday': birthdays[0]},
        {'House': '2', 'Name': names[1], 'Birthday': birthdays[1]}
    ]

    # Check all permutations for book genres and animals
    for book_perm in itertools.permutations(book_genres):
        # Clue 3: Science fiction is in the second house
        if book_perm[1] != 'science fiction':
            continue

        # Assign book genres
        houses[0]['BookGenre'] = book_perm[0]
        houses[1]['BookGenre'] = book_perm[1]

        for animal_perm in itertools.permutations(animals):
            # Clue 4: Person with horses has September birthday
            valid = True
            for i in range(2):
                if animal_perm[i] == 'horse' and houses[i]['Birthday'] != 'sept':
                    valid = False
                    break
            if not valid:
                continue

            # Assign animals
            houses[0]['Animal'] = animal_perm[0]
            houses[1]['Animal'] = animal_perm[1]

            # Prepare solution data
            solution_data = {
                "solution": {
                    "header": ["House", "Name", "BookGenre", "Birthday", "Animal"],
                    "rows": []
                }
            }

            # Populate rows
            for house in houses:
                row = [
                    house['House'],
                    house['Name'],
                    house['BookGenre'],
                    house['Birthday'],
                    house['Animal']
                ]
                solution_data['solution']['rows'].append(row)

            # Output JSON
            print(json.dumps(solution_data, indent=2))
            return

# Run the solver
solve_puzzle()