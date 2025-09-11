import json

def solve_puzzle():
    # Define the possible values for each category
    houses = ['1', '2']
    names = ['Eric', 'Arnold']
    book_genres = ['science fiction', 'mystery']
    birthdays = ['april', 'sept']
    animals = ['horse', 'cat']

    # Initialize the solution grid
    solution_grid = [
        {'House': '1', 'Name': None, 'BookGenre': None, 'Birthday': None, 'Animal': None},
        {'House': '2', 'Name': None, 'BookGenre': None, 'Birthday': None, 'Animal': None}
    ]

    # Apply the clues
    # Clue 1: Eric is in the first house.
    solution_grid[0]['Name'] = 'Eric'

    # Clue 2: Eric is the person whose birthday is in September.
    solution_grid[0]['Birthday'] = 'sept'

    # Clue 3: The person who loves science fiction books is in the second house.
    solution_grid[1]['BookGenre'] = 'science fiction'

    # Clue 4: The person who keeps horses is the person whose birthday is in September.
    solution_grid[0]['Animal'] = 'horse'

    # Deduce the remaining values
    # Since Eric is in the first house, Arnold must be in the second house
    solution_grid[1]['Name'] = 'Arnold'

    # Since the person in the second house loves science fiction, they cannot love mystery
    solution_grid[1]['BookGenre'] = 'science fiction'
    solution_grid[0]['BookGenre'] = 'mystery'

    # Since the person in the first house has a horse, the person in the second house must have a cat
    solution_grid[1]['Animal'] = 'cat'

    # Since Eric's birthday is in September, Arnold's birthday must be in April
    solution_grid[1]['Birthday'] = 'april'

    # Format the solution as required
    formatted_solution = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Birthday", "Animal"],
            "rows": [
                [solution_grid[0]['House'], solution_grid[0]['Name'], solution_grid[0]['BookGenre'], solution_grid[0]['Birthday'], solution_grid[0]['Animal']],
                [solution_grid[1]['House'], solution_grid[1]['Name'], solution_grid[1]['BookGenre'], solution_grid[1]['Birthday'], solution_grid[1]['Animal']]
            ]
        }
    }

    # Output the solution as JSON
    print(json.dumps(formatted_solution, indent=2))

if __name__ == "__main__":
    solve_puzzle()