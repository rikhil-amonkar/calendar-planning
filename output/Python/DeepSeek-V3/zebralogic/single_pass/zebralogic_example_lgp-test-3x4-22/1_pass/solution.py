import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and their options
    categories = {
        'House': ['1', '2', '3'],
        'Name': ['Arnold', 'Eric', 'Peter'],
        'Music': ['pop', 'rock', 'classical'],
        'Child': ['Fred', 'Meredith', 'Bella'],
        'Book': ['mystery', 'romance', 'science fiction']
    }
    
    # Generate all possible permutations for each category
    for names in permutations(categories['Name']):
        if names[0] != 'Peter':  # Clue 2: Peter is in the first house
            continue
        
        for music in permutations(categories['Music']):
            for child in permutations(categories['Child']):
                for book in permutations(categories['Book']):
                    # Create a list of houses with their attributes
                    houses = [
                        {'House': '1', 'Name': names[0], 'Music': music[0], 'Child': child[0], 'Book': book[0]},
                        {'House': '2', 'Name': names[1], 'Music': music[1], 'Child': child[1], 'Book': book[1]},
                        {'House': '3', 'Name': names[2], 'Music': music[2], 'Child': child[2], 'Book': book[2]}
                    ]
                    
                    # Check all clues
                    valid = True
                    
                    # Clue 1: The person's child is named Fred is directly left of the person who loves mystery books.
                    fred_pos = None
                    mystery_pos = None
                    for i, house in enumerate(houses):
                        if house['Child'] == 'Fred':
                            fred_pos = i
                        if house['Book'] == 'mystery':
                            mystery_pos = i
                    if not (fred_pos is not None and mystery_pos is not None and fred_pos + 1 == mystery_pos):
                        valid = False
                    
                    # Clue 3: The person who loves mystery books is the person who loves classical music.
                    if valid:
                        for house in houses:
                            if house['Book'] == 'mystery' and house['Music'] != 'classical':
                                valid = False
                                break
                    
                    # Clue 4: The person who loves science fiction books is the person's child is named Meredith.
                    if valid:
                        for house in houses:
                            if house['Book'] == 'science fiction' and house['Child'] != 'Meredith':
                                valid = False
                                break
                    
                    # Clue 5: Eric is the person who loves mystery books.
                    if valid:
                        for house in houses:
                            if house['Book'] == 'mystery' and house['Name'] != 'Eric':
                                valid = False
                                break
                    
                    # Clue 6: The person who loves rock music is somewhere to the right of the person who loves romance books.
                    if valid:
                        rock_pos = None
                        romance_pos = None
                        for i, house in enumerate(houses):
                            if house['Music'] == 'rock':
                                rock_pos = i
                            if house['Book'] == 'romance':
                                romance_pos = i
                        if not (rock_pos is not None and romance_pos is not None and rock_pos > romance_pos):
                            valid = False
                    
                    if valid:
                        # Prepare the solution in the required format
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Music", "Child", "Book"],
                                "rows": [
                                    [house['House'], house['Name'], house['Music'], house['Child'], house['Book']] for house in houses
                                ]
                            }
                        }
                        return json.dumps(solution, indent=2)
    
    return json.dumps({"solution": {}})

print(solve_puzzle())