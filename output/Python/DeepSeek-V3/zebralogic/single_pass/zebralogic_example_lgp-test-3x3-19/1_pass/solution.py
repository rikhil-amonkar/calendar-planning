import json
from itertools import permutations

def solve_puzzle():
    # Define the possible values for each attribute
    names = ['Eric', 'Arnold', 'Peter']
    smoothies = ['desert', 'watermelon', 'cherry']
    genres = ['science fiction', 'romance', 'mystery']
    
    # Generate all possible permutations for each attribute
    for name_perm in permutations(names):
        for smoothie_perm in permutations(smoothies):
            for genre_perm in permutations(genres):
                # Assign attributes to houses
                solution = [
                    {'House': '1', 'Name': name_perm[0], 'Smoothie': smoothie_perm[0], 'BookGenre': genre_perm[0]},
                    {'House': '2', 'Name': name_perm[1], 'Smoothie': smoothie_perm[1], 'BookGenre': genre_perm[1]},
                    {'House': '3', 'Name': name_perm[2], 'Smoothie': smoothie_perm[2], 'BookGenre': genre_perm[2]}
                ]
                
                # Check all constraints
                # Clue 5: Peter is in the first house
                if solution[0]['Name'] != 'Peter':
                    continue
                
                # Clue 2: Arnold loves mystery books
                arnold_house = None
                mystery_house = None
                for house in solution:
                    if house['Name'] == 'Arnold':
                        arnold_house = house
                    if house['BookGenre'] == 'mystery':
                        mystery_house = house
                if arnold_house != mystery_house:
                    continue
                
                # Clue 1: Cherry is left of mystery
                cherry_positions = [i for i, h in enumerate(solution) if h['Smoothie'] == 'cherry']
                mystery_position = [i for i, h in enumerate(solution) if h['BookGenre'] == 'mystery'][0]
                if not all(pos < mystery_position for pos in cherry_positions):
                    continue
                
                # Clue 4: Desert is directly left of mystery
                desert_position = None
                for i, house in enumerate(solution):
                    if house['Smoothie'] == 'desert':
                        desert_position = i
                if desert_position is None or desert_position + 1 != mystery_position:
                    continue
                
                # Clue 3: Science fiction is not in the first house
                if solution[0]['BookGenre'] == 'science fiction':
                    continue
                
                # If all constraints are satisfied, format the solution
                formatted_solution = {
                    "solution": {
                        "header": ["House", "Name", "Smoothie", "BookGenre"],
                        "rows": [
                            [house['House'], house['Name'], house['Smoothie'], house['BookGenre']]
                            for house in solution
                        ]
                    }
                }
                return formatted_solution
    
    return {"solution": {"header": [], "rows": []}}

# Solve the puzzle and print the result
print(json.dumps(solve_puzzle(), indent=2))