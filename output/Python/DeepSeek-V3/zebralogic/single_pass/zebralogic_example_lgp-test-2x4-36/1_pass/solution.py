import json
from itertools import permutations

def solve_puzzle():
    # Define all possible options for each category
    names = ['Eric', 'Arnold']
    genres = ['science fiction', 'mystery']
    months = ['april', 'sept']
    animals = ['horse', 'cat']
    
    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for genre_perm in permutations(genres):
            for month_perm in permutations(months):
                for animal_perm in permutations(animals):
                    # Assign to houses
                    solution = [
                        {
                            'House': '1',
                            'Name': name_perm[0],
                            'BookGenre': genre_perm[0],
                            'Birthday': month_perm[0],
                            'Animal': animal_perm[0]
                        },
                        {
                            'House': '2',
                            'Name': name_perm[1],
                            'BookGenre': genre_perm[1],
                            'Birthday': month_perm[1],
                            'Animal': animal_perm[1]
                        }
                    ]
                    
                    # Check constraints
                    # Constraint 1: Eric is in the first house
                    if solution[0]['Name'] != 'Eric':
                        continue
                    
                    # Constraint 2: Eric's birthday is in September
                    if solution[0]['Name'] == 'Eric' and solution[0]['Birthday'] != 'sept':
                        continue
                    
                    # Constraint 3: Science fiction is in the second house
                    if solution[1]['BookGenre'] != 'science fiction':
                        continue
                    
                    # Constraint 4: Horse is kept by person with September birthday
                    if (solution[0]['Animal'] == 'horse' and solution[0]['Birthday'] != 'sept') or \
                       (solution[1]['Animal'] == 'horse' and solution[1]['Birthday'] != 'sept'):
                        continue
                    if 'horse' not in [solution[0]['Animal'], solution[1]['Animal']]:
                        continue
                    
                    # All constraints satisfied, format the solution
                    result = {
                        "solution": {
                            "header": ["House", "Name", "BookGenre", "Birthday", "Animal"],
                            "rows": [
                                [
                                    solution[0]['House'],
                                    solution[0]['Name'],
                                    solution[0]['BookGenre'],
                                    solution[0]['Birthday'],
                                    solution[0]['Animal']
                                ],
                                [
                                    solution[1]['House'],
                                    solution[1]['Name'],
                                    solution[1]['BookGenre'],
                                    solution[1]['Birthday'],
                                    solution[1]['Animal']
                                ]
                            ]
                        }
                    }
                    return json.dumps(result, indent=2)
    
    return json.dumps({"solution": {"header": [], "rows": []}})

print(solve_puzzle())