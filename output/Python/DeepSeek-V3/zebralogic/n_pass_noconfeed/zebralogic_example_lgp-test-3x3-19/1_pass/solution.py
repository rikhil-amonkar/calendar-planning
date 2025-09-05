import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values
    names = ['Eric', 'Arnold', 'Peter']
    smoothies = ['desert', 'watermelon', 'cherry']
    book_genres = ['science fiction', 'romance', 'mystery']
    houses = [1, 2, 3]
    
    # Generate all possible permutations
    for name_perm in permutations(names):
        for smoothie_perm in permutations(smoothies):
            for book_perm in permutations(book_genres):
                # Create assignment for each house
                assignment = []
                for i in range(3):
                    assignment.append({
                        'house': houses[i],
                        'name': name_perm[i],
                        'smoothie': smoothie_perm[i],
                        'book': book_perm[i]
                    })
                
                # Check all constraints
                valid = True
                
                # Clue 2: Arnold loves mystery books
                arnold_house = None
                mystery_book_house = None
                for house in assignment:
                    if house['name'] == 'Arnold':
                        arnold_house = house['house']
                    if house['book'] == 'mystery':
                        mystery_book_house = house['house']
                if arnold_house != mystery_book_house:
                    valid = False
                
                # Clue 1: Cherry smoothie left of mystery books
                cherry_smoothie_house = None
                for house in assignment:
                    if house['smoothie'] == 'cherry':
                        cherry_smoothie_house = house['house']
                if cherry_smoothie_house is not None and mystery_book_house is not None:
                    if cherry_smoothie_house >= mystery_book_house:
                        valid = False
                
                # Clue 3: Science fiction not in first house
                if assignment[0]['book'] == 'science fiction':
                    valid = False
                
                # Clue 4: Desert smoothie directly left of mystery books
                desert_smoothie_house = None
                for house in assignment:
                    if house['smoothie'] == 'desert':
                        desert_smoothie_house = house['house']
                if desert_smoothie_house is not None and mystery_book_house is not None:
                    if desert_smoothie_house + 1 != mystery_book_house:
                        valid = False
                
                # Clue 5: Peter in first house
                if assignment[0]['name'] != 'Peter':
                    valid = False
                
                if valid:
                    # Format the solution
                    rows = []
                    for house in sorted(assignment, key=lambda x: x['house']):
                        rows.append([
                            str(house['house']),
                            house['name'],
                            house['smoothie'],
                            house['book']
                        ])
                    
                    return {
                        "solution": {
                            "header": ["House", "Name", "Smoothie", "BookGenre"],
                            "rows": rows
                        }
                    }
    
    return {"solution": {"header": ["House", "Name", "Smoothie", "BookGenre"], "rows": []}}

# Solve and output the puzzle
result = solve_puzzle()
print(json.dumps(result, indent=2))