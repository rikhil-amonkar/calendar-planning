import json
from itertools import permutations

def solve_puzzle():
    houses = [1, 2, 3]
    names = ['Eric', 'Arnold', 'Peter']
    book_genres = ['mystery', 'science fiction', 'romance']
    vacations = ['mountain', 'beach', 'city']
    
    # Generate all possible permutations for each attribute
    for name_perm in permutations(names):
        for book_perm in permutations(book_genres):
            for vac_perm in permutations(vacations):
                # Create assignment for each house
                assignment = []
                for i in range(3):
                    assignment.append({
                        'house': houses[i],
                        'name': name_perm[i],
                        'book_genre': book_perm[i],
                        'vacation': vac_perm[i]
                    })
                
                # Check clue 1: Eric is directly left of Arnold
                eric_pos = None
                arnold_pos = None
                for house in assignment:
                    if house['name'] == 'Eric':
                        eric_pos = house['house']
                    if house['name'] == 'Arnold':
                        arnold_pos = house['house']
                if eric_pos is None or arnold_pos is None or eric_pos + 1 != arnold_pos:
                    continue
                
                # Check clue 2: Peter is somewhere to the right of the person who loves beach vacations
                beach_vac_pos = None
                peter_pos = None
                for house in assignment:
                    if house['vacation'] == 'beach':
                        beach_vac_pos = house['house']
                    if house['name'] == 'Peter':
                        peter_pos = house['house']
                if beach_vac_pos is None or peter_pos is None or peter_pos <= beach_vac_pos:
                    continue
                
                # Check clue 3: Peter is the person who prefers city breaks
                peter_city_check = False
                for house in assignment:
                    if house['name'] == 'Peter' and house['vacation'] == 'city':
                        peter_city_check = True
                        break
                if not peter_city_check:
                    continue
                
                # Check clue 4: The person who loves mystery books is somewhere to the left of the person who loves beach vacations
                mystery_book_pos = None
                beach_vac_pos = None
                for house in assignment:
                    if house['book_genre'] == 'mystery':
                        mystery_book_pos = house['house']
                    if house['vacation'] == 'beach':
                        beach_vac_pos = house['house']
                if mystery_book_pos is None or beach_vac_pos is None or mystery_book_pos >= beach_vac_pos:
                    continue
                
                # Check clue 5: The person who loves science fiction books is the person who loves beach vacations
                sci_fi_beach_check = False
                for house in assignment:
                    if house['book_genre'] == 'science fiction' and house['vacation'] == 'beach':
                        sci_fi_beach_check = True
                        break
                if not sci_fi_beach_check:
                    continue
                
                # If all clues are satisfied, return the solution
                solution = {
                    "solution": {
                        "header": ["House", "Name", "BookGenre", "Vacation"],
                        "rows": []
                    }
                }
                
                for house in sorted(assignment, key=lambda x: x['house']):
                    solution["solution"]["rows"].append([
                        str(house['house']),
                        house['name'],
                        house['book_genre'],
                        house['vacation']
                    ])
                
                return solution
    
    return None

def main():
    solution = solve_puzzle()
    if solution:
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"solution": {"header": [], "rows": []}}, indent=2))

if __name__ == "__main__":
    main()