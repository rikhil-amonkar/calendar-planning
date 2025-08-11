import json
from itertools import permutations

def solve_puzzle():
    # Define all possible attributes
    houses = ['1', '2']
    names = ['Eric', 'Arnold']
    genres = ['science fiction', 'mystery']
    months = ['april', 'sept']
    animals = ['horse', 'cat']
    
    # Generate all possible permutations for each attribute
    for name_perm in permutations(names):
        for genre_perm in permutations(genres):
            for month_perm in permutations(months):
                for animal_perm in permutations(animals):
                    # Assign attributes to houses
                    solution = {
                        '1': {
                            'Name': name_perm[0],
                            'book genre': genre_perm[0],
                            'birthday month': month_perm[0],
                            'animal': animal_perm[0]
                        },
                        '2': {
                            'Name': name_perm[1],
                            'book genre': genre_perm[1],
                            'birthday month': month_perm[1],
                            'animal': animal_perm[1]
                        }
                    }
                    
                    # Check all constraints
                    # Clue 1: Eric is in the first house.
                    if solution['1']['Name'] != 'Eric':
                        continue
                    
                    # Clue 2: Eric is the person whose birthday is in September.
                    if solution['1']['birthday month'] != 'sept':
                        continue
                    
                    # Clue 3: The person who loves science fiction books is in the second house.
                    if solution['2']['book genre'] != 'science fiction':
                        continue
                    
                    # Clue 4: The person who keeps horses is the person whose birthday is in September.
                    # Find the house where birthday is sept and check animal is horse
                    sept_house = None
                    for house in ['1', '2']:
                        if solution[house]['birthday month'] == 'sept':
                            sept_house = house
                            break
                    if solution[sept_house]['animal'] != 'horse':
                        continue
                    
                    # If all constraints are satisfied, return the solution
                    return solution
    
    return None

def format_solution(solution):
    if not solution:
        return {"solution": {"header": [], "rows": []}}
    
    header = ["House", "Name", "book genre", "birthday month", "animal"]
    rows = []
    for house in ['1', '2']:
        row = [house]
        row.append(solution[house]['Name'])
        row.append(solution[house]['book genre'])
        row.append(solution[house]['birthday month'])
        row.append(solution[house]['animal'])
        rows.append(row)
    
    return {"solution": {"header": header, "rows": rows}}

solution = solve_puzzle()
formatted_solution = format_solution(solution)
print(json.dumps(formatted_solution, indent=2))