import json
from itertools import permutations

def solve_puzzle():
    # Define all possible options
    names = ['Eric', 'Arnold', 'Peter', 'Alice']
    hair_colors = ['blonde', 'black', 'brown', 'red']
    music_genres = ['pop', 'jazz', 'rock', 'classical']
    houses = ['1', '2', '3', '4']
    
    # Generate all possible permutations for each attribute
    for name_perm in permutations(names):
        for hair_perm in permutations(hair_colors):
            for music_perm in permutations(music_genres):
                # Assign to houses
                assignment = []
                for i in range(4):
                    assignment.append({
                        'House': str(i+1),
                        'Name': name_perm[i],
                        'HairColor': hair_perm[i],
                        'MusicGenre': music_perm[i]
                    })
                
                # Check all constraints
                valid = True
                
                # Constraint 1: Eric has red hair
                eric_house = None
                for house in assignment:
                    if house['Name'] == 'Eric':
                        eric_house = house
                        break
                if not eric_house or eric_house['HairColor'] != 'red':
                    valid = False
                    continue
                
                # Constraint 2: classical is directly left of blonde
                classical_pos = None
                blonde_pos = None
                for i, house in enumerate(assignment):
                    if house['MusicGenre'] == 'classical':
                        classical_pos = i
                    if house['HairColor'] == 'blonde':
                        blonde_pos = i
                if classical_pos is None or blonde_pos is None or classical_pos + 1 != blonde_pos:
                    valid = False
                    continue
                
                # Constraint 3: brown hair not in first house
                if assignment[0]['HairColor'] == 'brown':
                    valid = False
                    continue
                
                # Constraint 4: pop not in third house
                if assignment[2]['MusicGenre'] == 'pop':
                    valid = False
                    continue
                
                # Constraint 5: classical in first house
                if assignment[0]['MusicGenre'] != 'classical':
                    valid = False
                    continue
                
                # Constraint 6: jazz is red hair (which is Eric)
                for house in assignment:
                    if house['MusicGenre'] == 'jazz' and house['Name'] != 'Eric':
                        valid = False
                        break
                if not valid:
                    continue
                
                # Constraint 7: rock is Arnold
                arnold_house = None
                for house in assignment:
                    if house['Name'] == 'Arnold':
                        arnold_house = house
                        break
                if not arnold_house or arnold_house['MusicGenre'] != 'rock':
                    valid = False
                    continue
                
                # Constraint 8: Peter is right of rock (Arnold)
                arnold_pos = None
                peter_pos = None
                for i, house in enumerate(assignment):
                    if house['Name'] == 'Arnold':
                        arnold_pos = i
                    if house['Name'] == 'Peter':
                        peter_pos = i
                if peter_pos <= arnold_pos:
                    valid = False
                    continue
                
                if valid:
                    # Prepare the solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "HairColor", "MusicGenre"],
                            "rows": []
                        }
                    }
                    for house in assignment:
                        solution["solution"]["rows"].append([
                            house['House'],
                            house['Name'],
                            house['HairColor'],
                            house['MusicGenre']
                        ])
                    return solution
    
    return {"solution": {"header": [], "rows": []}}

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))