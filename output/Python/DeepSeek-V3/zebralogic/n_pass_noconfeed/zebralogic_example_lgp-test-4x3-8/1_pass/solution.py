import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values
    names = ['Eric', 'Arnold', 'Peter', 'Alice']
    hair_colors = ['blonde', 'black', 'brown', 'red']
    music_genres = ['pop', 'jazz', 'rock', 'classical']
    houses = [1, 2, 3, 4]
    
    # Generate all possible permutations for each attribute
    for name_perm in permutations(names):
        for hair_perm in permutations(hair_colors):
            for music_perm in permutations(music_genres):
                # Create assignment for each house
                assignment = []
                for i in range(4):
                    assignment.append({
                        'house': i+1,
                        'name': name_perm[i],
                        'hair': hair_perm[i],
                        'music': music_perm[i]
                    })
                
                # Check all constraints
                valid = True
                
                # Clue 1: Eric is the person who has red hair.
                eric_house = None
                red_hair_house = None
                for house in assignment:
                    if house['name'] == 'Eric':
                        eric_house = house
                    if house['hair'] == 'red':
                        red_hair_house = house
                if eric_house != red_hair_house:
                    valid = False
                
                # Clue 2: The person who loves classical music is directly left of the person who has blonde hair.
                classical_house = None
                blonde_hair_house = None
                for house in assignment:
                    if house['music'] == 'classical':
                        classical_house = house
                    if house['hair'] == 'blonde':
                        blonde_hair_house = house
                if classical_house and blonde_hair_house:
                    if classical_house['house'] + 1 != blonde_hair_house['house']:
                        valid = False
                else:
                    valid = False
                
                # Clue 3: The person who has brown hair is not in the first house.
                for house in assignment:
                    if house['house'] == 1 and house['hair'] == 'brown':
                        valid = False
                
                # Clue 4: The person who loves pop music is not in the third house.
                for house in assignment:
                    if house['house'] == 3 and house['music'] == 'pop':
                        valid = False
                
                # Clue 5: The person who loves classical music is in the first house.
                for house in assignment:
                    if house['house'] == 1 and house['music'] != 'classical':
                        valid = False
                    if house['music'] == 'classical' and house['house'] != 1:
                        valid = False
                
                # Clue 6: The person who loves jazz music is the person who has red hair.
                jazz_house = None
                red_hair_house = None
                for house in assignment:
                    if house['music'] == 'jazz':
                        jazz_house = house
                    if house['hair'] == 'red':
                        red_hair_house = house
                if jazz_house != red_hair_house:
                    valid = False
                
                # Clue 7: The person who loves rock music is Arnold.
                for house in assignment:
                    if house['music'] == 'rock' and house['name'] != 'Arnold':
                        valid = False
                    if house['name'] == 'Arnold' and house['music'] != 'rock':
                        valid = False
                
                # Clue 8: Peter is somewhere to the right of the person who loves rock music.
                peter_house = None
                rock_house = None
                for house in assignment:
                    if house['name'] == 'Peter':
                        peter_house = house
                    if house['music'] == 'rock':
                        rock_house = house
                if peter_house and rock_house:
                    if peter_house['house'] <= rock_house['house']:
                        valid = False
                else:
                    valid = False
                
                if valid:
                    # Format the solution
                    rows = []
                    for house in sorted(assignment, key=lambda x: x['house']):
                        rows.append([
                            str(house['house']),
                            house['name'],
                            house['hair'],
                            house['music']
                        ])
                    
                    return {
                        "solution": {
                            "header": ["House", "Name", "HairColor", "MusicGenre"],
                            "rows": rows
                        }
                    }
    
    return {"solution": {"header": ["House", "Name", "HairColor", "MusicGenre"], "rows": []}}

# Solve the puzzle and output the result
result = solve_puzzle()
print(json.dumps(result, indent=2))