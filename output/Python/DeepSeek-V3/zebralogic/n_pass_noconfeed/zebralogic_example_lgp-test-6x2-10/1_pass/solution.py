import json
from itertools import permutations

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Arnold', 'Eric', 'Peter', 'Alice', 'Carol', 'Bob']
    genres = ['jazz', 'pop', 'classical', 'rock', 'hip hop', 'country']
    
    # Generate all possible assignments
    for name_perm in permutations(names):
        for genre_perm in permutations(genres):
            assignment = list(zip(houses, name_perm, genre_perm))
            
            # Check all constraints
            valid = True
            
            # Clue 3: Carol is in the sixth house
            if assignment[5][1] != 'Carol':
                continue
                
            # Clue 5: The person who loves country music is Carol
            if assignment[5][2] != 'country':
                continue
                
            # Clue 9: The person who loves hip-hop music is in the third house
            if assignment[2][2] != 'hip hop':
                continue
                
            # Clue 8: The person who loves pop music is Peter
            peter_house = None
            for house, name, genre in assignment:
                if name == 'Peter':
                    peter_house = house
                if genre == 'pop' and name != 'Peter':
                    valid = False
                    break
            if not valid:
                continue
                
            # Clue 6: Arnold is not in the fifth house
            if assignment[4][1] == 'Arnold':
                continue
                
            # Clue 1: Bob is directly left of the person who loves jazz music
            bob_house = None
            jazz_house = None
            for house, name, genre in assignment:
                if name == 'Bob':
                    bob_house = house
                if genre == 'jazz':
                    jazz_house = house
            if bob_house is None or jazz_house is None or jazz_house != bob_house + 1:
                continue
                
            # Clue 2: Eric is somewhere to the left of the person who loves hip-hop music
            eric_house = None
            hiphop_house = 3  # From clue 9
            for house, name, genre in assignment:
                if name == 'Eric':
                    eric_house = house
            if eric_house is None or eric_house >= hiphop_house:
                continue
                
            # Clue 4: Eric and the person who loves hip-hop music are next to each other
            if abs(eric_house - hiphop_house) != 1:
                continue
                
            # Clue 7: Arnold is somewhere to the right of the person who loves pop music
            arnold_house = None
            pop_house = None
            for house, name, genre in assignment:
                if name == 'Arnold':
                    arnold_house = house
                if genre == 'pop':
                    pop_house = house
            if arnold_house is None or pop_house is None or arnold_house <= pop_house:
                continue
                
            # Clue 10: There is one house between Peter and Bob
            if abs(peter_house - bob_house) != 2:
                continue
                
            # Clue 11: The person who loves rock music is not in the fifth house
            if assignment[4][2] == 'rock':
                continue
                
            # If we reach here, all constraints are satisfied
            result = {
                "solution": {
                    "header": ["House", "Name", "MusicGenre"],
                    "rows": []
                }
            }
            
            for house, name, genre in assignment:
                result["solution"]["rows"].append([str(house), name, genre])
            
            return result
    
    return {"solution": {"header": ["House", "Name", "MusicGenre"], "rows": []}}

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))