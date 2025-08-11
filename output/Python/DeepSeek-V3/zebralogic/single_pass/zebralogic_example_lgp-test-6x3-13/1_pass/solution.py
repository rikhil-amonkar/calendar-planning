import json
from itertools import permutations

def solve_puzzle():
    # Define all possible options for each attribute
    names = ['Bob', 'Arnold', 'Carol', 'Alice', 'Peter', 'Eric']
    genres = ['romance', 'historical fiction', 'biography', 'mystery', 'fantasy', 'science fiction']
    occupations = ['artist', 'doctor', 'nurse', 'engineer', 'teacher', 'lawyer']
    houses = [1, 2, 3, 4, 5, 6]
    
    # We'll represent each house as a dictionary with attributes
    solution = None
    
    # Generate all possible permutations for names, genres, and occupations across 6 houses
    # This is computationally expensive, but for 6 houses it's manageable
    # We'll use a more efficient approach by applying constraints early
    
    # Let's iterate through all possible assignments step by step
    
    # Pre-allocate house structures
    houses_data = [{'house': i, 'name': None, 'genre': None, 'occupation': None} for i in houses]
    
    # Apply clue 10: doctor is in house 1
    houses_data[0]['occupation'] = 'doctor'
    
    # Apply clue 12: Eric is in house 3
    houses_data[2]['name'] = 'Eric'
    
    # Apply clue 1: Alice loves fantasy
    # Apply clue 4: lawyer loves fantasy, so Alice is lawyer
    # So Alice's occupation is lawyer and genre is fantasy
    
    # Apply clue 7: nurse is directly left of Alice
    # So Alice cannot be in house 1, and nurse is in house (Alice's house - 1)
    
    # Apply clue 3: Carol loves mystery
    # Apply clue 2: mystery lover (Carol) and Bob are next to each other
    # Apply clue 13: mystery (Carol) is not in house 5
    
    # Apply clue 5: Bob is not in house 5
    
    # Apply clue 6: Arnold is left of engineer
    
    # Apply clue 8: biography lover is teacher
    # Apply clue 9: historical fiction is left of teacher
    
    # Apply clue 11: science fiction lover is artist
    
    # Let's try to assign Alice first
    possible_alice_houses = [2, 3, 4, 5, 6]  # can't be 1 because nurse must be to her left
    
    for alice_house in possible_alice_houses:
        # Make a copy of the current state
        current_houses = [house.copy() for house in houses_data]
        
        # Assign Alice
        current_houses[alice_house-1]['name'] = 'Alice'
        current_houses[alice_house-1]['genre'] = 'fantasy'
        current_houses[alice_house-1]['occupation'] = 'lawyer'
        
        # Assign nurse to left of Alice
        nurse_house = alice_house - 1
        if nurse_house < 1:
            continue  # invalid
        current_houses[nurse_house-1]['occupation'] = 'nurse'
        
        # Now assign Carol (mystery lover)
        possible_carol_houses = [h for h in houses if h != alice_house and h != 5 and current_houses[h-1]['name'] is None]
        
        for carol_house in possible_carol_houses:
            current_houses_carol = [house.copy() for house in current_houses]
            
            # Assign Carol
            current_houses_carol[carol_house-1]['name'] = 'Carol'
            current_houses_carol[carol_house-1]['genre'] = 'mystery'
            
            # Bob must be next to Carol
            bob_possible_houses = []
            if carol_house > 1:
                bob_possible_houses.append(carol_house - 1)
            if carol_house < 6:
                bob_possible_houses.append(carol_house + 1)
            bob_possible_houses = [h for h in bob_possible_houses if h != 5 and current_houses_carol[h-1]['name'] is None]
            
            for bob_house in bob_possible_houses:
                current_houses_bob = [house.copy() for house in current_houses_carol]
                
                # Assign Bob
                current_houses_bob[bob_house-1]['name'] = 'Bob'
                
                # Now assign Arnold left of engineer
                # First find possible engineer positions
                remaining_names = [n for n in names if n not in ['Alice', 'Carol', 'Bob', 'Eric'] and n not in [h['name'] for h in current_houses_bob if h['name'] is not None]]
                
                # Assign Eric if not already assigned (clue 12 already handled)
                
                # Now assign remaining names: Arnold, Peter
                # Arnold must be left of engineer
                
                # Find possible engineer houses (occupation not assigned yet)
                possible_engineer_houses = [h['house'] for h in current_houses_bob if h['occupation'] is None and h['house'] > 1]  # engineer can't be in house 1 (doctor)
                
                for engineer_house in possible_engineer_houses:
                    current_houses_eng = [house.copy() for house in current_houses_bob]
                    current_houses_eng[engineer_house-1]['occupation'] = 'engineer'
                    
                    # Arnold must be left of engineer
                    possible_arnold_houses = [h for h in range(1, engineer_house) if current_houses_eng[h-1]['name'] is None]
                    
                    for arnold_house in possible_arnold_houses:
                        current_houses_arnold = [house.copy() for house in current_houses_eng]
                        current_houses_arnold[arnold_house-1]['name'] = 'Arnold'
                        
                        # Assign remaining name (Peter)
                        remaining_name = [n for n in names if n not in [h['name'] for h in current_houses_arnold if h['name'] is not None]][0]
                        remaining_name_house = [h['house'] for h in current_houses_arnold if h['name'] is None][0]
                        current_houses_arnold[remaining_name_house-1]['name'] = remaining_name
                        
                        # Now assign genres
                        assigned_genres = [h['genre'] for h in current_houses_arnold if h['genre'] is not None]
                        remaining_genres = [g for g in genres if g not in assigned_genres]
                        
                        # Assign biography to teacher (clue 8)
                        # Assign historical fiction left of teacher (clue 9)
                        # Assign science fiction to artist (clue 11)
                        
                        # Find teacher houses (occupation not assigned yet)
                        possible_teacher_houses = [h['house'] for h in current_houses_arnold if h['occupation'] is None]
                        
                        for teacher_house in possible_teacher_houses:
                            current_houses_teacher = [house.copy() for house in current_houses_arnold]
                            current_houses_teacher[teacher_house-1]['occupation'] = 'teacher'
                            current_houses_teacher[teacher_house-1]['genre'] = 'biography'
                            
                            # Historical fiction must be left of teacher
                            possible_histfic_houses = [h for h in range(1, teacher_house) if current_houses_teacher[h-1]['genre'] is None]
                            
                            for histfic_house in possible_histfic_houses:
                                current_houses_histfic = [house.copy() for house in current_houses_teacher]
                                current_houses_histfic[histfic_house-1]['genre'] = 'historical fiction'
                                
                                # Assign remaining genres
                                remaining_genres_now = [g for g in genres if g not in ['fantasy', 'mystery', 'biography', 'historical fiction'] and g not in [h['genre'] for h in current_houses_histfic if h['genre'] is not None]]
                                
                                # Assign science fiction to artist (clue 11)
                                possible_artist_houses = [h['house'] for h in current_houses_histfic if h['occupation'] is None]
                                
                                for artist_house in possible_artist_houses:
                                    current_houses_artist = [house.copy() for house in current_houses_histfic]
                                    current_houses_artist[artist_house-1]['occupation'] = 'artist'
                                    current_houses_artist[artist_house-1]['genre'] = 'science fiction'
                                    
                                    # Assign last remaining genre (romance) to last remaining house
                                    remaining_genre = [g for g in genres if g not in [h['genre'] for h in current_houses_artist if h['genre'] is not None]][0]
                                    remaining_house = [h for h in current_houses_artist if h['genre'] is None][0]
                                    remaining_house['genre'] = remaining_genre
                                    
                                    # Assign last remaining occupation
                                    remaining_occupation = [o for o in occupations if o not in [h['occupation'] for h in current_houses_artist if h['occupation'] is not None][0]
                                    remaining_house_occ = [h for h in current_houses_artist if h['occupation'] is None][0]
                                    remaining_house_occ['occupation'] = remaining_occupation
                                    
                                    # Verify all constraints are satisfied
                                    valid = True
                                    
                                    # Check all names are assigned
                                    if any(h['name'] is None for h in current_houses_artist):
                                        valid = False
                                    
                                    # Check all genres are assigned
                                    if any(h['genre'] is None for h in current_houses_artist):
                                        valid = False
                                    
                                    # Check all occupations are assigned
                                    if any(h['occupation'] is None for h in current_houses_artist):
                                        valid = False
                                    
                                    # Check clue 2: Carol (mystery) and Bob are next to each other
                                    carol_pos = [h['house'] for h in current_houses_artist if h['name'] == 'Carol'][0]
                                    bob_pos = [h['house'] for h in current_houses_artist if h['name'] == 'Bob'][0]
                                    if abs(carol_pos - bob_pos) != 1:
                                        valid = False
                                    
                                    # Check clue 5: Bob not in house 5
                                    if bob_pos == 5:
                                        valid = False
                                    
                                    # Check clue 6: Arnold left of engineer
                                    arnold_pos = [h['house'] for h in current_houses_artist if h['name'] == 'Arnold'][0]
                                    engineer_pos = [h['house'] for h in current_houses_artist if h['occupation'] == 'engineer'][0]
                                    if arnold_pos >= engineer_pos:
                                        valid = False
                                    
                                    # Check clue 7: nurse directly left of Alice
                                    nurse_pos = [h['house'] for h in current_houses_artist if h['occupation'] == 'nurse'][0]
                                    alice_pos = [h['house'] for h in current_houses_artist if h['name'] == 'Alice'][0]
                                    if nurse_pos != alice_pos - 1:
                                        valid = False
                                    
                                    # Check clue 9: historical fiction left of teacher
                                    histfic_pos = [h['house'] for h in current_houses_artist if h['genre'] == 'historical fiction'][0]
                                    teacher_pos = [h['house'] for h in current_houses_artist if h['occupation'] == 'teacher'][0]
                                    if histfic_pos >= teacher_pos:
                                        valid = False
                                    
                                    if valid:
                                        solution = current_houses_artist
                                        break
                                    
                                if solution:
                                    break
                            if solution:
                                break
                        if solution:
                            break
                    if solution:
                        break
                if solution:
                    break
            if solution:
                break
        if solution:
            break
    
    # Format the solution
    if solution:
        solution_sorted = sorted(solution, key=lambda x: x['house'])
        result = {
            "solution": {
                "header": ["House", "Name", "genre", "occupation"],
                "rows": [
                    [str(h['house']), h['name'], h['genre'], h['occupation']] for h in solution_sorted
                ]
            }
        }
        return json.dumps(result, indent=2)
    else:
        return json.dumps({"error": "No solution found"}, indent=2)

print(solve_puzzle())