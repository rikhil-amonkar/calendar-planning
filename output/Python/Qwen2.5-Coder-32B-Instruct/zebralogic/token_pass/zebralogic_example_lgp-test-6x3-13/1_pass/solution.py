import itertools
import json

# Define the possible values for each attribute
names = ["Bob", "Arnold", "Carol", "Alice", "Peter", "Eric"]
book_genres = ["romance", "historical fiction", "biography", "mystery", "fantasy", "science fiction"]
occupations = ["artist", "doctor", "nurse", "engineer", "teacher", "lawyer"]

# Function to check if a given state satisfies all constraints
def is_valid_state(state):
    # Unpack the state
    house1, house2, house3, house4, house5, house6 = state
    
    # Constraint 1: Alice is the person who loves fantasy books.
    if house1['Name'] == "Alice" and house1['BookGenre'] != "fantasy":
        return False
    if house2['Name'] == "Alice" and house2['BookGenre'] != "fantasy":
        return False
    if house3['Name'] == "Alice" and house3['BookGenre'] != "fantasy":
        return False
    if house4['Name'] == "Alice" and house4['BookGenre'] != "fantasy":
        return False
    if house5['Name'] == "Alice" and house5['BookGenre'] != "fantasy":
        return False
    if house6['Name'] == "Alice" and house6['BookGenre'] != "fantasy":
        return False
    
    # Constraint 2 & 13: The person who loves mystery books and Bob are next to each other, and mystery is not in the 5th house.
    mystery_house = None
    bob_house = None
    for i, house in enumerate(state):
        if house['BookGenre'] == "mystery":
            mystery_house = i
        if house['Name'] == "Bob":
            bob_house = i
    if mystery_house is not None and bob_house is not None:
        if abs(mystery_house - bob_house) != 1:
            return False
        if mystery_house == 4:
            return False
    
    # Constraint 3: Carol is the person who loves mystery books.
    if house1['Name'] == "Carol" and house1['BookGenre'] != "mystery":
        return False
    if house2['Name'] == "Carol" and house2['BookGenre'] != "mystery":
        return False
    if house3['Name'] == "Carol" and house3['BookGenre'] != "mystery":
        return False
    if house4['Name'] == "Carol" and house4['BookGenre'] != "mystery":
        return False
    if house5['Name'] == "Carol" and house5['BookGenre'] != "mystery":
        return False
    if house6['Name'] == "Carol" and house6['BookGenre'] != "mystery":
        return False
    
    # Constraint 4: The person who is a lawyer is the person who loves fantasy books.
    if any(house['Occupation'] == "lawyer" and house['BookGenre'] != "fantasy" for house in state):
        return False
    
    # Constraint 5: Bob is not in the fifth house.
    if house5['Name'] == "Bob":
        return False
    
    # Constraint 6: Arnold is somewhere to the left of the person who is an engineer.
    arnold_house = None
    engineer_house = None
    for i, house in enumerate(state):
        if house['Name'] == "Arnold":
            arnold_house = i
        if house['Occupation'] == "engineer":
            engineer_house = i
    if arnold_house is not None and engineer_house is not None:
        if arnold_house >= engineer_house:
            return False
    
    # Constraint 7: The person who is a nurse is directly left of Alice.
    for i in range(5):
        if state[i]['Occupation'] == "nurse" and state[i + 1]['Name'] == "Alice":
            break
    else:
        return False
    
    # Constraint 8: The person who loves biography books is the person who is a teacher.
    if any(house['BookGenre'] == "biography" and house['Occupation'] != "teacher" for house in state):
        return False
    
    # Constraint 9: The person who loves historical fiction books is somewhere to the left of the person who is a teacher.
    historical_fiction_house = None
    teacher_house = None
    for i, house in enumerate(state):
        if house['BookGenre'] == "historical fiction":
            historical_fiction_house = i
        if house['Occupation'] == "teacher":
            teacher_house = i
    if historical_fiction_house is not None and teacher_house is not None:
        if historical_fiction_house >= teacher_house:
            return False
    
    # Constraint 10: The person who is a doctor is in the first house.
    if house1['Occupation'] != "doctor":
        return False
    
    # Constraint 11: The person who loves science fiction books is the person who is an artist.
    if any(house['BookGenre'] == "science fiction" and house['Occupation'] != "artist" for house in state):
        return False
    
    # Constraint 12: Eric is in the third house.
    if house3['Name'] != "Eric":
        return False
    
    return True

# Generate all permutations of names, book genres, and occupations
name_permutations = itertools.permutations(names)
book_genre_permutations = itertools.permutations(book_genres)
occupation_permutations = itertools.permutations(occupations)

# Iterate through all possible permutations
for name_perm in name_permutations:
    for book_genre_perm in book_genre_permutations:
        for occupation_perm in occupation_permutations:
            state = [
                {"Name": name_perm[0], "BookGenre": book_genre_perm[0], "Occupation": occupation_perm[0]},
                {"Name": name_perm[1], "BookGenre": book_genre_perm[1], "Occupation": occupation_perm[1]},
                {"Name": name_perm[2], "BookGenre": book_genre_perm[2], "Occupation": occupation_perm[2]},
                {"Name": name_perm[3], "BookGenre": book_genre_perm[3], "Occupation": occupation_perm[3]},
                {"Name": name_perm[4], "BookGenre": book_genre_perm[4], "Occupation": occupation_perm[4]},
                {"Name": name_perm[5], "BookGenre": book_genre_perm[5], "Occupation": occupation_perm[5]}
            ]
            if is_valid_state(state):
                # Format the solution as JSON
                solution = {
                    "solution": {
                        "header": ["House", "Name", "BookGenre", "Occupation"],
                        "rows": [
                            ["1", state[0]['Name'], state[0]['BookGenre'], state[0]['Occupation']],
                            ["2", state[1]['Name'], state[1]['BookGenre'], state[1]['Occupation']],
                            ["3", state[2]['Name'], state[2]['BookGenre'], state[2]['Occupation']],
                            ["4", state[3]['Name'], state[3]['BookGenre'], state[3]['Occupation']],
                            ["5", state[4]['Name'], state[4]['BookGenre'], state[4]['Occupation']],
                            ["6", state[5]['Name'], state[5]['BookGenre'], state[5]['Occupation']]
                        ]
                    }
                }
                print(json.dumps(solution, indent=2))
                exit()