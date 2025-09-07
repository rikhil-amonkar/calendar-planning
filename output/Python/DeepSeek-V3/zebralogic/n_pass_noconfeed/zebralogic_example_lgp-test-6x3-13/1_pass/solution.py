import json
from itertools import permutations

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Bob', 'Arnold', 'Carol', 'Alice', 'Peter', 'Eric']
    genres = ['romance', 'historical fiction', 'biography', 'mystery', 'fantasy', 'science fiction']
    occupations = ['artist', 'doctor', 'nurse', 'engineer', 'teacher', 'lawyer']
    
    # Generate all possible permutations for names, genres, occupations
    for name_perm in permutations(names):
        for genre_perm in permutations(genres):
            for occup_perm in permutations(occupations):
                assignment = {}
                valid = True
                
                # Create assignment dictionary
                for i, house in enumerate(houses):
                    assignment[house] = {
                        'Name': name_perm[i],
                        'BookGenre': genre_perm[i],
                        'Occupation': occup_perm[i]
                    }
                
                # Check clue 10: The person who is a doctor is in the first house.
                if assignment[1]['Occupation'] != 'doctor':
                    continue
                
                # Check clue 12: Eric is in the third house.
                if assignment[3]['Name'] != 'Eric':
                    continue
                
                # Check clue 1: Alice is the person who loves fantasy books.
                alice_house = None
                fantasy_house = None
                for house, attrs in assignment.items():
                    if attrs['Name'] == 'Alice':
                        alice_house = house
                    if attrs['BookGenre'] == 'fantasy':
                        fantasy_house = house
                if alice_house != fantasy_house:
                    continue
                
                # Check clue 3: Carol is the person who loves mystery books.
                carol_house = None
                mystery_house = None
                for house, attrs in assignment.items():
                    if attrs['Name'] == 'Carol':
                        carol_house = house
                    if attrs['BookGenre'] == 'mystery':
                        mystery_house = house
                if carol_house != mystery_house:
                    continue
                
                # Check clue 4: The person who is a lawyer is the person who loves fantasy books.
                lawyer_house = None
                for house, attrs in assignment.items():
                    if attrs['Occupation'] == 'lawyer':
                        lawyer_house = house
                if lawyer_house != fantasy_house:
                    continue
                
                # Check clue 5: Bob is not in the fifth house.
                if assignment[5]['Name'] == 'Bob':
                    continue
                
                # Check clue 13: The person who loves mystery books is not in the fifth house.
                if mystery_house == 5:
                    continue
                
                # Check clue 2: The person who loves mystery books and Bob are next to each other.
                bob_house = None
                for house, attrs in assignment.items():
                    if attrs['Name'] == 'Bob':
                        bob_house = house
                if abs(mystery_house - bob_house) != 1:
                    continue
                
                # Check clue 6: Arnold is somewhere to the left of the person who is an engineer.
                arnold_house = None
                engineer_house = None
                for house, attrs in assignment.items():
                    if attrs['Name'] == 'Arnold':
                        arnold_house = house
                    if attrs['Occupation'] == 'engineer':
                        engineer_house = house
                if arnold_house is None or engineer_house is None or arnold_house >= engineer_house:
                    continue
                
                # Check clue 7: The person who is a nurse is directly left of Alice.
                nurse_house = None
                for house, attrs in assignment.items():
                    if attrs['Occupation'] == 'nurse':
                        nurse_house = house
                if nurse_house != alice_house - 1:
                    continue
                
                # Check clue 8: The person who loves biography books is the person who is a teacher.
                biography_house = None
                teacher_house = None
                for house, attrs in assignment.items():
                    if attrs['BookGenre'] == 'biography':
                        biography_house = house
                    if attrs['Occupation'] == 'teacher':
                        teacher_house = house
                if biography_house != teacher_house:
                    continue
                
                # Check clue 9: The person who loves historical fiction books is somewhere to the left of the person who is a teacher.
                historical_house = None
                for house, attrs in assignment.items():
                    if attrs['BookGenre'] == 'historical fiction':
                        historical_house = house
                if historical_house is None or teacher_house is None or historical_house >= teacher_house:
                    continue
                
                # Check clue 11: The person who loves science fiction books is the person who is an artist.
                scifi_house = None
                artist_house = None
                for house, attrs in assignment.items():
                    if attrs['BookGenre'] == 'science fiction':
                        scifi_house = house
                    if attrs['Occupation'] == 'artist':
                        artist_house = house
                if scifi_house != artist_house:
                    continue
                
                # If we reach here, all constraints are satisfied
                result = {
                    "solution": {
                        "header": ["House", "Name", "BookGenre", "Occupation"],
                        "rows": []
                    }
                }
                
                for house in sorted(assignment.keys()):
                    attrs = assignment[house]
                    result["solution"]["rows"].append([
                        str(house),
                        attrs['Name'],
                        attrs['BookGenre'],
                        attrs['Occupation']
                    ])
                
                return result
    
    return None

def main():
    solution = solve_puzzle()
    if solution:
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"solution": {"header": [], "rows": []}}, indent=2))

if __name__ == "__main__":
    main()