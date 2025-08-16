import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values for each category
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Bob', 'Arnold', 'Carol', 'Alice', 'Peter', 'Eric']
    genres = ['romance', 'historical fiction', 'biography', 'mystery', 'fantasy', 'science fiction']
    occupations = ['artist', 'doctor', 'nurse', 'engineer', 'teacher', 'lawyer']

    # Generate all possible permutations for names, genres, and occupations
    for name_perm in permutations(names):
        for genre_perm in permutations(genres):
            for occ_perm in permutations(occupations):
                # Create a dictionary to hold the current assignment
                assignment = {}
                for i in range(6):
                    house = i + 1
                    assignment[house] = {
                        'Name': name_perm[i],
                        'BookGenre': genre_perm[i],
                        'Occupation': occ_perm[i]
                    }

                # Check all constraints
                # Clue 10: The person who is a doctor is in the first house.
                if assignment[1]['Occupation'] != 'doctor':
                    continue

                # Clue 12: Eric is in the third house.
                if assignment[3]['Name'] != 'Eric':
                    continue

                # Clue 1: Alice is the person who loves fantasy books.
                alice_house = None
                for house in houses:
                    if assignment[house]['Name'] == 'Alice':
                        alice_house = house
                        break
                if alice_house is None:
                    continue
                if assignment[alice_house]['BookGenre'] != 'fantasy':
                    continue

                # Clue 4: The person who is a lawyer is the person who loves fantasy books.
                lawyer_house = None
                for house in houses:
                    if assignment[house]['Occupation'] == 'lawyer':
                        lawyer_house = house
                        break
                if lawyer_house is None or lawyer_house != alice_house:
                    continue

                # Clue 7: The person who is a nurse is directly left of Alice.
                if alice_house == 1:
                    continue  # Alice can't be in house 1 if someone is left of her
                if assignment[alice_house - 1]['Occupation'] != 'nurse':
                    continue

                # Clue 3: Carol is the person who loves mystery books.
                carol_house = None
                for house in houses:
                    if assignment[house]['Name'] == 'Carol':
                        carol_house = house
                        break
                if carol_house is None:
                    continue
                if assignment[carol_house]['BookGenre'] != 'mystery':
                    continue

                # Clue 2: The person who loves mystery books and Bob are next to each other.
                bob_house = None
                for house in houses:
                    if assignment[house]['Name'] == 'Bob':
                        bob_house = house
                        break
                if bob_house is None:
                    continue
                if abs(bob_house - carol_house) != 1:
                    continue

                # Clue 5: Bob is not in the fifth house.
                if bob_house == 5:
                    continue

                # Clue 13: The person who loves mystery books is not in the fifth house.
                if carol_house == 5:
                    continue

                # Clue 6: Arnold is somewhere to the left of the person who is an engineer.
                arnold_house = None
                engineer_house = None
                for house in houses:
                    if assignment[house]['Name'] == 'Arnold':
                        arnold_house = house
                    if assignment[house]['Occupation'] == 'engineer':
                        engineer_house = house
                if arnold_house is None or engineer_house is None:
                    continue
                if arnold_house >= engineer_house:
                    continue

                # Clue 8: The person who loves biography books is the person who is a teacher.
                teacher_house = None
                for house in houses:
                    if assignment[house]['Occupation'] == 'teacher':
                        teacher_house = house
                        break
                if teacher_house is None:
                    continue
                if assignment[teacher_house]['BookGenre'] != 'biography':
                    continue

                # Clue 9: The person who loves historical fiction books is somewhere to the left of the person who is a teacher.
                historical_fiction_house = None
                for house in houses:
                    if assignment[house]['BookGenre'] == 'historical fiction':
                        historical_fiction_house = house
                        break
                if historical_fiction_house is None:
                    continue
                if historical_fiction_house >= teacher_house:
                    continue

                # Clue 11: The person who loves science fiction books is the person who is an artist.
                artist_house = None
                for house in houses:
                    if assignment[house]['Occupation'] == 'artist':
                        artist_house = house
                        break
                if artist_house is None:
                    continue
                if assignment[artist_house]['BookGenre'] != 'science fiction':
                    continue

                # All constraints satisfied, prepare the solution
                solution = {
                    "solution": {
                        "header": ["House", "Name", "BookGenre", "Occupation"],
                        "rows": []
                    }
                }
                for house in houses:
                    row = [
                        str(house),
                        assignment[house]['Name'],
                        assignment[house]['BookGenre'],
                        assignment[house]['Occupation']
                    ]
                    solution["solution"]["rows"].append(row)
                return solution

    return {"solution": {"header": ["House", "Name", "BookGenre", "Occupation"], "rows": []}}

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))