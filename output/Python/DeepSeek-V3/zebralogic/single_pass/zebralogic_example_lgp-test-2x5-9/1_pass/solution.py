import json
from itertools import permutations

def solve_puzzle():
    # Define all possible attributes
    houses = [1, 2]
    names = ['Arnold', 'Eric']
    book_genres = ['science fiction', 'mystery']
    vacations = ['mountain', 'beach']
    animals = ['cat', 'horse']
    music_genres = ['rock', 'pop']

    # Generate all possible permutations for each attribute
    for name_perm in permutations(names):
        for book_perm in permutations(book_genres):
            for vacation_perm in permutations(vacations):
                for animal_perm in permutations(animals):
                    for music_perm in permutations(music_genres):
                        # Assign attributes to houses
                        solution = {
                            1: {
                                'Name': name_perm[0],
                                'Book Genre': book_perm[0],
                                'Vacation': vacation_perm[0],
                                'Animal': animal_perm[0],
                                'Music Genre': music_perm[0]
                            },
                            2: {
                                'Name': name_perm[1],
                                'Book Genre': book_perm[1],
                                'Vacation': vacation_perm[1],
                                'Animal': animal_perm[1],
                                'Music Genre': music_perm[1]
                            }
                        }

                        # Apply clues to check validity
                        # Clue 1: The person who loves beach vacations is Eric.
                        beach_vacation_house = None
                        for house in [1, 2]:
                            if solution[house]['Vacation'] == 'beach':
                                beach_vacation_house = house
                        if beach_vacation_house is None or solution[beach_vacation_house]['Name'] != 'Eric':
                            continue

                        # Clue 2: The person who loves pop music is the person who loves beach vacations.
                        if solution[beach_vacation_house]['Music Genre'] != 'pop':
                            continue

                        # Clue 3: The person who loves rock music is the person who loves mystery books.
                        rock_music_house = None
                        for house in [1, 2]:
                            if solution[house]['Music Genre'] == 'rock':
                                rock_music_house = house
                        if rock_music_house is None or solution[rock_music_house]['Book Genre'] != 'mystery':
                            continue

                        # Clue 4: The cat lover is not in the second house.
                        if solution[2]['Animal'] == 'cat':
                            continue

                        # Clue 5: The person who loves mystery books is in the first house.
                        if solution[1]['Book Genre'] != 'mystery':
                            continue

                        # If all clues are satisfied, return the solution
                        result = {
                            "solution": {
                                "header": ["House", "Name", "Book Genre", "Vacation", "Animal", "Music Genre"],
                                "rows": [
                                    ["1", solution[1]['Name'], solution[1]['Book Genre'], solution[1]['Vacation'], solution[1]['Animal'], solution[1]['Music Genre']],
                                    ["2", solution[2]['Name'], solution[2]['Book Genre'], solution[2]['Vacation'], solution[2]['Animal'], solution[2]['Music Genre']]
                                ]
                            }
                        }
                        return json.dumps(result, indent=2)

    return json.dumps({"error": "No solution found"}, indent=2)

print(solve_puzzle())