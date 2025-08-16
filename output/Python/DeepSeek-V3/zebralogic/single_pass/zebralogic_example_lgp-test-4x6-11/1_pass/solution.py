import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    houses = ['1', '2', '3', '4']
    names = ['Peter', 'Alice', 'Eric', 'Arnold']
    hobbies = ['cooking', 'painting', 'gardening', 'photography']
    animals = ['horse', 'fish', 'cat', 'bird']
    book_genres = ['fantasy', 'mystery', 'romance', 'science fiction']
    birthday_months = ['april', 'jan', 'sept', 'feb']
    music_genres = ['pop', 'rock', 'classical', 'jazz']
    
    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for hobby_perm in permutations(hobbies):
            for animal_perm in permutations(animals):
                for book_perm in permutations(book_genres):
                    for bday_perm in permutations(birthday_months):
                        for music_perm in permutations(music_genres):
                            # Assign each permutation to houses
                            assignment = []
                            for i in range(4):
                                assignment.append({
                                    'House': houses[i],
                                    'Name': name_perm[i],
                                    'Hobby': hobby_perm[i],
                                    'Animal': animal_perm[i],
                                    'BookGenre': book_perm[i],
                                    'Birthday': bday_perm[i],
                                    'MusicGenre': music_perm[i]
                                })
                            
                            # Check all constraints
                            valid = True
                            
                            # Clue 1: cooking hobby ↔ romance book
                            for house in assignment:
                                if (house['Hobby'] == 'cooking') != (house['BookGenre'] == 'romance'):
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            # Clue 2: feb birthday ↔ pop music
                            for house in assignment:
                                if (house['Birthday'] == 'feb') != (house['MusicGenre'] == 'pop'):
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            # Clue 3: Eric not in house 2
                            if assignment[1]['Name'] == 'Eric':
                                valid = False
                            if not valid:
                                continue
                            
                            # Clue 4: romance book not in house 4
                            if assignment[3]['BookGenre'] == 'romance':
                                valid = False
                            if not valid:
                                continue
                            
                            # Clue 5: feb birthday ↔ fish
                            for house in assignment:
                                if (house['Birthday'] == 'feb') != (house['Animal'] == 'fish'):
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            # Clue 6: Alice is right of fantasy book lover
                            fantasy_house = None
                            alice_house = None
                            for i, house in enumerate(assignment):
                                if house['BookGenre'] == 'fantasy':
                                    fantasy_house = i + 1  # 1-based
                                if house['Name'] == 'Alice':
                                    alice_house = i + 1
                            if fantasy_house is None or alice_house is None or alice_house <= fantasy_house:
                                valid = False
                            if not valid:
                                continue
                            
                            # Clue 7: horse ↔ rock music
                            for house in assignment:
                                if (house['Animal'] == 'horse') != (house['MusicGenre'] == 'rock'):
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            # Clue 8: gardening hobby ↔ april birthday
                            for house in assignment:
                                if (house['Hobby'] == 'gardening') != (house['Birthday'] == 'april'):
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            # Clue 9: jazz music ↔ cooking hobby
                            for house in assignment:
                                if (house['MusicGenre'] == 'jazz') != (house['Hobby'] == 'cooking'):
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            # Clue 10: rock music ↔ mystery book
                            for house in assignment:
                                if (house['MusicGenre'] == 'rock') != (house['BookGenre'] == 'mystery'):
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            # Clue 11: painting is directly left of romance
                            painting_left = False
                            for i in range(3):
                                if assignment[i]['Hobby'] == 'painting' and assignment[i+1]['BookGenre'] == 'romance':
                                    painting_left = True
                                    break
                            if not painting_left:
                                valid = False
                            if not valid:
                                continue
                            
                            # Clue 12: Peter loves pop music
                            for house in assignment:
                                if (house['Name'] == 'Peter') != (house['MusicGenre'] == 'pop'):
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            # Clue 13: gardening hobby is Arnold
                            for house in assignment:
                                if (house['Hobby'] == 'gardening') != (house['Name'] == 'Arnold'):
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            # Clue 14: rock music is directly left of jan birthday
                            rock_left = False
                            for i in range(3):
                                if assignment[i]['MusicGenre'] == 'rock' and assignment[i+1]['Birthday'] == 'jan':
                                    rock_left = True
                                    break
                            if not rock_left:
                                valid = False
                            if not valid:
                                continue
                            
                            # Clue 15: cooking not in house 3
                            if assignment[2]['Hobby'] == 'cooking':
                                valid = False
                            if not valid:
                                continue
                            
                            # Clue 16: cat is right of horse
                            horse_pos = None
                            cat_pos = None
                            for i, house in enumerate(assignment):
                                if house['Animal'] == 'horse':
                                    horse_pos = i
                                if house['Animal'] == 'cat':
                                    cat_pos = i
                            if horse_pos is None or cat_pos is None or cat_pos <= horse_pos:
                                valid = False
                            if not valid:
                                continue
                            
                            # If all constraints are satisfied, return the solution
                            if valid:
                                solution = {
                                    "solution": {
                                        "header": ["House", "Name", "Hobby", "Animal", "BookGenre", "Birthday", "MusicGenre"],
                                        "rows": []
                                    }
                                }
                                for house in assignment:
                                    solution["solution"]["rows"].append([
                                        house['House'],
                                        house['Name'],
                                        house['Hobby'],
                                        house['Animal'],
                                        house['BookGenre'],
                                        house['Birthday'],
                                        house['MusicGenre']
                                    ])
                                return solution
    return {"solution": {"header": [], "rows": []}}

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))