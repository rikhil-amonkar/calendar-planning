import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    names = ['Arnold', 'Eric', 'Peter']
    cigars = ['pall mall', 'blue master', 'prince']
    animals = ['horse', 'cat', 'bird']
    children = ['Bella', 'Fred', 'Meredith']
    genres = ['science fiction', 'romance', 'mystery']
    phones = ['google pixel 6', 'iphone 13', 'samsung galaxy s21']
    
    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for cigar_perm in permutations(cigars):
            for animal_perm in permutations(animals):
                for child_perm in permutations(children):
                    for genre_perm in permutations(genres):
                        for phone_perm in permutations(phones):
                            # Assign each permutation to houses 1, 2, 3
                            solution = {
                                1: {
                                    'Name': name_perm[0],
                                    'Cigar': cigar_perm[0],
                                    'Animal': animal_perm[0],
                                    'Children': child_perm[0],
                                    'BookGenre': genre_perm[0],
                                    'PhoneModel': phone_perm[0]
                                },
                                2: {
                                    'Name': name_perm[1],
                                    'Cigar': cigar_perm[1],
                                    'Animal': animal_perm[1],
                                    'Children': child_perm[1],
                                    'BookGenre': genre_perm[1],
                                    'PhoneModel': phone_perm[1]
                                },
                                3: {
                                    'Name': name_perm[2],
                                    'Cigar': cigar_perm[2],
                                    'Animal': animal_perm[2],
                                    'Children': child_perm[2],
                                    'BookGenre': genre_perm[2],
                                    'PhoneModel': phone_perm[2]
                                }
                            }
                            
                            # Check all constraints
                            # Clue 3: Pall Mall is in the second house
                            if solution[2]['Cigar'] != 'pall mall':
                                continue
                            
                            # Clue 2: Eric is the cat lover
                            eric_house = None
                            for house in [1, 2, 3]:
                                if solution[house]['Name'] == 'Eric':
                                    eric_house = house
                                    break
                            if eric_house is None or solution[eric_house]['Animal'] != 'cat':
                                continue
                            
                            # Clue 8: Peter is left of Eric
                            peter_house = None
                            for house in [1, 2, 3]:
                                if solution[house]['Name'] == 'Peter':
                                    peter_house = house
                                    break
                            if peter_house is None or peter_house >= eric_house:
                                continue
                            
                            # Clue 10: Science fiction is in the third house
                            if solution[3]['BookGenre'] != 'science fiction':
                                continue
                            
                            # Clue 9: Science fiction lover uses samsung galaxy s21
                            if solution[3]['PhoneModel'] != 'samsung galaxy s21':
                                continue
                            
                            # Clue 6: iPhone 13 is directly left of samsung galaxy s21
                            if not (solution[1]['PhoneModel'] == 'iphone 13' and solution[2]['PhoneModel'] == 'samsung galaxy s21') and \
                               not (solution[2]['PhoneModel'] == 'iphone 13' and solution[3]['PhoneModel'] == 'samsung galaxy s21'):
                                continue
                            
                            # Clue 1: Mystery lover's child is Fred
                            mystery_house = None
                            for house in [1, 2, 3]:
                                if solution[house]['BookGenre'] == 'mystery' and solution[house]['Children'] == 'Fred':
                                    mystery_house = house
                                    break
                            if mystery_house is None:
                                continue
                            
                            # Clue 11: Mystery is not in the second house
                            if solution[2]['BookGenre'] == 'mystery':
                                continue
                            
                            # Clue 7: Fred's child is directly left of Arnold
                            # Find house where child is Fred
                            fred_house = None
                            for house in [1, 2, 3]:
                                if solution[house]['Children'] == 'Fred':
                                    fred_house = house
                                    break
                            if fred_house is None or fred_house == 3:
                                continue
                            # Arnold must be in fred_house + 1
                            if solution[fred_house + 1]['Name'] != 'Arnold':
                                continue
                            
                            # Clue 4: Horse lover's child is Meredith
                            horse_house = None
                            for house in [1, 2, 3]:
                                if solution[house]['Animal'] == 'horse' and solution[house]['Children'] == 'Meredith':
                                    horse_house = house
                                    break
                            if horse_house is None:
                                continue
                            
                            # Clue 5: Bella's child is Prince smoker
                            bella_house = None
                            for house in [1, 2, 3]:
                                if solution[house]['Children'] == 'Bella' and solution[house]['Cigar'] == 'prince':
                                    bella_house = house
                                    break
                            if bella_house is None:
                                continue
                            
                            # If all constraints are satisfied, return the solution
                            result = {
                                "solution": {
                                    "header": ["House", "Name", "Cigar", "Animal", "Children", "BookGenre", "PhoneModel"],
                                    "rows": [
                                        ["1", solution[1]['Name'], solution[1]['Cigar'], solution[1]['Animal'], solution[1]['Children'], solution[1]['BookGenre'], solution[1]['PhoneModel']],
                                        ["2", solution[2]['Name'], solution[2]['Cigar'], solution[2]['Animal'], solution[2]['Children'], solution[2]['BookGenre'], solution[2]['PhoneModel']],
                                        ["3", solution[3]['Name'], solution[3]['Cigar'], solution[3]['Animal'], solution[3]['Children'], solution[3]['BookGenre'], solution[3]['PhoneModel']]
                                    ]
                                }
                            }
                            return result
    return {"solution": {"header": [], "rows": []}}

# Solve the puzzle and print the result
print(json.dumps(solve_puzzle(), indent=2))