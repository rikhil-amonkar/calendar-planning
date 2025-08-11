import json
from itertools import permutations

def solve_puzzle():
    # Define all possible options for each attribute
    names = ['Arnold', 'Eric', 'Peter']
    cigars = ['pall mall', 'blue master', 'prince']
    animals = ['horse', 'cat', 'bird']
    children = ['Bella', 'Fred', 'Meredith']
    genres = ['science fiction', 'romance', 'mystery']
    phones = ['google pixel 6', 'iphone 13', 'samsung galaxy s21']
    
    # Generate all possible permutations for each attribute
    for name_perm in permutations(names):
        for cigar_perm in permutations(cigars):
            for animal_perm in permutations(animals):
                for child_perm in permutations(children):
                    for genre_perm in permutations(genres):
                        for phone_perm in permutations(phones):
                            # Assign each permutation to houses 1-3
                            solution = [
                                {
                                    'House': '1',
                                    'Name': name_perm[0],
                                    'cigar': cigar_perm[0],
                                    'animal': animal_perm[0],
                                    'child': child_perm[0],
                                    'book genre': genre_perm[0],
                                    'phone model': phone_perm[0]
                                },
                                {
                                    'House': '2',
                                    'Name': name_perm[1],
                                    'cigar': cigar_perm[1],
                                    'animal': animal_perm[1],
                                    'child': child_perm[1],
                                    'book genre': genre_perm[1],
                                    'phone model': phone_perm[1]
                                },
                                {
                                    'House': '3',
                                    'Name': name_perm[2],
                                    'cigar': cigar_perm[2],
                                    'animal': animal_perm[2],
                                    'child': child_perm[2],
                                    'book genre': genre_perm[2],
                                    'phone model': phone_perm[2]
                                }
                            ]
                            
                            # Check all constraints
                            valid = True
                            
                            # Clue 2: The cat lover is Eric
                            for house in solution:
                                if house['animal'] == 'cat' and house['Name'] != 'Eric':
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            # Clue 3: Pall Mall is in the second house
                            if solution[1]['cigar'] != 'pall mall':
                                valid = False
                                continue
                            
                            # Clue 5: Child Bella is the Prince smoker
                            for house in solution:
                                if house['child'] == 'Bella' and house['cigar'] != 'prince':
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            # Clue 6: iPhone 13 is directly left of Samsung Galaxy S21
                            iphone_pos = -1
                            samsung_pos = -1
                            for i in range(3):
                                if solution[i]['phone model'] == 'iphone 13':
                                    iphone_pos = i
                                if solution[i]['phone model'] == 'samsung galaxy s21':
                                    samsung_pos = i
                            if iphone_pos != samsung_pos - 1:
                                valid = False
                                continue
                            
                            # Clue 7: Child Fred is directly left of Arnold
                            fred_pos = -1
                            arnold_pos = -1
                            for i in range(3):
                                if solution[i]['child'] == 'Fred':
                                    fred_pos = i
                                if solution[i]['Name'] == 'Arnold':
                                    arnold_pos = i
                            if fred_pos != arnold_pos - 1:
                                valid = False
                                continue
                            
                            # Clue 8: Peter is left of Eric
                            peter_pos = -1
                            eric_pos = -1
                            for i in range(3):
                                if solution[i]['Name'] == 'Peter':
                                    peter_pos = i
                                if solution[i]['Name'] == 'Eric':
                                    eric_pos = i
                            if peter_pos >= eric_pos:
                                valid = False
                                continue
                            
                            # Clue 9: Science fiction lover uses Samsung Galaxy S21
                            for house in solution:
                                if house['book genre'] == 'science fiction' and house['phone model'] != 'samsung galaxy s21':
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            # Clue 10: Science fiction is in the third house
                            if solution[2]['book genre'] != 'science fiction':
                                valid = False
                                continue
                            
                            # Clue 4: Horse lover's child is Meredith
                            for house in solution:
                                if house['animal'] == 'horse' and house['child'] != 'Meredith':
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            # Clue 1: Mystery lover's child is Fred
                            for house in solution:
                                if house['book genre'] == 'mystery' and house['child'] != 'Fred':
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            # Clue 11: Mystery is not in the second house
                            if solution[1]['book genre'] == 'mystery':
                                valid = False
                                continue
                            
                            if valid:
                                # Prepare the output
                                output = {
                                    "solution": {
                                        "header": ["House", "Name", "cigar", "animal", "child", "book genre", "phone model"],
                                        "rows": []
                                    }
                                }
                                for house in solution:
                                    output["solution"]["rows"].append([
                                        house['House'],
                                        house['Name'],
                                        house['cigar'],
                                        house['animal'],
                                        house['child'],
                                        house['book genre'],
                                        house['phone model']
                                    ])
                                return output
    return {"solution": {"header": [], "rows": []}}

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))