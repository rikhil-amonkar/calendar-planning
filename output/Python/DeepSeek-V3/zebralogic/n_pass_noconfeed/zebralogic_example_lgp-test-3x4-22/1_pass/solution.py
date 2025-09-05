import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values for each category
    names = ['Arnold', 'Eric', 'Peter']
    music_genres = ['pop', 'rock', 'classical']
    children = ['Fred', 'Meredith', 'Bella']
    book_genres = ['mystery', 'romance', 'science fiction']
    
    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for music_perm in permutations(music_genres):
            for child_perm in permutations(children):
                for book_perm in permutations(book_genres):
                    # Create assignment for each house
                    assignment = []
                    for i in range(3):
                        house = {
                            'House': str(i + 1),
                            'Name': name_perm[i],
                            'MusicGenre': music_perm[i],
                            'Children': child_perm[i],
                            'BookGenre': book_perm[i]
                        }
                        assignment.append(house)
                    
                    # Check clue 2: Peter is in the first house
                    if assignment[0]['Name'] != 'Peter':
                        continue
                    
                    # Check clue 5: Eric is the person who loves mystery books
                    eric_found = False
                    for house in assignment:
                        if house['Name'] == 'Eric' and house['BookGenre'] == 'mystery':
                            eric_found = True
                            break
                    if not eric_found:
                        continue
                    
                    # Check clue 3: The person who loves mystery books is the person who loves classical music
                    mystery_book_house = None
                    for house in assignment:
                        if house['BookGenre'] == 'mystery':
                            mystery_book_house = house
                            break
                    if mystery_book_house and mystery_book_house['MusicGenre'] != 'classical':
                        continue
                    
                    # Check clue 4: The person who loves science fiction books is the person's child is named Meredith
                    scifi_book_house = None
                    for house in assignment:
                        if house['BookGenre'] == 'science fiction':
                            scifi_book_house = house
                            break
                    if scifi_book_house and scifi_book_house['Children'] != 'Meredith':
                        continue
                    
                    # Check clue 1: The person's child is named Fred is directly left of the person who loves mystery books
                    fred_house_index = None
                    mystery_book_house_index = None
                    for i, house in enumerate(assignment):
                        if house['Children'] == 'Fred':
                            fred_house_index = i
                        if house['BookGenre'] == 'mystery':
                            mystery_book_house_index = i
                    
                    if fred_house_index is None or mystery_book_house_index is None:
                        continue
                    if fred_house_index + 1 != mystery_book_house_index:
                        continue
                    
                    # Check clue 6: The person who loves rock music is somewhere to the right of the person who loves romance books
                    romance_book_house_index = None
                    rock_music_house_index = None
                    for i, house in enumerate(assignment):
                        if house['BookGenre'] == 'romance':
                            romance_book_house_index = i
                        if house['MusicGenre'] == 'rock':
                            rock_music_house_index = i
                    
                    if romance_book_house_index is None or rock_music_house_index is None:
                        continue
                    if rock_music_house_index <= romance_book_house_index:
                        continue
                    
                    # If all clues are satisfied, return the solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "MusicGenre", "Children", "BookGenre"],
                            "rows": []
                        }
                    }
                    
                    for house in assignment:
                        row = [
                            house['House'],
                            house['Name'],
                            house['MusicGenre'],
                            house['Children'],
                            house['BookGenre']
                        ]
                        solution["solution"]["rows"].append(row)
                    
                    return solution
    
    return None

def main():
    solution = solve_puzzle()
    if solution:
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"solution": {"header": [], "rows": []}}, indent=2))

if __name__ == "__main__":
    main()