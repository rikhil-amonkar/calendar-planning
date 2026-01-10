import itertools
import json

def main():
    # Define the attributes and their possible values
    attributes = {
        'Name': ['Eric', 'Arnold'],
        'Hobby': ['gardening', 'photography'],
        'BookGenre': ['science fiction', 'mystery'],
        'MusicGenre': ['rock', 'pop'],
        'Birthday': ['april', 'sept']
    }
    
    # Generate all possible permutations for each attribute
    name_perms = list(itertools.permutations(attributes['Name']))
    hobby_perms = list(itertools.permutations(attributes['Hobby']))
    book_perms = list(itertools.permutations(attributes['BookGenre']))
    music_perms = list(itertools.permutations(attributes['MusicGenre']))
    birthday_perms = list(itertools.permutations(attributes['Birthday']))
    
    # Combine all permutations to form complete assignments
    all_assignments = itertools.product(name_perms, hobby_perms, book_perms, music_perms, birthday_perms)
    
    # Check each assignment against the constraints
    for assignment in all_assignments:
        name_assign, hobby_assign, book_assign, music_assign, birthday_assign = assignment
        
        # Create house dictionaries
        H1 = {
            'Name': name_assign[0],
            'Hobby': hobby_assign[0],
            'BookGenre': book_assign[0],
            'MusicGenre': music_assign[0],
            'Birthday': birthday_assign[0]
        }
        H2 = {
            'Name': name_assign[1],
            'Hobby': hobby_assign[1],
            'BookGenre': book_assign[1],
            'MusicGenre': music_assign[1],
            'Birthday': birthday_assign[1]
        }
        
        # Check constraints
        # Clue 1: Mystery books and rock music are the same person
        mystery_house = H1 if H1['BookGenre'] == 'mystery' else H2 if H2['BookGenre'] == 'mystery' else None
        if mystery_house is None or mystery_house['MusicGenre'] != 'rock':
            continue
            
        # Clue 2: Arnold not in first house
        if H1['Name'] == 'Arnold':
            continue
            
        # Clue 3: Mystery books and gardening are the same person
        if mystery_house['Hobby'] != 'gardening':
            continue
            
        # Clue 4: April birthday is Arnold
        april_house = H1 if H1['Birthday'] == 'april' else H2 if H2['Birthday'] == 'april' else None
        if april_house is None or april_house['Name'] != 'Arnold':
            continue
            
        # Clue 5: Mystery books in first house
        if mystery_house != H1:
            continue
            
        # Found the solution
        solution = {
            "solution": {
                "header": ["House", "Name", "Hobby", "BookGenre", "MusicGenre", "Birthday"],
                "rows": [
                    ["1", H1['Name'], H1['Hobby'], H1['BookGenre'], H1['MusicGenre'], H1['Birthday']],
                    ["2", H2['Name'], H2['Hobby'], H2['BookGenre'], H2['MusicGenre'], H2['Birthday']]
                ]
            }
        }
        
        print(json.dumps(solution, indent=2))
        return
    
    print("No solution found")

if __name__ == "__main__":
    main()