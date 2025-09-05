import json

def main():
    # Initialize the houses
    houses = [
        {'House': '1', 'Name': None, 'BookGenre': None, 'Vacation': None, 'Animal': None, 'MusicGenre': None},
        {'House': '2', 'Name': None, 'BookGenre': None, 'Vacation': None, 'Animal': None, 'MusicGenre': None}
    ]
    
    # Apply clue 5: Mystery books in first house
    for house in houses:
        if house['House'] == '1':
            house['BookGenre'] = 'mystery'
    
    # Apply clue 4: Cat lover not in second house -> so in first
    for house in houses:
        if house['House'] == '1':
            house['Animal'] = 'cat'
    
    # Apply clue 3: Rock music lover is mystery book lover -> so house 1 has rock music
    for house in houses:
        if house['BookGenre'] == 'mystery':
            house['MusicGenre'] = 'rock'
    
    # Apply clue 1 and 2: Beach vacation is Eric, and pop music is beach vacation
    # Since house 1 has rock music, beach must be in house 2
    for house in houses:
        if house['House'] == '2':
            house['Vacation'] = 'beach'
            house['Name'] = 'Eric'
            house['MusicGenre'] = 'pop'
    
    # Now assign remaining attributes
    # House 1 gets remaining name: Arnold
    for house in houses:
        if house['Name'] is None:
            house['Name'] = 'Arnold'
    
    # House 1 gets remaining vacation: mountain
    for house in houses:
        if house['Vacation'] is None:
            house['Vacation'] = 'mountain'
    
    # House 2 gets remaining book genre: science fiction
    for house in houses:
        if house['BookGenre'] is None:
            house['BookGenre'] = 'science fiction'
    
    # House 2 gets remaining animal: horse
    for house in houses:
        if house['Animal'] is None:
            house['Animal'] = 'horse'
    
    # Prepare output
    header = ["House", "Name", "BookGenre", "Vacation", "Animal", "MusicGenre"]
    rows = []
    for house in houses:
        row = [
            house['House'],
            house['Name'],
            house['BookGenre'],
            house['Vacation'],
            house['Animal'],
            house['MusicGenre']
        ]
        rows.append(row)
    
    solution = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    
    print(json.dumps(solution, indent=2))

if __name__ == "__main__":
    main()