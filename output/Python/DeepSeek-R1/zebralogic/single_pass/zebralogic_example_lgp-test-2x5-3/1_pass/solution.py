import json

def main():
    # Initialize the two houses as dictionaries
    house1 = {'House': '1'}
    house2 = {'House': '2'}
    
    # Apply clue 2: Arnold is not in the first house -> House1 must be Eric, House2 must be Arnold
    house1['Name'] = 'Eric'
    house2['Name'] = 'Arnold'
    
    # Apply clue 4: Birthday in April is Arnold -> House2 has April, so House1 has Sept
    house1['Birthday'] = 'sept'
    house2['Birthday'] = 'april'
    
    # Apply clue 5: Mystery books are in the first house -> House1 has mystery, House2 has science fiction
    house1['BookGenre'] = 'mystery'
    house2['BookGenre'] = 'science fiction'
    
    # Apply clue 1: Mystery book lover (House1) loves rock music -> House1 has rock, House2 has pop
    house1['MusicGenre'] = 'rock'
    house2['MusicGenre'] = 'pop'
    
    # Apply clue 3: Mystery book lover (House1) enjoys gardening -> House1 has gardening, House2 has photography
    house1['Hobby'] = 'gardening'
    house2['Hobby'] = 'photography'
    
    # Build the solution structure
    header = ["House", "Name", "Hobby", "BookGenre", "MusicGenre", "Birthday"]
    rows = [
        [house1['House'], house1['Name'], house1['Hobby'], house1['BookGenre'], house1['MusicGenre'], house1['Birthday']],
        [house2['House'], house2['Name'], house2['Hobby'], house2['BookGenre'], house2['MusicGenre'], house2['Birthday']]
    ]
    
    solution = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    
    # Output as JSON
    print(json.dumps(solution, indent=2))

if __name__ == "__main__":
    main()