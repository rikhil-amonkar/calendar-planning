import json

def main():
    # Initialize house dictionaries
    house1 = {'House': '1', 'Name': None, 'BookGenre': None, 'Birthday': None, 'Animal': None}
    house2 = {'House': '2', 'Name': None, 'BookGenre': None, 'Birthday': None, 'Animal': None}
    
    # Apply clues
    house1['Name'] = 'Eric'          # Clue 1
    house1['Birthday'] = 'sept'       # Clue 2
    house1['Animal'] = 'horse'        # Clue 4
    house2['BookGenre'] = 'science fiction'  # Clue 3
    
    # Assign remaining attributes
    house2['Name'] = 'Arnold'
    house2['Birthday'] = 'april'
    house2['Animal'] = 'cat'
    house1['BookGenre'] = 'mystery'
    
    # Build the solution rows
    row1 = [house1['House'], house1['Name'], house1['BookGenre'], house1['Birthday'], house1['Animal']]
    row2 = [house2['House'], house2['Name'], house2['BookGenre'], house2['Birthday'], house2['Animal']]
    rows = [row1, row2]
    
    # Construct the solution dictionary
    solution_dict = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Birthday", "Animal"],
            "rows": rows
        }
    }
    
    # Output the solution as JSON
    print(json.dumps(solution_dict))

if __name__ == "__main__":
    main()