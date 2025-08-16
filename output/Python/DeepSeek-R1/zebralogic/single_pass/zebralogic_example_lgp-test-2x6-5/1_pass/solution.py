import json

def main():
    # Initialize the houses with house numbers as strings and attributes as None.
    house1 = {'House': '1', 'Name': None, 'Occupation': None, 'Birthday': None, 'HouseStyle': None, 'Height': None, 'Cigar': None}
    house2 = {'House': '2', 'Name': None, 'Occupation': None, 'Birthday': None, 'HouseStyle': None, 'Height': None, 'Cigar': None}
    
    # Apply constraints step by step.
    
    # Clue 1: The engineer is in the first house.
    house1['Occupation'] = 'engineer'
    
    # Clue 6: The engineer is Eric.
    house1['Name'] = 'Eric'
    
    # The remaining name and occupation for house2.
    house2['Name'] = 'Arnold'
    house2['Occupation'] = 'doctor'
    
    # Clue 3: The colonial-style house is the engineer (house1).
    house1['HouseStyle'] = 'colonial'
    house2['HouseStyle'] = 'victorian'
    
    # Clue 4: The very short person is the engineer (house1).
    house1['Height'] = 'very short'
    house2['Height'] = 'short'
    
    # Clue 5: The short person (house2) prefers Pall Mall.
    house2['Cigar'] = 'pall mall'
    house1['Cigar'] = 'prince'
    
    # Clue 2: The April birthday and the doctor are next to each other and distinct.
    # Since the doctor is in house2, the April birthday must be in house1 (adjacent and distinct person).
    house1['Birthday'] = 'april'
    house2['Birthday'] = 'sept'
    
    # Prepare the solution in the required format.
    header = ["House", "Name", "Occupation", "Birthday", "HouseStyle", "Height", "Cigar"]
    rows = []
    for house in [house1, house2]:
        row = [house[attr] for attr in header]
        rows.append(row)
    
    solution_dict = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    
    # Output the solution as JSON.
    print(json.dumps(solution_dict))

if __name__ == "__main__":
    main()