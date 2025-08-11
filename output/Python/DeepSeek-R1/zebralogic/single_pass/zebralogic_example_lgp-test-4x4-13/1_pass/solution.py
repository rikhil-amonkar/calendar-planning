import json

def main():
    houses = [{'Name': None, 'Cigar': None, 'Sport': None, 'Drink': None} for _ in range(4)]
    
    # Apply direct clues
    houses[3]['Name'] = 'Peter'       # Clue1
    houses[2]['Sport'] = 'basketball'  # Clue8
    houses[2]['Name'] = 'Eric'         # Clue4
    houses[2]['Drink'] = 'tea'         # Clue2
    houses[0]['Drink'] = 'water'       # Clue6
    houses[3]['Cigar'] = 'pall mall'   # Clue10
    
    # Assign Arnold to house2 (index1) with deduced attributes
    houses[1]['Name'] = 'Arnold'
    houses[1]['Drink'] = 'coffee'      # Clue7
    houses[1]['Cigar'] = 'blue master' # Clue3
    houses[1]['Sport'] = 'tennis'      # Clue5 (via Clue3 and Clue5)
    
    # Assign the remaining name (Alice) to house1 (index0)
    for i in range(4):
        if houses[i]['Name'] is None:
            houses[i]['Name'] = 'Alice'
            break
    
    # Assign the remaining drink (milk) to house4 (index3)
    for i in range(4):
        if houses[i]['Drink'] is None:
            houses[i]['Drink'] = 'milk'
            break
    
    # Assign cigars to house1 (index0) and house3 (index2)
    cigars = ['prince', 'dunhill']
    if houses[0]['Cigar'] is None and houses[2]['Cigar'] is None:
        # Clue9: Prince smoker must love soccer, but house3 has basketball -> cannot be prince
        houses[0]['Cigar'] = 'prince'
        houses[2]['Cigar'] = 'dunhill'
    
    # Apply Clue9: Prince smoker loves soccer -> house1 (index0) has cigar prince -> set sport to soccer
    if houses[0]['Cigar'] == 'prince':
        houses[0]['Sport'] = 'soccer'
    
    # Assign the remaining sport (swimming) to house4 (index3)
    for i in range(4):
        if houses[i]['Sport'] is None:
            houses[i]['Sport'] = 'swimming'
            break
    
    # Prepare the output
    header = ["House", "Name", "Favorite Cigar", "Favorite Sport", "Favorite Drink"]
    rows = []
    for i in range(4):
        row = [
            str(i+1),
            houses[i]['Name'],
            houses[i]['Cigar'],
            houses[i]['Sport'],
            houses[i]['Drink']
        ]
        rows.append(row)
    
    solution_dict = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(solution_dict))

if __name__ == "__main__":
    main()