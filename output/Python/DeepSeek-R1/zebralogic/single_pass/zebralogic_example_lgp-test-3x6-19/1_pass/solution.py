import json

def main():
    houses = [
        {'House': '1'},
        {'House': '2'},
        {'House': '3'}
    ]
    
    # Apply clues step by step
    houses[2]['BookGenre'] = 'science fiction'  # Clue 10
    houses[2]['PhoneModel'] = 'samsung galaxy s21'  # Clue 9
    houses[1]['PhoneModel'] = 'iphone 13'  # Clue 6
    houses[0]['PhoneModel'] = 'google pixel 6'  # Deduced from remaining phones
    
    houses[0]['BookGenre'] = 'mystery'  # Clue 10 and 11
    houses[1]['BookGenre'] = 'romance'  # Deduced from remaining genres
    
    houses[0]['Children'] = 'Fred'  # Clue 1
    houses[1]['Name'] = 'Arnold'  # Clue 7
    houses[1]['Cigar'] = 'pall mall'  # Clue 3
    
    houses[0]['Name'] = 'Peter'  # Clue 8 and remaining names
    houses[2]['Name'] = 'Eric'   # Clue 8 and remaining names
    
    houses[2]['Animal'] = 'cat'  # Clue 2
    houses[0]['Animal'] = 'bird'  # Deduced from animals and Clue 4
    houses[1]['Animal'] = 'horse'  # Deduced from remaining animals
    houses[1]['Children'] = 'Meredith'  # Clue 4 (horse keeper has child Meredith)
    
    houses[2]['Children'] = 'Bella'  # Deduced from remaining children
    houses[2]['Cigar'] = 'prince'  # Clue 5 (child Bella is Prince smoker)
    houses[0]['Cigar'] = 'blue master'  # Deduced from remaining cigars
    
    # Prepare output
    header = ["House", "Name", "Cigar", "Animal", "Children", "BookGenre", "PhoneModel"]
    rows = []
    for house in houses:
        row = [
            house['House'],
            house['Name'],
            house['Cigar'],
            house['Animal'],
            house['Children'],
            house['BookGenre'],
            house['PhoneModel']
        ]
        rows.append(row)
    
    result = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()