import json

def main():
    # Initialize the houses as a list of dictionaries
    houses = [
        {'Name': None, 'Cigar': None, 'Animal': None, 'Child': None, 'Book': None, 'Phone': None},
        {'Name': None, 'Cigar': None, 'Animal': None, 'Child': None, 'Book': None, 'Phone': None},
        {'Name': None, 'Cigar': None, 'Animal': None, 'Child': None, 'Book': None, 'Phone': None}
    ]
    
    # Apply deductions based on constraints
    # From clue 10: Science fiction book in third house
    houses[2]['Book'] = 'science fiction'
    # From clue 9: Science fiction book house has Samsung Galaxy S21
    houses[2]['Phone'] = 'samsung galaxy s21'
    # From clue 6: iPhone 13 directly left of Samsung Galaxy S21 -> house1 (index1) has iPhone 13
    houses[1]['Phone'] = 'iphone 13'
    # Remaining phone for house0
    houses[0]['Phone'] = 'google pixel 6'
    
    # From clue 11: Mystery book not in second house (index1)
    # Books left: mystery and romance for house0 and house1
    houses[0]['Book'] = 'mystery'
    houses[1]['Book'] = 'romance'
    
    # From clue 1: Mystery book house has child Fred
    houses[0]['Child'] = 'Fred'
    
    # From clue 7: Child Fred house directly left of Arnold
    houses[1]['Name'] = 'Arnold'
    
    # From clue 8: Peter left of Eric
    # Names left: Peter and Eric for house0 and house2
    houses[0]['Name'] = 'Peter'
    houses[2]['Name'] = 'Eric'
    
    # From clue 2: Cat lover is Eric
    houses[2]['Animal'] = 'cat'
    
    # From clue 3: Pall Mall in second house
    houses[1]['Cigar'] = 'pall mall'
    
    # From clue 4: Horse house has child Meredith
    # House0 has child Fred, so horse not in house0. House2 has cat, so horse must be in house1
    houses[1]['Animal'] = 'horse'
    houses[1]['Child'] = 'Meredith'
    
    # Remaining child for house2
    houses[2]['Child'] = 'Bella'
    
    # From clue 5: Bella house has Prince cigar
    houses[2]['Cigar'] = 'prince'
    # Remaining cigar for house0
    houses[0]['Cigar'] = 'blue master'
    
    # Remaining animal for house0
    houses[0]['Animal'] = 'bird'
    
    # Verify all constraints are satisfied
    if not all_constraints_satisfied(houses):
        print("Error: Constraints not satisfied")
        return
    
    # Prepare the output
    header = ["House", "Name", "Cigar", "Animal", "Child", "Book", "Phone"]
    rows = []
    for i, house in enumerate(houses):
        row = [str(i+1)]
        for attr in header[1:]:
            row.append(house[attr])
        rows.append(row)
    
    solution_dict = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    
    print(json.dumps(solution_dict, indent=2))

def all_constraints_satisfied(houses):
    # Constraint 1: Mystery book house has child Fred
    for i in range(3):
        if houses[i]['Book'] == 'mystery':
            if houses[i]['Child'] != 'Fred':
                return False
    
    # Constraint 2: Cat lover is Eric
    for i in range(3):
        if houses[i]['Animal'] == 'cat':
            if houses[i]['Name'] != 'Eric':
                return False
    
    # Constraint 3: Pall Mall in second house
    if houses[1]['Cigar'] != 'pall mall':
        return False
    
    # Constraint 4: Horse house has child Meredith
    for i in range(3):
        if houses[i]['Animal'] == 'horse':
            if houses[i]['Child'] != 'Meredith':
                return False
    
    # Constraint 5: Bella house has Prince cigar
    for i in range(3):
        if houses[i]['Child'] == 'Bella':
            if houses[i]['Cigar'] != 'prince':
                return False
    
    # Constraint 6: iPhone 13 directly left of Samsung Galaxy S21
    if not (houses[1]['Phone'] == 'iphone 13' and houses[2]['Phone'] == 'samsung galaxy s21'):
        return False
    
    # Constraint 7: Fred child house directly left of Arnold
    for i in range(2):
        if houses[i]['Child'] == 'Fred':
            if houses[i+1]['Name'] != 'Arnold':
                return False
    
    # Constraint 8: Peter left of Eric
    peter_index = next(i for i, house in enumerate(houses) if house['Name'] == 'Peter')
    eric_index = next(i for i, house in enumerate(houses) if house['Name'] == 'Eric')
    if peter_index >= eric_index:
        return False
    
    # Constraint 9: Science fiction book house has Samsung Galaxy S21
    for i in range(3):
        if houses[i]['Book'] == 'science fiction':
            if houses[i]['Phone'] != 'samsung galaxy s21':
                return False
    
    # Constraint 10: Science fiction book in third house
    if houses[2]['Book'] != 'science fiction':
        return False
    
    # Constraint 11: Mystery book not in second house
    if houses[1]['Book'] == 'mystery':
        return False
    
    return True

if __name__ == "__main__":
    main()