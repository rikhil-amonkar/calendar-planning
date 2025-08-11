import json

def main():
    houses = [{'name': None, 'color': None, 'phone': None, 'occupation': None} for _ in range(5)]
    
    # Clue 2: Bob is in the second house (house 2, index 1)
    houses[1]['name'] = 'Bob'
    
    # Clue 10: Arnold is the engineer
    # Clue 11: Alice loves yellow
    # Clue 12: Eric uses google pixel 6
    # Clue 13: The person who uses google pixel 6 is the teacher -> Eric is teacher
    # Assign Eric to house 1 (index 0)
    houses[0]['name'] = 'Eric'
    houses[0]['phone'] = 'google pixel 6'
    houses[0]['occupation'] = 'teacher'
    
    # Clue 9: One house between google pixel 6 and huawei p50 -> |0 - ?| = 2 -> positions 0 and 2
    houses[2]['phone'] = 'huawei p50'
    
    # Clue 3 and 4: Samsung user is doctor and loves blue
    # Clue 7: Blue is directly left of red -> so if blue is at house i, red is at i+1
    # Assign Bob (house 2, index1) as doctor, with samsung and blue
    houses[1]['occupation'] = 'doctor'
    houses[1]['phone'] = 'samsung galaxy s21'
    houses[1]['color'] = 'blue'
    # Then red must be at house 3 (index2)
    houses[2]['color'] = 'red'
    
    # Clue 6: Lawyer uses oneplus 9
    # Clue 8: Lawyer is to the right of the samsung user (doctor at index1) -> so lawyer at index2,3,4
    # But house2 (index1) is doctor, house3 (index2) has phone huawei, not oneplus -> skip index2
    # Assign lawyer to house4 (index3) with oneplus9
    houses[3]['phone'] = 'oneplus 9'
    houses[3]['occupation'] = 'lawyer'
    
    # Clue 1: Engineer is to the right of lawyer -> engineer at house5 (index4)
    houses[4]['occupation'] = 'engineer'
    # Clue 10: Arnold is engineer -> so house5 (index4) is Arnold
    houses[4]['name'] = 'Arnold'
    
    # Clue 11: Alice loves yellow -> assign to house4 (index3) as lawyer
    houses[3]['name'] = 'Alice'
    houses[3]['color'] = 'yellow'
    
    # Only Peter left for house3 (index2)
    houses[2]['name'] = 'Peter'
    # Only artist occupation left for house3 (index2)
    houses[2]['occupation'] = 'artist'
    
    # Now assign colors: only green and white left
    # Clue 5: Green not in fifth house -> so house5 (index4) cannot be green -> must be white
    houses[4]['color'] = 'white'
    # Then house1 (index0) must be green
    houses[0]['color'] = 'green'
    
    # Only phone left for house5 (index4) is iphone13
    phones = ['huawei p50', 'samsung galaxy s21', 'oneplus 9', 'iphone 13', 'google pixel 6']
    assigned_phones = [house['phone'] for house in houses]
    remaining_phone = [p for p in phones if p not in assigned_phones][0]
    houses[4]['phone'] = remaining_phone

    # Prepare the solution in the required JSON format
    solution_rows = []
    for i in range(5):
        house_number = str(i+1)
        row = [
            house_number,
            houses[i]['name'],
            houses[i]['color'],
            houses[i]['phone'],
            houses[i]['occupation']
        ]
        solution_rows.append(row)
    
    header = ["House", "Name", "favorite color", "phone model", "occupation"]
    solution_dict = {
        "solution": {
            "header": header,
            "rows": solution_rows
        }
    }
    
    print(json.dumps(solution_dict, indent=2))

if __name__ == "__main__":
    main()