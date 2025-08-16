import json

def main():
    houses = [{'House': i+1, 'Name': None, 'Height': None, 'PhoneModel': None} for i in range(6)]
    
    # Apply direct clues
    houses[5]['Height'] = 'short'  # Clue 12: house 6 is short
    houses[4]['PhoneModel'] = 'oneplus 9'  # Clue 7: house 5 uses OnePlus 9
    houses[3]['PhoneModel'] = 'google pixel 6'  # Clue 5: house 4 uses Google Pixel 6
    houses[4]['Height'] = 'very short'  # Clue 3: house 5 is very short
    houses[0]['Height'] = 'super tall'  # Clue 9: house 1 is super tall
    
    # Assign Carol (very tall, Xiaomi Mi 11) to house 2
    houses[1]['Name'] = 'Carol'
    houses[1]['Height'] = 'very tall'
    houses[1]['PhoneModel'] = 'xiaomi mi 11'
    
    # Assign Arnold (tall) to house 4 and Bob to house 3
    houses[3]['Name'] = 'Arnold'
    houses[3]['Height'] = 'tall'  # Clue 8
    houses[2]['Name'] = 'Bob'  # Clue 1: Bob left of Arnold
    houses[2]['Height'] = 'average'  # Only remaining height for house 3
    
    # Assign Eric to house 1
    houses[0]['Name'] = 'Eric'  # Clue 11: Eric left of house 4
    
    # Assign Huawei P50 to house 1
    houses[0]['PhoneModel'] = 'huawei p50'  # Clue 6 and Clue 2
    
    # Assign Peter to house 5 and Alice to house 6
    houses[4]['Name'] = 'Peter'
    houses[5]['Name'] = 'Alice'
    houses[5]['PhoneModel'] = 'iphone 13'  # Clue 2: Peter left of iPhone 13 user
    
    # Assign Samsung Galaxy S21 to house 3
    houses[2]['PhoneModel'] = 'samsung galaxy s21'
    
    # Prepare the solution in the required JSON format
    header = ["House", "Name", "Height", "PhoneModel"]
    rows = []
    for house in houses:
        rows.append([str(house['House']), house['Name'], house['Height'], house['PhoneModel']])
    
    solution_dict = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    
    print(json.dumps(solution_dict))

if __name__ == "__main__":
    main()