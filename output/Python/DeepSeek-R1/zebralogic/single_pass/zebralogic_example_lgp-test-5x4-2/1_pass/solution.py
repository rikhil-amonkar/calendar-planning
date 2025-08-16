import json

def main():
    houses = [{'name': None, 'color': None, 'phone': None, 'occupation': None} for _ in range(5)]
    
    # Fixed assignment: Bob in second house (index1)
    houses[1]['name'] = 'Bob'
    
    # From clues 3 and 4: doctor uses samsung and loves blue -> assign to house1 (index1)
    houses[1]['occupation'] = 'doctor'
    houses[1]['phone'] = 'samsung galaxy s21'
    houses[1]['color'] = 'blue'
    
    # Clue7: blue directly left of red -> house2 (index2) is red
    houses[2]['color'] = 'red'
    
    # Clue14: red is right of teacher -> teacher must be in house0 (index0) (since house1 is doctor)
    houses[0]['occupation'] = 'teacher'
    # Clue12 and 13: teacher is Eric and uses google pixel
    houses[0]['name'] = 'Eric'
    houses[0]['phone'] = 'google pixel 6'
    
    # Clue9: one house between google and huawei -> since google is at house0, huawei must be at house2 (index2)
    houses[2]['phone'] = 'huawei p50'
    
    # Clue8: lawyer is right of doctor (house1) -> so house index > 1
    # Clue1: engineer is right of lawyer
    # Therefore, lawyer at house3 (index3), engineer at house4 (index4)
    houses[3]['occupation'] = 'lawyer'
    houses[4]['occupation'] = 'engineer'
    # Clue6: lawyer uses oneplus9
    houses[3]['phone'] = 'oneplus 9'
    
    # The remaining occupation is artist -> house2 (index2)
    houses[2]['occupation'] = 'artist'
    
    # Clue10: Arnold is engineer -> house4 (index4) name is Arnold
    houses[4]['name'] = 'Arnold'
    
    # Clue11: Alice loves yellow -> find Alice and assign yellow
    # Houses left: house2 (index2) and house3 (index3) for names Alice and Peter
    # House2 is red, so Alice cannot be there (yellow required) -> Alice at house3 (index3)
    houses[3]['name'] = 'Alice'
    houses[3]['color'] = 'yellow'
    
    # Then house2 (index2) must be Peter
    houses[2]['name'] = 'Peter'
    
    # Remaining colors: green and white for house0 and house4
    # Clue5: green not in fifth house -> house4 (index4) cannot be green -> house4 is white, house0 is green
    houses[0]['color'] = 'green'
    houses[4]['color'] = 'white'
    
    # Remaining phone: iphone 13 for house4 (index4)
    houses[4]['phone'] = 'iphone 13'
    
    # Build the output rows
    rows = []
    for i in range(5):
        house_number = str(i+1)
        name = houses[i]['name']
        color = houses[i]['color']
        phone_model = houses[i]['phone']
        occupation = houses[i]['occupation']
        rows.append([house_number, name, color, phone_model, occupation])
    
    solution_dict = {
        "solution": {
            "header": ["House", "Name", "Color", "PhoneModel", "Occupation"],
            "rows": rows
        }
    }
    
    print(json.dumps(solution_dict))

if __name__ == "__main__":
    main()