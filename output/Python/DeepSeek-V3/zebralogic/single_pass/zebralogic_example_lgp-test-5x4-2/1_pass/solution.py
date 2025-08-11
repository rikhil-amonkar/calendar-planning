import json
from itertools import permutations

def solve_puzzle():
    # Define all possible options for each category
    houses = ['1', '2', '3', '4', '5']
    names = ['Bob', 'Eric', 'Arnold', 'Alice', 'Peter']
    colors = ['blue', 'green', 'white', 'yellow', 'red']
    phones = ['huawei p50', 'samsung galaxy s21', 'oneplus 9', 'iphone 13', 'google pixel 6']
    occupations = ['artist', 'teacher', 'doctor', 'engineer', 'lawyer']
    
    # We'll represent each house as a dictionary, and the solution as a list of houses
    for name_order in permutations(names):
        for color_order in permutations(colors):
            for phone_order in permutations(phones):
                for occupation_order in permutations(occupations):
                    solution = []
                    for i in range(5):
                        house = {
                            'House': str(i+1),
                            'Name': name_order[i],
                            'Color': color_order[i],
                            'Phone': phone_order[i],
                            'Occupation': occupation_order[i]
                        }
                        solution.append(house)
                    
                    # Apply all constraints
                    # Constraint 2: Bob is in the second house
                    if solution[1]['Name'] != 'Bob':
                        continue
                    
                    # Constraint 10: Arnold is the engineer
                    # Find Arnold's house and check occupation
                    arnold_house = None
                    engineer_house = None
                    for house in solution:
                        if house['Name'] == 'Arnold':
                            arnold_house = house
                        if house['Occupation'] == 'engineer':
                            engineer_house = house
                    if arnold_house is None or engineer_house is None or arnold_house != engineer_house:
                        continue
                    
                    # Constraint 1: engineer is right of lawyer
                    lawyer_pos = -1
                    engineer_pos = -1
                    for i in range(5):
                        if solution[i]['Occupation'] == 'lawyer':
                            lawyer_pos = i
                        if solution[i]['Occupation'] == 'engineer':
                            engineer_pos = i
                    if lawyer_pos == -1 or engineer_pos == -1 or engineer_pos <= lawyer_pos:
                        continue
                    
                    # Constraint 3: samsung galaxy s21 user is doctor
                    # Constraint 4: doctor loves blue
                    for house in solution:
                        if house['Phone'] == 'samsung galaxy s21':
                            if house['Occupation'] != 'doctor':
                                break
                            if house['Color'] != 'blue':
                                break
                    else:
                        # Check that no other house is doctor or blue if not samsung
                        for house in solution:
                            if house['Occupation'] == 'doctor' and house['Phone'] != 'samsung galaxy s21':
                                break
                            if house['Color'] == 'blue' and house['Phone'] != 'samsung galaxy s21':
                                break
                        else:
                            pass
                        continue
                    continue
                    
                    # Constraint 5: green not in fifth house
                    if solution[4]['Color'] == 'green':
                        continue
                    
                    # Constraint 6: lawyer uses oneplus 9
                    for house in solution:
                        if house['Occupation'] == 'lawyer' and house['Phone'] != 'oneplus 9':
                            break
                    else:
                        # Also check that no one else uses oneplus 9
                        oneplus_count = 0
                        for house in solution:
                            if house['Phone'] == 'oneplus 9':
                                oneplus_count += 1
                        if oneplus_count != 1:
                            continue
                        pass
                    continue
                    
                    # Constraint 7: blue directly left of red
                    blue_pos = -1
                    red_pos = -1
                    for i in range(5):
                        if solution[i]['Color'] == 'blue':
                            blue_pos = i
                        if solution[i]['Color'] == 'red':
                            red_pos = i
                    if blue_pos == -1 or red_pos == -1 or red_pos != blue_pos + 1:
                        continue
                    
                    # Constraint 8: lawyer is right of samsung user (doctor)
                    samsung_pos = -1
                    lawyer_pos = -1
                    for i in range(5):
                        if solution[i]['Phone'] == 'samsung galaxy s21':
                            samsung_pos = i
                        if solution[i]['Occupation'] == 'lawyer':
                            lawyer_pos = i
                    if samsung_pos == -1 or lawyer_pos == -1 or lawyer_pos <= samsung_pos:
                        continue
                    
                    # Constraint 9: one house between google pixel 6 and huawei p50
                    google_pos = -1
                    huawei_pos = -1
                    for i in range(5):
                        if solution[i]['Phone'] == 'google pixel 6':
                            google_pos = i
                        if solution[i]['Phone'] == 'huawei p50':
                            huawei_pos = i
                    if google_pos == -1 or huawei_pos == -1 or abs(google_pos - huawei_pos) != 2:
                        continue
                    
                    # Constraint 11: Alice loves yellow
                    for house in solution:
                        if house['Name'] == 'Alice' and house['Color'] != 'yellow':
                            break
                    else:
                        # Also check that no one else loves yellow if not Alice
                        yellow_count = 0
                        for house in solution:
                            if house['Color'] == 'yellow':
                                yellow_count += 1
                        if yellow_count != 1:
                            continue
                        pass
                    continue
                    
                    # Constraint 12: google pixel 6 is Eric
                    for house in solution:
                        if house['Phone'] == 'google pixel 6' and house['Name'] != 'Eric':
                            break
                    else:
                        # Also check that no one else is Eric if not google pixel 6
                        eric_count = 0
                        for house in solution:
                            if house['Name'] == 'Eric':
                                eric_count += 1
                        if eric_count != 1:
                            continue
                        pass
                    continue
                    
                    # Constraint 13: google pixel 6 user is teacher
                    for house in solution:
                        if house['Phone'] == 'google pixel 6' and house['Occupation'] != 'teacher':
                            break
                    else:
                        # Also check that no one else is teacher if not google pixel 6
                        teacher_count = 0
                        for house in solution:
                            if house['Occupation'] == 'teacher':
                                teacher_count += 1
                        if teacher_count != 1:
                            continue
                        pass
                    continue
                    
                    # Constraint 14: red is right of teacher
                    teacher_pos = -1
                    red_pos = -1
                    for i in range(5):
                        if solution[i]['Occupation'] == 'teacher':
                            teacher_pos = i
                        if solution[i]['Color'] == 'red':
                            red_pos = i
                    if teacher_pos == -1 or red_pos == -1 or red_pos <= teacher_pos:
                        continue
                    
                    # If all constraints passed, return the solution
                    result = {
                        "solution": {
                            "header": ["House", "Name", "Color", "Phone", "Occupation"],
                            "rows": []
                        }
                    }
                    for house in solution:
                        result["solution"]["rows"].append([
                            house['House'],
                            house['Name'],
                            house['Color'],
                            house['Phone'],
                            house['Occupation']
                        ])
                    return json.dumps(result, indent=2)
    
    return json.dumps({"solution": {"header": [], "rows": []}})

print(solve_puzzle())