import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values for each category
    names = ['Bob', 'Eric', 'Arnold', 'Alice', 'Peter']
    colors = ['blue', 'green', 'white', 'yellow', 'red']
    phones = ['huawei p50', 'samsung galaxy s21', 'oneplus 9', 'iphone 13', 'google pixel 6']
    occupations = ['artist', 'teacher', 'doctor', 'engineer', 'lawyer']
    
    # We'll represent each house as a dictionary with keys: name, color, phone, occupation
    # Initialize all possibilities
    for name_order in permutations(names):
        # Check Bob is in house 2 (clue 2)
        if name_order[1] != 'Bob':
            continue
        
        for color_order in permutations(colors):
            # Check Alice loves yellow (clue 11)
            if 'Alice' in name_order:
                alice_index = name_order.index('Alice')
                if color_order[alice_index] != 'yellow':
                    continue
            
            for phone_order in permutations(phones):
                # Check Eric uses google pixel 6 (clue 12)
                if 'Eric' in name_order:
                    eric_index = name_order.index('Eric')
                    if phone_order[eric_index] != 'google pixel 6':
                        continue
                
                # Check google pixel 6 user is teacher (clue 13)
                if 'google pixel 6' in phone_order:
                    teacher_index = phone_order.index('google pixel 6')
                    if occupations[teacher_index] != 'teacher':
                        continue
                
                # Check one house between google pixel 6 and huawei p50 (clue 9)
                if 'google pixel 6' in phone_order and 'huawei p50' in phone_order:
                    gp_index = phone_order.index('google pixel 6')
                    hw_index = phone_order.index('huawei p50')
                    if abs(gp_index - hw_index) != 2:
                        continue
                
                for occupation_order in permutations(occupations):
                    # Check Arnold is engineer (clue 10)
                    if 'Arnold' in name_order:
                        arnold_index = name_order.index('Arnold')
                        if occupation_order[arnold_index] != 'engineer':
                            continue
                    
                    # Check engineer is right of lawyer (clue 1)
                    if 'engineer' in occupation_order and 'lawyer' in occupation_order:
                        engineer_index = occupation_order.index('engineer')
                        lawyer_index = occupation_order.index('lawyer')
                        if engineer_index <= lawyer_index:
                            continue
                    
                    # Check lawyer uses oneplus 9 (clue 6)
                    if 'lawyer' in occupation_order:
                        lawyer_index = occupation_order.index('lawyer')
                        if phone_order[lawyer_index] != 'oneplus 9':
                            continue
                    
                    # Check samsung galaxy s21 user is doctor (clue 3)
                    if 'samsung galaxy s21' in phone_order:
                        doctor_index = phone_order.index('samsung galaxy s21')
                        if occupation_order[doctor_index] != 'doctor':
                            continue
                    
                    # Check doctor loves blue (clue 4)
                    if 'doctor' in occupation_order:
                        doctor_index = occupation_order.index('doctor')
                        if color_order[doctor_index] != 'blue':
                            continue
                    
                    # Check blue is directly left of red (clue 7)
                    if 'blue' in color_order:
                        blue_index = color_order.index('blue')
                        if blue_index == 4 or color_order[blue_index + 1] != 'red':
                            continue
                    
                    # Check lawyer is right of samsung galaxy s21 user (clue 8)
                    if 'lawyer' in occupation_order and 'samsung galaxy s21' in phone_order:
                        lawyer_index = occupation_order.index('lawyer')
                        samsung_index = phone_order.index('samsung galaxy s21')
                        if lawyer_index <= samsung_index:
                            continue
                    
                    # Check green not in house 5 (clue 5)
                    if color_order[4] == 'green':
                        continue
                    
                    # Check red is right of teacher (clue 14)
                    if 'red' in color_order and 'teacher' in occupation_order:
                        red_index = color_order.index('red')
                        teacher_index = occupation_order.index('teacher')
                        if red_index <= teacher_index:
                            continue
                    
                    # If all checks passed, construct the solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Color", "PhoneModel", "Occupation"],
                            "rows": []
                        }
                    }
                    for i in range(5):
                        solution["solution"]["rows"].append([
                            str(i+1),
                            name_order[i],
                            color_order[i],
                            phone_order[i],
                            occupation_order[i]
                        ])
                    return json.dumps(solution, indent=2)
    
    return json.dumps({"solution": {"header": [], "rows": []}})

print(solve_puzzle())