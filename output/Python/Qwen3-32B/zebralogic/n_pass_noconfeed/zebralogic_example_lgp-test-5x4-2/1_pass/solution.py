import itertools
import json

def solve_puzzle():
    names = ['Bob', 'Eric', 'Arnold', 'Alice', 'Peter']
    colors = ['blue', 'green', 'white', 'yellow', 'red']
    phones = ['huawei p50', 'samsung galaxy s21', 'oneplus 9', 'iphone 13', 'google pixel 6']
    occupations = ['artist', 'teacher', 'doctor', 'engineer', 'lawyer']
    
    # Generate valid name permutations where Bob is in house 2 (index 1)
    valid_names_list = []
    for p in itertools.permutations(names):
        if p[1] == 'Bob':
            valid_names_list.append(p)
    
    for valid_names in valid_names_list:
        eric_pos = valid_names.index('Eric')
        # Generate valid phone permutations where Eric uses Google Pixel 6
        valid_phone_perms = []
        for phone_p in itertools.permutations(phones):
            if phone_p[eric_pos] == 'google pixel 6':
                valid_phone_perms.append(phone_p)
        
        for phone_p in valid_phone_perms:
            # Generate valid occupation permutations where Arnold is engineer and Eric is teacher
            arnold_pos = valid_names.index('Arnold')
            eric_occ_pos = valid_names.index('Eric')
            valid_occ_perms = []
            for occ_p in itertools.permutations(occupations):
                if occ_p[arnold_pos] == 'engineer' and occ_p[eric_occ_pos] == 'teacher':
                    valid_occ_perms.append(occ_p)
            
            for occ_p in valid_occ_perms:
                # Check doctor's phone is samsung galaxy s21 and lawyer's phone is oneplus 9
                doctor_pos = occ_p.index('doctor')
                lawyer_pos = occ_p.index('lawyer')
                if phone_p[doctor_pos] != 'samsung galaxy s21':
                    continue
                if phone_p[lawyer_pos] != 'oneplus 9':
                    continue
                
                # Check clue 8: lawyer is to the right of doctor
                if lawyer_pos <= doctor_pos:
                    continue
                
                # Check clue 1: engineer (arnold_pos) is to the right of lawyer
                if arnold_pos <= lawyer_pos:
                    continue
                
                # Now process colors
                alice_pos = valid_names.index('Alice')
                for color_p in itertools.permutations(colors):
                    # Check Alice's color is yellow
                    if color_p[alice_pos] != 'yellow':
                        continue
                    # Check doctor's color is blue
                    if color_p[doctor_pos] != 'blue':
                        continue
                    # Check blue is directly left of red
                    blue_pos = color_p.index('blue')
                    if blue_pos == 4 or color_p[blue_pos + 1] != 'red':
                        continue
                    # Check green not in fifth house
                    if color_p[4] == 'green':
                        continue
                    # Check red is to the right of teacher (Eric's occupation is teacher)
                    teacher_pos = eric_occ_pos  # since Eric is teacher
                    red_pos = color_p.index('red')
                    if red_pos <= teacher_pos:
                        continue
                    
                    # Check clue 9: one house between Google Pixel 6 and Huawei P50
                    google_pixel_pos = eric_pos
                    huawei_p50_pos = phone_p.index('huawei p50')
                    if abs(huawei_p50_pos - google_pixel_pos) != 2:
                        continue
                    
                    # All constraints satisfied, build solution
                    solution_rows = []
                    for i in range(5):
                        house_num = i + 1
                        name = valid_names[i]
                        color = color_p[i]
                        phone = phone_p[i]
                        occupation = occ_p[i]
                        solution_rows.append([str(house_num), name, color, phone, occupation])
                    
                    # Output as JSON
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Color", "PhoneModel", "Occupation"],
                            "rows": solution_rows
                        }
                    }
                    print(json.dumps(solution))
                    return  # Return after first solution found

solve_puzzle()