import itertools
import json

# Define all possible attributes
names = ['Arnold', 'Eric', 'Alice', 'Bob', 'Peter']
vacations = ['mountain', 'city', 'cruise', 'beach', 'camping']
educations = ['doctorate', 'high school', 'bachelor', 'associate', 'master']
colors = ['blue', 'red', 'white', 'yellow', 'green']
phones = ['google pixel 6', 'iphone 13', 'oneplus 9', 'huawei p50', 'samsung galaxy s21']
foods = ['grilled cheese', 'stir fry', 'pizza', 'spaghetti', 'stew']

# Known values for house 3 (index 2)
houses = [{} for _ in range(5)]
houses[2]['name'] = 'Eric'
houses[2]['education'] = 'doctorate'
houses[2]['food'] = 'pizza'
houses[2]['phone'] = 'samsung galaxy s21'

# Generate all possible name permutations (excluding Eric in house 3)
remaining_names = ['Arnold', 'Alice', 'Bob', 'Peter']
name_indices = [0, 1, 3, 4]  # houses 0,1,3,4 (1,2,4,5 in the puzzle)

for name_perm in itertools.permutations(remaining_names):
    # Assign names to the houses
    houses = [{} for _ in range(5)]
    houses[2]['name'] = 'Eric'
    for i, idx in enumerate(name_indices):
        houses[idx]['name'] = name_perm[i]
    
    # Generate all possible education permutations (excluding doctorate in house 3)
    remaining_educations = ['high school', 'bachelor', 'associate', 'master']
    for edu_perm in itertools.permutations(remaining_educations):
        for i, idx in enumerate(name_indices):
            houses[idx]['education'] = edu_perm[i]
        
        # Check if bachelor and associate are properly positioned
        bachelor_idx = -1
        associate_idx = -1
        for i in name_indices:
            if houses[i]['education'] == 'bachelor':
                bachelor_idx = i
            if houses[i]['education'] == 'associate':
                associate_idx = i
        if bachelor_idx == -1 or associate_idx == -1:
            continue
        if abs(bachelor_idx - associate_idx) != 3:
            continue
        
        # Generate all possible food permutations (excluding pizza in house 3)
        remaining_foods = ['grilled cheese', 'stir fry', 'spaghetti', 'stew']
        for food_perm in itertools.permutations(remaining_foods):
            for i, idx in enumerate(name_indices):
                houses[idx]['food'] = food_perm[i]
            
            # Check if bachelor's food is stir fry
            if houses[bachelor_idx]['food'] != 'stir fry':
                continue
            
            # Generate all possible phone permutations (excluding samsung in house 3)
            remaining_phones = ['google pixel 6', 'iphone 13', 'oneplus 9', 'huawei p50']
            for phone_perm in itertools.permutations(remaining_phones):
                for i, idx in enumerate(name_indices):
                    houses[idx]['phone'] = phone_perm[i]
                
                # Check Arnold's phone and food
                arnold_idx = -1
                for i in name_indices:
                    if houses[i]['name'] == 'Arnold':
                        arnold_idx = i
                        break
                if arnold_idx == -1:
                    continue
                if houses[arnold_idx]['phone'] != 'google pixel 6':
                    continue
                if houses[arnold_idx]['food'] != 'grilled cheese':
                    continue
                if houses[4]['food'] == 'grilled cheese':
                    continue
                
                # Generate all possible vacation permutations
                for vac_perm in itertools.permutations(vacations):
                    for i in range(5):
                        houses[i]['vacation'] = vac_perm[i]
                    
                    # Check Alice's vacation is cruise
                    alice_idx = -1
                    for i in range(5):
                        if houses[i]['name'] == 'Alice':
                            alice_idx = i
                            break
                    if alice_idx == -1:
                        continue
                    if houses[alice_idx]['vacation'] != 'cruise':
                        continue
                    
                    # Check bachelor's vacation is mountain
                    if houses[bachelor_idx]['vacation'] != 'mountain':
                        continue
                    
                    # Check camping and iPhone 13
                    camping_idx = -1
                    for i in range(5):
                        if houses[i]['vacation'] == 'camping':
                            camping_idx = i
                            break
                    if camping_idx == -1:
                        continue
                    if houses[camping_idx]['phone'] != 'iphone 13':
                        continue
                    
                    # Check beach is to the right of city
                    city_idx = -1
                    beach_idx = -1
                    for i in range(5):
                        if houses[i]['vacation'] == 'city':
                            city_idx = i
                        if houses[i]['vacation'] == 'beach':
                            beach_idx = i
                    if city_idx == -1 or beach_idx == -1 or beach_idx <= city_idx:
                        continue
                    
                    # Check stew is not in house 1 (index 0)
                    if houses[0]['food'] == 'stew':
                        continue
                    
                    # Generate all possible color permutations
                    for color_perm in itertools.permutations(colors):
                        for i in range(5):
                            houses[i]['color'] = color_perm[i]
                        
                        # Check green is to the right of Peter
                        peter_idx = -1
                        for i in range(5):
                            if houses[i]['name'] == 'Peter':
                                peter_idx = i
                                break
                        if peter_idx == -1:
                            continue
                        green_idx = -1
                        for i in range(5):
                            if houses[i]['color'] == 'green':
                                green_idx = i
                                break
                        if green_idx == -1 or green_idx <= peter_idx:
                            continue
                        
                        # Check green is not in house 2 (index 2)
                        if green_idx == 2:
                            continue
                        
                        # Check blue is to the right of Peter
                        blue_idx = -1
                        for i in range(5):
                            if houses[i]['color'] == 'blue':
                                blue_idx = i
                                break
                        if blue_idx == -1 or blue_idx <= peter_idx:
                            continue
                        
                        # Check two houses between bachelor and red
                        red_idx = -1
                        for i in range(5):
                            if houses[i]['color'] == 'red':
                                red_idx = i
                                break
                        if red_idx == -1 or abs(bachelor_idx - red_idx) != 3:
                            continue
                        
                        # Check one house between camping and yellow
                        yellow_idx = -1
                        for i in range(5):
                            if houses[i]['color'] == 'yellow':
                                yellow_idx = i
                                break
                        if yellow_idx == -1 or abs(camping_idx - yellow_idx) != 2:
                            continue
                        
                        # Check Bob is to the left of Eric (house 3)
                        bob_idx = -1
                        for i in range(5):
                            if houses[i]['name'] == 'Bob':
                                bob_idx = i
                                break
                        if bob_idx == -1 or bob_idx >= 2:
                            continue
                        
                        # Check high school and Samsung are one house apart
                        high_school_idx = -1
                        for i in range(5):
                            if houses[i]['education'] == 'high school':
                                high_school_idx = i
                                break
                        if high_school_idx == -1 or abs(high_school_idx - 2) != 2:
                            continue
                        
                        # Check OnePlus 9 is to the right of Huawei P50
                        huawei_idx = -1
                        oneplus_idx = -1
                        for i in range(5):
                            if houses[i]['phone'] == 'huawei p50':
                                huawei_idx = i
                            if houses[i]['phone'] == 'oneplus 9':
                                oneplus_idx = i
                        if huawei_idx == -1 or oneplus_idx == -1 or oneplus_idx <= huawei_idx:
                            continue
                        
                        # All constraints satisfied
                        solution = []
                        for i in range(5):
                            house_num = i + 1
                            name = houses[i]['name']
                            vacation = houses[i]['vacation']
                            education = houses[i]['education']
                            color = houses[i]['color']
                            phone = houses[i]['phone']
                            food = houses[i]['food']
                            solution.append([str(house_num), name, vacation, education, color, phone, food])
                        
                        print(json.dumps({
                            "solution": {
                                "header": ["House", "Name", "Vacation", "Education", "Color", "PhoneModel", "Food"],
                                "rows": solution
                            }
                        }))
                        exit()