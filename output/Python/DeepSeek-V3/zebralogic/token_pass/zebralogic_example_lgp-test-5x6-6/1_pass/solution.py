import json
from itertools import permutations

def solve():
    # Define all possible values for each category
    names = ["Arnold", "Eric", "Alice", "Bob", "Peter"]
    vacations = ["mountain", "city", "cruise", "beach", "camping"]
    educations = ["doctorate", "high school", "bachelor", "associate", "master"]
    colors = ["blue", "red", "white", "yellow", "green"]
    phones = ["google pixel 6", "iphone 13", "oneplus 9", "huawei p50", "samsung galaxy s21"]
    foods = ["grilled cheese", "stir fry", "pizza", "spaghetti", "stew"]
    
    houses = [1, 2, 3, 4, 5]
    
    # Try all permutations (brute force with pruning)
    for name_perm in permutations(names):
        for vac_perm in permutations(vacations):
            for edu_perm in permutations(educations):
                for col_perm in permutations(colors):
                    for phone_perm in permutations(phones):
                        for food_perm in permutations(foods):
                            # Create assignment dictionaries
                            assignment = {}
                            for i in range(5):
                                assignment[i] = {
                                    'house': i+1,
                                    'name': name_perm[i],
                                    'vacation': vac_perm[i],
                                    'education': edu_perm[i],
                                    'color': col_perm[i],
                                    'phone': phone_perm[i],
                                    'food': food_perm[i]
                                }
                            
                            # Check all clues
                            # 1. The person who loves the stew is not in the first house.
                            if assignment[0]['food'] == 'stew':
                                continue
                            
                            # 2. There are two houses between the person who loves stir fry and the person with an associate's degree.
                            stir_fry_house = None
                            associate_house = None
                            for i in range(5):
                                if assignment[i]['food'] == 'stir fry':
                                    stir_fry_house = i+1
                                if assignment[i]['education'] == 'associate':
                                    associate_house = i+1
                            if stir_fry_house is None or associate_house is None:
                                continue
                            if abs(stir_fry_house - associate_house) != 3:
                                continue
                            
                            # 3. The person who enjoys mountain retreats is the person with a bachelor's degree.
                            for i in range(5):
                                if assignment[i]['vacation'] == 'mountain' and assignment[i]['education'] != 'bachelor':
                                    break
                                if assignment[i]['education'] == 'bachelor' and assignment[i]['vacation'] != 'mountain':
                                    break
                            else:
                                pass  # All good
                            else:
                                continue
                            
                            # 4. The person with a doctorate is somewhere to the right of Bob.
                            bob_house = None
                            doctorate_house = None
                            for i in range(5):
                                if assignment[i]['name'] == 'Bob':
                                    bob_house = i+1
                                if assignment[i]['education'] == 'doctorate':
                                    doctorate_house = i+1
                            if bob_house is None or doctorate_house is None:
                                continue
                            if not doctorate_house > bob_house:
                                continue
                            
                            # 5. The person who uses a Samsung Galaxy S21 is in the third house.
                            if assignment[2]['phone'] != 'samsung galaxy s21':
                                continue
                            
                            # 6. Eric is the person with a doctorate.
                            for i in range(5):
                                if assignment[i]['name'] == 'Eric' and assignment[i]['education'] != 'doctorate':
                                    break
                                if assignment[i]['education'] == 'doctorate' and assignment[i]['name'] != 'Eric':
                                    break
                            else:
                                pass
                            else:
                                continue
                            
                            # 7. The person with a doctorate is in the third house.
                            if assignment[2]['education'] != 'doctorate':
                                continue
                            
                            # 8. The person who loves stir fry is the person with a bachelor's degree.
                            for i in range(5):
                                if assignment[i]['food'] == 'stir fry' and assignment[i]['education'] != 'bachelor':
                                    break
                                if assignment[i]['education'] == 'bachelor' and assignment[i]['food'] != 'stir fry':
                                    break
                            else:
                                pass
                            else:
                                continue
                            
                            # 9. The person with a doctorate is the person who is a pizza lover.
                            if assignment[2]['food'] != 'pizza':
                                continue
                            
                            # 10. The person whose favorite color is green is somewhere to the right of Peter.
                            peter_house = None
                            green_house = None
                            for i in range(5):
                                if assignment[i]['name'] == 'Peter':
                                    peter_house = i+1
                                if assignment[i]['color'] == 'green':
                                    green_house = i+1
                            if peter_house is None or green_house is None:
                                continue
                            if not green_house > peter_house:
                                continue
                            
                            # 11. The person who enjoys camping trips is the person who uses an iPhone 13.
                            for i in range(5):
                                if assignment[i]['vacation'] == 'camping' and assignment[i]['phone'] != 'iphone 13':
                                    break
                                if assignment[i]['phone'] == 'iphone 13' and assignment[i]['vacation'] != 'camping':
                                    break
                            else:
                                pass
                            else:
                                continue
                            
                            # 12. The person who likes going on cruises is Alice.
                            for i in range(5):
                                if assignment[i]['name'] == 'Alice' and assignment[i]['vacation'] != 'cruise':
                                    break
                                if assignment[i]['vacation'] == 'cruise' and assignment[i]['name'] != 'Alice':
                                    break
                            else:
                                pass
                            else:
                                continue
                            
                            # 13. There is one house between the person with a high school diploma and the person who uses a Samsung Galaxy S21.
                            high_school_house = None
                            for i in range(5):
                                if assignment[i]['education'] == 'high school':
                                    high_school_house = i+1
                            if high_school_house is None:
                                continue
                            if abs(high_school_house - 3) != 2:  # Samsung is house 3
                                continue
                            
                            # 14. The person who uses a Google Pixel 6 is Arnold.
                            for i in range(5):
                                if assignment[i]['name'] == 'Arnold' and assignment[i]['phone'] != 'google pixel 6':
                                    break
                                if assignment[i]['phone'] == 'google pixel 6' and assignment[i]['name'] != 'Arnold':
                                    break
                            else:
                                pass
                            else:
                                continue
                            
                            # 15. The person who uses a OnePlus 9 is somewhere to the right of the person who uses a Huawei P50.
                            huawei_house = None
                            oneplus_house = None
                            for i in range(5):
                                if assignment[i]['phone'] == 'huawei p50':
                                    huawei_house = i+1
                                if assignment[i]['phone'] == 'oneplus 9':
                                    oneplus_house = i+1
                            if huawei_house is None or oneplus_house is None:
                                continue
                            if not oneplus_house > huawei_house:
                                continue
                            
                            # 16. Arnold is the person who loves eating grilled cheese.
                            for i in range(5):
                                if assignment[i]['name'] == 'Arnold' and assignment[i]['food'] != 'grilled cheese':
                                    break
                                if assignment[i]['food'] == 'grilled cheese' and assignment[i]['name'] != 'Arnold':
                                    break
                            else:
                                pass
                            else:
                                continue
                            
                            # 17. The person who loves eating grilled cheese is not in the fourth house.
                            if assignment[3]['food'] == 'grilled cheese':
                                continue
                            
                            # 18. There are two houses between the person with a bachelor's degree and the person whose favorite color is red.
                            bachelor_house = None
                            red_house = None
                            for i in range(5):
                                if assignment[i]['education'] == 'bachelor':
                                    bachelor_house = i+1
                                if assignment[i]['color'] == 'red':
                                    red_house = i+1
                            if bachelor_house is None or red_house is None:
                                continue
                            if abs(bachelor_house - red_house) != 3:
                                continue
                            
                            # 19. The person who loves beach vacations is somewhere to the right of the person who prefers city breaks.
                            city_house = None
                            beach_house = None
                            for i in range(5):
                                if assignment[i]['vacation'] == 'city':
                                    city_house = i+1
                                if assignment[i]['vacation'] == 'beach':
                                    beach_house = i+1
                            if city_house is None or beach_house is None:
                                continue
                            if not beach_house > city_house:
                                continue
                            
                            # 20. The person whose favorite color is green is not in the second house.
                            if assignment[1]['color'] == 'green':
                                continue
                            
                            # 21. The person who loves blue is somewhere to the right of Peter.
                            blue_house = None
                            for i in range(5):
                                if assignment[i]['color'] == 'blue':
                                    blue_house = i+1
                            if blue_house is None:
                                continue
                            if not blue_house > peter_house:
                                continue
                            
                            # 22. There is one house between the person who enjoys camping trips and the person who loves yellow.
                            camping_house = None
                            yellow_house = None
                            for i in range(5):
                                if assignment[i]['vacation'] == 'camping':
                                    camping_house = i+1
                                if assignment[i]['color'] == 'yellow':
                                    yellow_house = i+1
                            if camping_house is None or yellow_house is None:
                                continue
                            if abs(camping_house - yellow_house) != 2:
                                continue
                            
                            # All constraints satisfied
                            # Prepare result
                            result = {
                                "solution": {
                                    "header": ["House", "Name", "Vacation", "Education", "Color", "PhoneModel", "Food"],
                                    "rows": []
                                }
                            }
                            
                            for i in range(5):
                                row = [
                                    str(i+1),
                                    assignment[i]['name'],
                                    assignment[i]['vacation'],
                                    assignment[i]['education'],
                                    assignment[i]['color'],
                                    assignment[i]['phone'],
                                    assignment[i]['food']
                                ]
                                result["solution"]["rows"].append(row)
                            
                            return result
    
    return None

if __name__ == "__main__":
    solution = solve()
    if solution:
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"error": "No solution found"}, indent=2))