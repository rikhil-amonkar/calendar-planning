import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    houses = ['1', '2', '3']
    names = ['Arnold', 'Peter', 'Eric']
    occupations = ['doctor', 'teacher', 'engineer']
    educations = ['associate', 'high school', 'bachelor']
    smoothies = ['desert', 'cherry', 'watermelon']
    hobbies = ['gardening', 'cooking', 'photography']  # Note: 'gardening' is misspelled in the problem as 'gardening' but 'gardening' in the output
    
    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for occ_perm in permutations(occupations):
            for edu_perm in permutations(educations):
                for sm_perm in permutations(smoothies):
                    for hobby_perm in permutations(hobbies):
                        # Assign to houses
                        solution = {
                            '1': {
                                'Name': name_perm[0],
                                'Occupation': occ_perm[0],
                                'Education': edu_perm[0],
                                'Smoothie': sm_perm[0],
                                'Hobby': hobby_perm[0]
                            },
                            '2': {
                                'Name': name_perm[1],
                                'Occupation': occ_perm[1],
                                'Education': edu_perm[1],
                                'Smoothie': sm_perm[1],
                                'Hobby': hobby_perm[1]
                            },
                            '3': {
                                'Name': name_perm[2],
                                'Occupation': occ_perm[2],
                                'Education': edu_perm[2],
                                'Smoothie': sm_perm[2],
                                'Hobby': hobby_perm[2]
                            }
                        }
                        
                        # Check constraints
                        # 1. The Desert smoothie lover is the person who is a doctor.
                        desert_doctor = False
                        for house in solution:
                            if solution[house]['Smoothie'] == 'desert' and solution[house]['Occupation'] == 'doctor':
                                desert_doctor = True
                        if not desert_doctor:
                            continue
                        
                        # 2. Arnold is not in the third house.
                        if solution['3']['Name'] == 'Arnold':
                            continue
                        
                        # 3. The person who likes Cherry smoothies is somewhere to the right of Peter.
                        peter_house = None
                        cherry_house = None
                        for house in solution:
                            if solution[house]['Name'] == 'Peter':
                                peter_house = house
                            if solution[house]['Smoothie'] == 'cherry':
                                cherry_house = house
                        if peter_house is None or cherry_house is None or int(cherry_house) <= int(peter_house):
                            continue
                        
                        # 4. The person who loves cooking is in the second house.
                        if solution['2']['Hobby'] != 'cooking':
                            continue
                        
                        # 5. The person who loves cooking is Peter.
                        if solution['2']['Name'] != 'Peter':
                            continue
                        
                        # 6. The person with an associate's degree is somewhere to the right of the person who enjoys gardening.
                        gardening_house = None
                        associate_house = None
                        for house in solution:
                            if solution[house]['Hobby'] == 'gardening':
                                gardening_house = house
                            if solution[house]['Education'] == 'associate':
                                associate_house = house
                        if gardening_house is None or associate_house is None or int(associate_house) <= int(gardening_house):
                            continue
                        
                        # 7. The person with a bachelor's degree is somewhere to the right of the Desert smoothie lover.
                        desert_house = None
                        bachelor_house = None
                        for house in solution:
                            if solution[house]['Smoothie'] == 'desert':
                                desert_house = house
                            if solution[house]['Education'] == 'bachelor':
                                bachelor_house = house
                        if desert_house is None or bachelor_house is None or int(bachelor_house) <= int(desert_house):
                            continue
                        
                        # 8. The person who loves cooking is the person who is a doctor.
                        if solution['2']['Occupation'] != 'doctor':
                            continue
                        
                        # 9. The photography enthusiast is the person who is a teacher.
                        photo_teacher = False
                        for house in solution:
                            if solution[house]['Hobby'] == 'photography' and solution[house]['Occupation'] == 'teacher':
                                photo_teacher = True
                        if not photo_teacher:
                            continue
                        
                        # If all constraints are satisfied, return the solution
                        result = {
                            "solution": {
                                "header": ["House", "Name", "Occupation", "Education", "Smoothie", "Hobby"],
                                "rows": [
                                    ["1", solution['1']['Name'], solution['1']['Occupation'], solution['1']['Education'], solution['1']['Smoothie'], solution['1']['Hobby']],
                                    ["2", solution['2']['Name'], solution['2']['Occupation'], solution['2']['Education'], solution['2']['Smoothie'], solution['2']['Hobby']],
                                    ["3", solution['3']['Name'], solution['3']['Occupation'], solution['3']['Education'], solution['3']['Smoothie'], solution['3']['Hobby']]
                                ]
                            }
                        }
                        return json.dumps(result, indent=2)
    
    return json.dumps({"solution": {"header": [], "rows": []}})

print(solve_puzzle())