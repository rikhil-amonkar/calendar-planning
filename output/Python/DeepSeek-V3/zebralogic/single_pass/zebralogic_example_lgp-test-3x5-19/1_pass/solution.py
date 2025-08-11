import json
from itertools import permutations

def solve_puzzle():
    # Define all possible options for each attribute
    names = ['Arnold', 'Peter', 'Eric']
    occupations = ['doctor', 'teacher', 'engineer']
    educations = ['associate', 'high school', 'bachelor']
    smoothies = ['desert', 'cherry', 'watermelon']
    hobbies = ['gardening', 'cooking', 'photography']
    
    # Generate all possible permutations for each attribute
    for name_order in permutations(names):
        for occ_order in permutations(occupations):
            for edu_order in permutations(educations):
                for smoo_order in permutations(smoothies):
                    for hobby_order in permutations(hobbies):
                        # Create a list of houses with their attributes
                        houses = [
                            {
                                'House': '1',
                                'Name': name_order[0],
                                'Occupation': occ_order[0],
                                'Education': edu_order[0],
                                'Smoothie': smoo_order[0],
                                'Hobby': hobby_order[0]
                            },
                            {
                                'House': '2',
                                'Name': name_order[1],
                                'Occupation': occ_order[1],
                                'Education': edu_order[1],
                                'Smoothie': smoo_order[1],
                                'Hobby': hobby_order[1]
                            },
                            {
                                'House': '3',
                                'Name': name_order[2],
                                'Occupation': occ_order[2],
                                'Education': edu_order[2],
                                'Smoothie': smoo_order[2],
                                'Hobby': hobby_order[2]
                            }
                        ]
                        
                        # Check all constraints
                        # 1. The Desert smoothie lover is the person who is a doctor.
                        desert_doctor = True
                        for house in houses:
                            if house['Smoothie'] == 'desert' and house['Occupation'] != 'doctor':
                                desert_doctor = False
                                break
                        if not desert_doctor:
                            continue
                        
                        # 2. Arnold is not in the third house.
                        if houses[2]['Name'] == 'Arnold':
                            continue
                        
                        # 3. The person who likes Cherry smoothies is somewhere to the right of Peter.
                        peter_house = None
                        cherry_house = None
                        for house in houses:
                            if house['Name'] == 'Peter':
                                peter_house = int(house['House'])
                            if house['Smoothie'] == 'cherry':
                                cherry_house = int(house['House'])
                        if peter_house is None or cherry_house is None or cherry_house <= peter_house:
                            continue
                        
                        # 4. The person who loves cooking is in the second house.
                        if houses[1]['Hobby'] != 'cooking':
                            continue
                        
                        # 5. The person who loves cooking is Peter.
                        if houses[1]['Name'] != 'Peter':
                            continue
                        
                        # 6. The person with an associate's degree is somewhere to the right of the person who enjoys gardening.
                        gardening_house = None
                        associate_house = None
                        for house in houses:
                            if house['Hobby'] == 'gardening':
                                gardening_house = int(house['House'])
                            if house['Education'] == 'associate':
                                associate_house = int(house['House'])
                        if gardening_house is None or associate_house is None or associate_house <= gardening_house:
                            continue
                        
                        # 7. The person with a bachelor's degree is somewhere to the right of the Desert smoothie lover.
                        desert_house = None
                        bachelor_house = None
                        for house in houses:
                            if house['Smoothie'] == 'desert':
                                desert_house = int(house['House'])
                            if house['Education'] == 'bachelor':
                                bachelor_house = int(house['House'])
                        if desert_house is None or bachelor_house is None or bachelor_house <= desert_house:
                            continue
                        
                        # 8. The person who loves cooking is the person who is a doctor.
                        if houses[1]['Occupation'] != 'doctor':
                            continue
                        
                        # 9. The photography enthusiast is the person who is a teacher.
                        photo_teacher = True
                        for house in houses:
                            if house['Hobby'] == 'photography' and house['Occupation'] != 'teacher':
                                photo_teacher = False
                                break
                            if house['Occupation'] == 'teacher' and house['Hobby'] != 'photography':
                                photo_teacher = False
                                break
                        if not photo_teacher:
                            continue
                        
                        # If all constraints are satisfied, return the solution
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Occupation", "Education", "Smoothie", "Hobby"],
                                "rows": [
                                    [house['House'], house['Name'], house['Occupation'], house['Education'], house['Smoothie'], house['Hobby']] for house in houses
                                ]
                            }
                        }
                        return solution
    
    return {"solution": {"header": [], "rows": []}}

# Solve the puzzle and print the solution as JSON
solution = solve_puzzle()
print(json.dumps(solution, indent=2))