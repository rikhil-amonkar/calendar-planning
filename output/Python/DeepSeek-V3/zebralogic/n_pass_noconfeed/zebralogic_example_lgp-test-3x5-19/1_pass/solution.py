import json
from itertools import permutations

def main():
    # Define all possible values for each category
    names = ['Arnold', 'Peter', 'Eric']
    occupations = ['doctor', 'teacher', 'engineer']
    educations = ['associate', 'high school', 'bachelor']
    smoothies = ['desert', 'cherry', 'watermelon']
    hobbies = ['gardening', 'cooking', 'photography']
    
    houses = [1, 2, 3]
    
    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for occ_perm in permutations(occupations):
            for edu_perm in permutations(educations):
                for smo_perm in permutations(smoothies):
                    for hob_perm in permutations(hobbies):
                        # Create assignment for each house
                        assignment = []
                        for i in range(3):
                            house = {
                                'House': str(i+1),
                                'Name': name_perm[i],
                                'Occupation': occ_perm[i],
                                'Education': edu_perm[i],
                                'Smoothie': smo_perm[i],
                                'Hobby': hob_perm[i]
                            }
                            assignment.append(house)
                        
                        # Check all constraints
                        valid = True
                        
                        # Clue 1: The Desert smoothie lover is the person who is a doctor.
                        desert_smoothie_drinker = None
                        doctor_person = None
                        for house in assignment:
                            if house['Smoothie'] == 'desert':
                                desert_smoothie_drinker = house
                            if house['Occupation'] == 'doctor':
                                doctor_person = house
                        if desert_smoothie_drinker != doctor_person:
                            valid = False
                        
                        # Clue 2: Arnold is not in the third house.
                        if assignment[2]['Name'] == 'Arnold':
                            valid = False
                        
                        # Clue 3: The person who likes Cherry smoothies is somewhere to the right of Peter.
                        peter_house = None
                        cherry_house = None
                        for house in assignment:
                            if house['Name'] == 'Peter':
                                peter_house = int(house['House'])
                            if house['Smoothie'] == 'cherry':
                                cherry_house = int(house['House'])
                        if peter_house is not None and cherry_house is not None:
                            if cherry_house <= peter_house:
                                valid = False
                        
                        # Clue 4: The person who loves cooking is in the second house.
                        if assignment[1]['Hobby'] != 'cooking':
                            valid = False
                        
                        # Clue 5: The person who loves cooking is Peter.
                        cooking_person = None
                        for house in assignment:
                            if house['Hobby'] == 'cooking':
                                cooking_person = house
                        if cooking_person is None or cooking_person['Name'] != 'Peter':
                            valid = False
                        
                        # Clue 6: The person with an associate's degree is somewhere to the right of the person who enjoys gardening.
                        associate_house = None
                        gardening_house = None
                        for house in assignment:
                            if house['Education'] == 'associate':
                                associate_house = int(house['House'])
                            if house['Hobby'] == 'gardening':
                                gardening_house = int(house['House'])
                        if associate_house is not None and gardening_house is not None:
                            if associate_house <= gardening_house:
                                valid = False
                        
                        # Clue 7: The person with a bachelor's degree is somewhere to the right of the Desert smoothie lover.
                        bachelor_house = None
                        desert_house = None
                        for house in assignment:
                            if house['Education'] == 'bachelor':
                                bachelor_house = int(house['House'])
                            if house['Smoothie'] == 'desert':
                                desert_house = int(house['House'])
                        if bachelor_house is not None and desert_house is not None:
                            if bachelor_house <= desert_house:
                                valid = False
                        
                        # Clue 8: The person who loves cooking is the person who is a doctor.
                        if cooking_person is None or cooking_person['Occupation'] != 'doctor':
                            valid = False
                        
                        # Clue 9: The photography enthusiast is the person who is a teacher.
                        photography_person = None
                        teacher_person = None
                        for house in assignment:
                            if house['Hobby'] == 'photography':
                                photography_person = house
                            if house['Occupation'] == 'teacher':
                                teacher_person = house
                        if photography_person != teacher_person:
                            valid = False
                        
                        if valid:
                            # Format the solution
                            header = ["House", "Name", "Occupation", "Education", "Smoothie", "Hobby"]
                            rows = []
                            for house in sorted(assignment, key=lambda x: int(x['House'])):
                                row = [
                                    house['House'],
                                    house['Name'],
                                    house['Occupation'],
                                    house['Education'],
                                    house['Smoothie'],
                                    house['Hobby']
                                ]
                                rows.append(row)
                            
                            result = {
                                "solution": {
                                    "header": header,
                                    "rows": rows
                                }
                            }
                            
                            print(json.dumps(result, indent=2))
                            return
    
    print('{"solution": {"header": [], "rows": []}}')

if __name__ == "__main__":
    main()