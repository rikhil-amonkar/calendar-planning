import json
from itertools import permutations

def main():
    fixed_names = ['Arnold', 'Peter', 'Eric']
    fixed_smoothies = ['watermelon', 'desert', 'cherry']
    
    occupations_options = [
        ['teacher', 'doctor', 'engineer'],
        ['engineer', 'doctor', 'teacher']
    ]
    
    hobbies_options = [
        ['gardening', 'cooking', 'photography'],
        ['photography', 'cooking', 'gardening']
    ]
    
    educations_list = ['associate', 'high school', 'bachelor']
    educations_options = list(permutations(educations_list))
    
    found = False
    sol_occupations = None
    sol_hobbies = None
    sol_educations = None
    
    for occupations in occupations_options:
        for hobbies in hobbies_options:
            for edu_tuple in educations_options:
                educations = list(edu_tuple)
                
                if educations[2] != 'bachelor':
                    continue
                
                gardening_index = None
                for idx, hobby_val in enumerate(hobbies):
                    if hobby_val == 'gardening':
                        gardening_index = idx
                if gardening_index is None:
                    continue
                    
                associate_index = None
                for idx, edu_val in enumerate(educations):
                    if edu_val == 'associate':
                        associate_index = idx
                if associate_index is None:
                    continue
                    
                if associate_index <= gardening_index:
                    continue
                
                photo_index = None
                for idx, hobby_val in enumerate(hobbies):
                    if hobby_val == 'photography':
                        photo_index = idx
                teacher_index = None
                for idx, occ_val in enumerate(occupations):
                    if occ_val == 'teacher':
                        teacher_index = idx
                if photo_index is None or teacher_index is None:
                    continue
                if photo_index != teacher_index:
                    continue
                
                found = True
                sol_occupations = occupations
                sol_hobbies = hobbies
                sol_educations = educations
                break
            if found:
                break
        if found:
            break
            
    if not found:
        result = {"solution": {"header": [], "rows": []}}
    else:
        rows = []
        for i in range(3):
            house_number = str(i + 1)
            row = [
                house_number,
                fixed_names[i],
                sol_occupations[i],
                sol_educations[i],
                fixed_smoothies[i],
                sol_hobbies[i]
            ]
            rows.append(row)
        
        result = {
            "solution": {
                "header": ["House", "Name", "Occupation", "Education", "Smoothie", "Hobby"],
                "rows": rows
            }
        }
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()