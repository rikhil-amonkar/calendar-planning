import json
from itertools import permutations

def main():
    # Define all possible values for each category
    names = ['Arnold', 'Alice', 'Eric', 'Peter']
    hobbies = ['cooking', 'painting', 'photography', 'gardening']
    birthdays = ['april', 'jan', 'sept', 'feb']
    educations = ['master', 'bachelor', 'associate', 'high school']
    smoothies = ['cherry', 'watermelon', 'desert', 'dragonfruit']
    
    houses = [1, 2, 3, 4]
    
    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for hobby_perm in permutations(hobbies):
            for bday_perm in permutations(birthdays):
                for edu_perm in permutations(educations):
                    for smoothie_perm in permutations(smoothies):
                        # Create assignment for each house
                        assignment = {}
                        for i, house in enumerate(houses):
                            assignment[house] = {
                                'name': name_perm[i],
                                'hobby': hobby_perm[i],
                                'birthday': bday_perm[i],
                                'education': edu_perm[i],
                                'smoothie': smoothie_perm[i]
                            }
                        
                        # Check all constraints
                        valid = True
                        
                        # Clue 1: The Desert smoothie lover is the person whose birthday is in January.
                        desert_smoothie_house = None
                        jan_bday_house = None
                        for house, attrs in assignment.items():
                            if attrs['smoothie'] == 'desert':
                                desert_smoothie_house = house
                            if attrs['birthday'] == 'jan':
                                jan_bday_house = house
                        if desert_smoothie_house != jan_bday_house:
                            valid = False
                            continue
                        
                        # Clue 2: Eric is the person with a bachelor's degree.
                        eric_house = None
                        bachelor_house = None
                        for house, attrs in assignment.items():
                            if attrs['name'] == 'Eric':
                                eric_house = house
                            if attrs['education'] == 'bachelor':
                                bachelor_house = house
                        if eric_house != bachelor_house:
                            valid = False
                            continue
                        
                        # Clue 3: The person whose birthday is in January is the person with a bachelor's degree.
                        if jan_bday_house != bachelor_house:
                            valid = False
                            continue
                        
                        # Clue 4: The person with a high school diploma is in the third house.
                        if assignment[3]['education'] != 'high school':
                            valid = False
                            continue
                        
                        # Clue 5: The Watermelon smoothie lover is not in the third house.
                        if assignment[3]['smoothie'] == 'watermelon':
                            valid = False
                            continue
                        
                        # Clue 6: The person with an associate's degree is Arnold.
                        arnold_house = None
                        associate_house = None
                        for house, attrs in assignment.items():
                            if attrs['name'] == 'Arnold':
                                arnold_house = house
                            if attrs['education'] == 'associate':
                                associate_house = house
                        if arnold_house != associate_house:
                            valid = False
                            continue
                        
                        # Clue 7: The person with a master's degree is the person who paints as a hobby.
                        master_house = None
                        painting_house = None
                        for house, attrs in assignment.items():
                            if attrs['education'] == 'master':
                                master_house = house
                            if attrs['hobby'] == 'painting':
                                painting_house = house
                        if master_house != painting_house:
                            valid = False
                            continue
                        
                        # Clue 8: There is one house between the Dragonfruit smoothie lover and the person whose birthday is in September.
                        dragonfruit_house = None
                        sept_bday_house = None
                        for house, attrs in assignment.items():
                            if attrs['smoothie'] == 'dragonfruit':
                                dragonfruit_house = house
                            if attrs['birthday'] == 'sept':
                                sept_bday_house = house
                        if abs(dragonfruit_house - sept_bday_house) != 2:
                            valid = False
                            continue
                        
                        # Clue 9: The person with a high school diploma is the person whose birthday is in September.
                        if assignment[3]['birthday'] != 'sept':
                            valid = False
                            continue
                        
                        # Clue 10: The person who loves cooking is Alice.
                        cooking_house = None
                        alice_house = None
                        for house, attrs in assignment.items():
                            if attrs['hobby'] == 'cooking':
                                cooking_house = house
                            if attrs['name'] == 'Alice':
                                alice_house = house
                        if cooking_house != alice_house:
                            valid = False
                            continue
                        
                        # Clue 11: The person whose birthday is in April and the person who enjoys gardening are next to each other.
                        april_bday_house = None
                        gardening_house = None
                        for house, attrs in assignment.items():
                            if attrs['birthday'] == 'april':
                                april_bday_house = house
                            if attrs['hobby'] == 'gardening':
                                gardening_house = house
                        if abs(april_bday_house - gardening_house) != 1:
                            valid = False
                            continue
                        
                        # Clue 12: The person who paints as a hobby is the person whose birthday is in February.
                        if assignment[master_house]['birthday'] != 'feb':
                            valid = False
                            continue
                        
                        if valid:
                            # Format the solution
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Hobby", "Birthday", "Education", "Smoothie"],
                                    "rows": []
                                }
                            }
                            
                            for house in sorted(assignment.keys()):
                                attrs = assignment[house]
                                row = [
                                    str(house),
                                    attrs['name'],
                                    attrs['hobby'],
                                    attrs['birthday'],
                                    attrs['education'],
                                    attrs['smoothie']
                                ]
                                solution["solution"]["rows"].append(row)
                            
                            print(json.dumps(solution, indent=2))
                            return
    
    print('{"solution": {"header": [], "rows": []}}')

if __name__ == "__main__":
    main()