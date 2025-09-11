import itertools
import json

def main():
    # Define the attributes
    attributes = {
        'names': ['Arnold', 'Alice', 'Eric', 'Peter'],
        'hobbies': ['cooking', 'painting', 'photography', 'gardening'],
        'birthdays': ['april', 'jan', 'sept', 'feb'],
        'educations': ['master', 'bachelor', 'associate', 'high school'],
        'smoothies': ['cherry', 'watermelon', 'desert', 'dragonfruit']
    }
    
    # Precompute fixed values for house3 and house1
    fixed_education = [None, None, 'high school', None]
    fixed_birthday = [None, None, 'sept', None]
    fixed_smoothie = ['dragonfruit', None, None, None]
    
    # Generate permutations for the variable parts
    name_perms = list(itertools.permutations(attributes['names']))
    hobby_perms = list(itertools.permutations(attributes['hobbies']))
    birthday_perms = list(itertools.permutations(['april', 'jan', 'feb']))
    education_perms = list(itertools.permutations(['master', 'bachelor', 'associate']))
    smoothie_perms = list(itertools.permutations(['cherry', 'watermelon', 'desert']))
    
    found_solution = None
    
    for names in name_perms:
        for hobbies in hobby_perms:
            for b_perm in birthday_perms:
                # Assign birthdays with fixed house3
                birthdays = [b_perm[0], b_perm[1], 'sept', b_perm[2]]
                for e_perm in education_perms:
                    # Assign educations with fixed house3
                    educations = [e_perm[0], e_perm[1], 'high school', e_perm[2]]
                    for s_perm in smoothie_perms:
                        # Assign smoothies with fixed house1 and check house3 not watermelon
                        smoothies = ['dragonfruit', s_perm[0], s_perm[1], s_perm[2]]
                        if smoothies[2] == 'watermelon':
                            continue
                        
                        # Create the houses assignment
                        houses = []
                        for i in range(4):
                            house = {
                                'name': names[i],
                                'hobby': hobbies[i],
                                'birthday': birthdays[i],
                                'education': educations[i],
                                'smoothie': smoothies[i]
                            }
                            houses.append(house)
                        
                        # Check constraints
                        if check_constraints(houses):
                            found_solution = houses
                            break
                    if found_solution:
                        break
                if found_solution:
                    break
            if found_solution:
                break
        if found_solution:
            break
            
    if found_solution is None:
        print("No solution found")
        return
        
    # Format the solution as JSON
    header = ["House", "Name", "Hobby", "Birthday", "Education", "Smoothie"]
    rows = []
    for i, house in enumerate(found_solution):
        rows.append([str(i+1), house['name'], house['hobby'], house['birthday'], house['education'], house['smoothie']])
    
    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    
    print(json.dumps(output, indent=2))

def check_constraints(houses):
    # Constraint 1: Desert smoothie lover is jan birthday
    desert_house = None
    for house in houses:
        if house['smoothie'] == 'desert':
            desert_house = house
            break
    if desert_house is None or desert_house['birthday'] != 'jan':
        return False
        
    # Constraint 2: Eric is bachelor
    eric_house = None
    for house in houses:
        if house['name'] == 'Eric':
            eric_house = house
            break
    if eric_house is None or eric_house['education'] != 'bachelor':
        return False
        
    # Constraint 3: jan birthday is bachelor
    jan_house = None
    for house in houses:
        if house['birthday'] == 'jan':
            jan_house = house
            break
    if jan_house is None or jan_house['education'] != 'bachelor':
        return False
        
    # Constraint 6: associate is Arnold
    associate_house = None
    for house in houses:
        if house['education'] == 'associate':
            associate_house = house
            break
    if associate_house is None or associate_house['name'] != 'Arnold':
        return False
        
    # Constraint 7: master is painting
    master_house = None
    for house in houses:
        if house['education'] == 'master':
            master_house = house
            break
    if master_house is None or master_house['hobby'] != 'painting':
        return False
        
    # Constraint 10: cooking is Alice
    cooking_house = None
    for house in houses:
        if house['hobby'] == 'cooking':
            cooking_house = house
            break
    if cooking_house is None or cooking_house['name'] != 'Alice':
        return False
        
    # Constraint 11: april birthday and gardening are adjacent
    april_index = None
    gardening_index = None
    for i, house in enumerate(houses):
        if house['birthday'] == 'april':
            april_index = i
        if house['hobby'] == 'gardening':
            gardening_index = i
    if april_index is None or gardening_index is None:
        return False
    if abs(april_index - gardening_index) != 1:
        return False
        
    # Constraint 12: painting is feb birthday
    painting_house = None
    for house in houses:
        if house['hobby'] == 'painting':
            painting_house = house
            break
    if painting_house is None or painting_house['birthday'] != 'feb':
        return False
        
    return True

if __name__ == '__main__':
    main()