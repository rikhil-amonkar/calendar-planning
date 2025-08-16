import itertools
import json

def main():
    names = ['Eric', 'Arnold']
    hobbies = ['gardening', 'photography']
    pets = ['cat', 'dog']
    heights = ['short', 'very short']
    
    found_solution = None
    
    for name_perm in itertools.permutations(names):
        for hobby_perm in itertools.permutations(hobbies):
            for pet_perm in itertools.permutations(pets):
                for height_perm in itertools.permutations(heights):
                    house1 = {
                        'House': 1,
                        'Name': name_perm[0],
                        'Hobby': hobby_perm[0],
                        'Pet': pet_perm[0],
                        'Height': height_perm[0]
                    }
                    house2 = {
                        'House': 2,
                        'Name': name_perm[1],
                        'Hobby': hobby_perm[1],
                        'Pet': pet_perm[1],
                        'Height': height_perm[1]
                    }
                    assignment = [house1, house2]
                    
                    if check_constraints(assignment):
                        found_solution = assignment
                        break
                if found_solution:
                    break
            if found_solution:
                break
        if found_solution:
            break
            
    if found_solution:
        rows = []
        for house in found_solution:
            rows.append([
                str(house['House']),
                house['Name'],
                house['Hobby'],
                house['Pet'],
                house['Height']
            ])
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "Hobby", "Pet", "Height"],
                "rows": rows
            }
        }
        print(json.dumps(solution_dict))
    else:
        print(json.dumps({"solution": None}))

def check_constraints(assignment):
    very_short_person = None
    eric_person = None
    cat_owner_house = None
    
    for house in assignment:
        if house['Height'] == 'very short':
            very_short_person = house
        if house['Name'] == 'Eric':
            eric_person = house
        if house['Pet'] == 'cat':
            cat_owner_house = house['House']
    
    if very_short_person is None or eric_person is None or cat_owner_house is None:
        return False
    
    if very_short_person['Hobby'] != 'photography':
        return False
    
    if eric_person['Height'] != 'very short':
        return False
    
    if cat_owner_house <= very_short_person['House']:
        return False
    
    return True

if __name__ == "__main__":
    main()