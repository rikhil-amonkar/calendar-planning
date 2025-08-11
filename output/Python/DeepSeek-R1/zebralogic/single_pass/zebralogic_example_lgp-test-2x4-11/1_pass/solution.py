import itertools
import json
import sys

def main():
    names = ['Eric', 'Arnold']
    hobbies = ['gardening', 'photography']
    pets = ['cat', 'dog']
    heights = ['short', 'very short']
    
    for name_perm in itertools.permutations(names):
        for hobby_perm in itertools.permutations(hobbies):
            for pet_perm in itertools.permutations(pets):
                for height_perm in itertools.permutations(heights):
                    assignment = {
                        1: {
                            'Name': name_perm[0],
                            'Hobby': hobby_perm[0],
                            'Pet': pet_perm[0],
                            'Height': height_perm[0]
                        },
                        2: {
                            'Name': name_perm[1],
                            'Hobby': hobby_perm[1],
                            'Pet': pet_perm[1],
                            'Height': height_perm[1]
                        }
                    }
                    
                    valid = True
                    
                    for house in [1, 2]:
                        if assignment[house]['Height'] == 'very short':
                            if assignment[house]['Hobby'] != 'photography':
                                valid = False
                                break
                    
                    if not valid:
                        continue
                    
                    for house in [1, 2]:
                        if assignment[house]['Name'] == 'Eric':
                            if assignment[house]['Height'] != 'very short':
                                valid = False
                                break
                    
                    if not valid:
                        continue
                    
                    very_short_house = None
                    cat_house = None
                    for house in [1, 2]:
                        if assignment[house]['Height'] == 'very short':
                            very_short_house = house
                        if assignment[house]['Pet'] == 'cat':
                            cat_house = house
                    
                    if very_short_house is None or cat_house is None:
                        valid = False
                    else:
                        if cat_house <= very_short_house:
                            valid = False
                    
                    if valid:
                        header = ['House', 'Name', 'Hobby', 'Pet', 'Height']
                        rows = []
                        for house_num in [1, 2]:
                            row = [str(house_num)]
                            row.append(assignment[house_num]['Name'])
                            row.append(assignment[house_num]['Hobby'])
                            row.append(assignment[house_num]['Pet'])
                            row.append(assignment[house_num]['Height'])
                            rows.append(row)
                        
                        solution_dict = {
                            "solution": {
                                "header": header,
                                "rows": rows
                            }
                        }
                        print(json.dumps(solution_dict))
                        return
    
    print("No solution found!", file=sys.stderr)
    sys.exit(1)

if __name__ == "__main__":
    main()