import itertools
import json

def main():
    # Define the attributes and their possible values
    names = ['Eric', 'Arnold']
    hobbies = ['gardening', 'photography']
    pets = ['cat', 'dog']
    heights = ['short', 'very short']
    
    # Generate all possible permutations for each attribute
    for name_perm in itertools.permutations(names):
        for hobby_perm in itertools.permutations(hobbies):
            for pet_perm in itertools.permutations(pets):
                for height_perm in itertools.permutations(heights):
                    # Create candidate assignment for two houses
                    candidate = [
                        [name_perm[0], hobby_perm[0], pet_perm[0], height_perm[0]],  # House 1
                        [name_perm[1], hobby_perm[1], pet_perm[1], height_perm[1]]   # House 2
                    ]
                    
                    # Check constraints
                    # Constraint 2: Eric is very short
                    eric_house = None
                    if candidate[0][0] == 'Eric':
                        eric_house = 0
                    elif candidate[1][0] == 'Eric':
                        eric_house = 1
                    if eric_house is None or candidate[eric_house][3] != 'very short':
                        continue
                    
                    # Constraint 1: Very short person is photography enthusiast
                    very_short_house = None
                    if candidate[0][3] == 'very short':
                        very_short_house = 0
                    elif candidate[1][3] == 'very short':
                        very_short_house = 1
                    if very_short_house is None or candidate[very_short_house][1] != 'photography':
                        continue
                    
                    # Constraint 3: Cat owner is to the right of very short person
                    cat_house = None
                    if candidate[0][2] == 'cat':
                        cat_house = 0
                    elif candidate[1][2] == 'cat':
                        cat_house = 1
                    if very_short_house is None or cat_house is None or cat_house <= very_short_house:
                        continue
                    
                    # All constraints satisfied, format the solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Hobby", "Pet", "Height"],
                            "rows": [
                                ["1", candidate[0][0], candidate[0][1], candidate[0][2], candidate[0][3]],
                                ["2", candidate[1][0], candidate[1][1], candidate[1][2], candidate[1][3]]
                            ]
                        }
                    }
                    print(json.dumps(solution))
                    return
    
    # If no solution found (should not happen for this puzzle)
    print('{"solution": {"header": ["House", "Name", "Hobby", "Pet", "Height"], "rows": []}}')

if __name__ == "__main__":
    main()