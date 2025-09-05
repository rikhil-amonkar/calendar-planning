import json

def main():
    # Define the attributes
    houses = [1, 2]
    names = ['Eric', 'Arnold']
    hobbies = ['gardening', 'photography']
    pets = ['cat', 'dog']
    heights = ['short', 'very short']
    
    # Initialize all possible assignments
    from itertools import product, permutations
    all_permutations = list(permutations(names))
    
    # Try all possible assignments
    for name_perm in all_permutations:
        for hobby_perm in permutations(hobbies):
            for pet_perm in permutations(pets):
                for height_perm in permutations(heights):
                    # Create assignment for house 1 and 2
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
                    
                    # Check clue 1: The person who is very short is the photography enthusiast.
                    very_short_house = None
                    for house, attrs in assignment.items():
                        if attrs['Height'] == 'very short':
                            very_short_house = house
                            break
                    
                    if very_short_house is None:
                        continue
                    
                    if assignment[very_short_house]['Hobby'] != 'photography':
                        continue
                    
                    # Check clue 2: Eric is the person who is very short.
                    if assignment[very_short_house]['Name'] != 'Eric':
                        continue
                    
                    # Check clue 3: The person who has a cat is somewhere to the right of the person who is very short.
                    cat_house = None
                    for house, attrs in assignment.items():
                        if attrs['Pet'] == 'cat':
                            cat_house = house
                            break
                    
                    if cat_house is None or cat_house <= very_short_house:
                        continue
                    
                    # If all clues are satisfied, we found the solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Hobby", "Pet", "Height"],
                            "rows": []
                        }
                    }
                    
                    for house in sorted(assignment.keys()):
                        row = [
                            str(house),
                            assignment[house]['Name'],
                            assignment[house]['Hobby'],
                            assignment[house]['Pet'],
                            assignment[house]['Height']
                        ]
                        solution["solution"]["rows"].append(row)
                    
                    print(json.dumps(solution, indent=2))
                    return
    
    # If no solution found (shouldn't happen with valid puzzle)
    print(json.dumps({"solution": {"header": ["House", "Name", "Hobby", "Pet", "Height"], "rows": []}}))

if __name__ == "__main__":
    main()