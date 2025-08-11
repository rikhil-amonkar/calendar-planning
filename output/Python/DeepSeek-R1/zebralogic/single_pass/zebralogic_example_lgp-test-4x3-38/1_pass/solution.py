import itertools
import json

def main():
    # Fixed attributes from clues
    fixed_house3_name = 'Alice'
    fixed_house3_mother = 'Kailyn'
    fixed_house2_flower = 'lilies'
    
    # Remaining attributes
    remaining_names = ['Peter', 'Arnold', 'Eric']
    remaining_mothers = ['Holly', 'Janelle', 'Aniya']
    remaining_flowers = ['carnations', 'roses', 'daffodils']  # for houses 1, 3, 4
    
    # Generate all permutations for the remaining attributes
    for names_perm in itertools.permutations(remaining_names):
        for mothers_perm in itertools.permutations(remaining_mothers):
            for flowers_perm in itertools.permutations(remaining_flowers):
                # Initialize the attributes for each house
                names = [
                    names_perm[0],  # house1
                    names_perm[1],  # house2
                    fixed_house3_name,  # house3
                    names_perm[2]   # house4
                ]
                mothers = [
                    mothers_perm[0],  # house1
                    mothers_perm[1],  # house2
                    fixed_house3_mother,  # house3
                    mothers_perm[2]   # house4
                ]
                flowers = [
                    flowers_perm[0],  # house1
                    fixed_house2_flower,  # house2
                    flowers_perm[1],  # house3
                    flowers_perm[2]   # house4
                ]
                
                # Check constraints
                valid = True
                
                # Clue4: Eric has daffodils
                for i in range(4):
                    if names[i] == 'Eric' and flowers[i] != 'daffodils':
                        valid = False
                        break
                if not valid:
                    continue
                    
                # Clue5: Arnold has mother Holly
                for i in [0, 1, 3]:  # house3 is fixed, skip
                    if names[i] == 'Arnold' and mothers[i] != 'Holly':
                        valid = False
                        break
                if not valid:
                    continue
                
                # Find Arnold's position
                arnold_index = None
                for i in [0, 1, 3]:
                    if names[i] == 'Arnold':
                        arnold_index = i
                        break
                if arnold_index is None:
                    valid = False
                    continue
                
                # Find Janelle's position
                janelle_index = None
                for i in [0, 1, 3]:
                    if mothers[i] == 'Janelle':
                        janelle_index = i
                        break
                if janelle_index is None:
                    valid = False
                    continue
                
                # Clue2: Janelle is right of Arnold
                if janelle_index <= arnold_index:
                    valid = False
                    continue
                
                # Find carnations position
                carnations_index = None
                for i in range(4):
                    if flowers[i] == 'carnations':
                        carnations_index = i
                        break
                if carnations_index is None:
                    valid = False
                    continue
                
                # Find Peter's position
                peter_index = None
                for i in range(4):
                    if names[i] == 'Peter':
                        peter_index = i
                        break
                if peter_index is None:
                    valid = False
                    continue
                
                # Clue3: Peter is right of carnations
                if peter_index <= carnations_index:
                    valid = False
                    continue
                
                # Clue6: carnations is right of Holly (Arnold's mother)
                if carnations_index <= arnold_index:
                    valid = False
                    continue
                
                if valid:
                    # Build the solution
                    solution = {
                        "header": ["House", "Name", "Mother", "Flower"],
                        "rows": [
                            ["1", names[0], mothers[0], flowers[0]],
                            ["2", names[1], mothers[1], flowers[1]],
                            ["3", names[2], mothers[2], flowers[2]],
                            ["4", names[3], mothers[3], flowers[3]]
                        ]
                    }
                    output = {"solution": solution}
                    print(json.dumps(output))
                    return
                    
    print(json.dumps({"solution": {}}))  # No solution found

if __name__ == "__main__":
    main()