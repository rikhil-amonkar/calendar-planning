import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values for each attribute
    houses = ['1', '2', '3', '4', '5']
    names = ['Alice', 'Peter', 'Bob', 'Eric', 'Arnold']
    heights = ['very short', 'short', 'tall', 'average', 'very tall']
    mothers = ['Janelle', 'Kailyn', 'Penny', 'Holly', 'Aniya']
    hair_colors = ['blonde', 'black', 'gray', 'red', 'brown']

    # Generate all possible permutations for each attribute
    for name_perm in permutations(names):
        for height_perm in permutations(heights):
            for mother_perm in permutations(mothers):
                for hair_perm in permutations(hair_colors):
                    # Create a dictionary to hold the current assignment
                    solution = {
                        '1': {'Name': None, 'height': None, 'mother': None, 'hair_color': None},
                        '2': {'Name': None, 'height': None, 'mother': None, 'hair_color': None},
                        '3': {'Name': None, 'height': None, 'mother': None, 'hair_color': None},
                        '4': {'Name': None, 'height': None, 'mother': None, 'hair_color': None},
                        '5': {'Name': None, 'height': None, 'mother': None, 'hair_color': None}
                    }
                    
                    # Assign current permutation values to houses
                    for i, house in enumerate(houses):
                        solution[house]['Name'] = name_perm[i]
                        solution[house]['height'] = height_perm[i]
                        solution[house]['mother'] = mother_perm[i]
                        solution[house]['hair_color'] = hair_perm[i]
                    
                    # Check all constraints
                    valid = True
                    
                    # Constraint 8: Bob is in the fifth house.
                    if solution['5']['Name'] != 'Bob':
                        valid = False
                        continue
                    
                    # Constraint 5: Eric has black hair.
                    for house in houses:
                        if solution[house]['Name'] == 'Eric' and solution[house]['hair_color'] != 'black':
                            valid = False
                            break
                    if not valid:
                        continue
                    
                    # Constraint 4: Black hair is not in house 4.
                    if solution['4']['hair_color'] == 'black':
                        valid = False
                        continue
                    
                    # Constraint 9: Peter has red hair.
                    for house in houses:
                        if solution[house]['Name'] == 'Peter' and solution[house]['hair_color'] != 'red':
                            valid = False
                            break
                    if not valid:
                        continue
                    
                    # Constraint 11: Arnold has brown hair.
                    for house in houses:
                        if solution[house]['Name'] == 'Arnold' and solution[house]['hair_color'] != 'brown':
                            valid = False
                            break
                    if not valid:
                        continue
                    
                    # Constraint 1: Tall person's mother is Holly.
                    for house in houses:
                        if solution[house]['height'] == 'tall' and solution[house]['mother'] != 'Holly':
                            valid = False
                            break
                    if not valid:
                        continue
                    
                    # Constraint 6: Very short person's mother is Penny.
                    for house in houses:
                        if solution[house]['height'] == 'very short' and solution[house]['mother'] != 'Penny':
                            valid = False
                            break
                    if not valid:
                        continue
                    
                    # Constraint 14: Mother Kailyn is in house 3.
                    if solution['3']['mother'] != 'Kailyn':
                        valid = False
                        continue
                    
                    # Constraint 10: Mother Kailyn is directly left of short person.
                    # Since Kailyn is in house 3, short must be in house 4.
                    if solution['4']['height'] != 'short':
                        valid = False
                        continue
                    
                    # Constraint 2: Two houses between average and short.
                    # Short is in 4, so average must be in 1 (4-3=1)
                    if solution['1']['height'] != 'average':
                        valid = False
                        continue
                    
                    # Constraint 7: Eric and gray hair next to each other.
                    eric_house = None
                    gray_house = None
                    for house in houses:
                        if solution[house]['Name'] == 'Eric':
                            eric_house = int(house)
                        if solution[house]['hair_color'] == 'gray':
                            gray_house = int(house)
                    if eric_house is None or gray_house is None or abs(eric_house - gray_house) != 1:
                        valid = False
                        continue
                    
                    # Constraint 3: Gray hair is directly left of mother Janelle.
                    gray_pos = None
                    janelle_pos = None
                    for house in houses:
                        if solution[house]['hair_color'] == 'gray':
                            gray_pos = int(house)
                        if solution[house]['mother'] == 'Janelle':
                            janelle_pos = int(house)
                    if gray_pos is None or janelle_pos is None or janelle_pos != gray_pos + 1:
                        valid = False
                        continue
                    
                    # Constraint 12: Brown hair is left of mother Janelle.
                    brown_pos = None
                    for house in houses:
                        if solution[house]['hair_color'] == 'brown':
                            brown_pos = int(house)
                            break
                    if brown_pos is None or brown_pos >= janelle_pos:
                        valid = False
                        continue
                    
                    # Constraint 13: Mother Aniya and very short next to each other.
                    aniya_pos = None
                    very_short_pos = None
                    for house in houses:
                        if solution[house]['mother'] == 'Aniya':
                            aniya_pos = int(house)
                        if solution[house]['height'] == 'very short':
                            very_short_pos = int(house)
                    if aniya_pos is None or very_short_pos is None or abs(aniya_pos - very_short_pos) != 1:
                        valid = False
                        continue
                    
                    # If all constraints are satisfied, return the solution
                    if valid:
                        # Prepare the output in the required JSON format
                        output = {
                            "solution": {
                                "header": ["House", "Name", "height", "mother", "hair_color"],
                                "rows": []
                            }
                        }
                        for house in houses:
                            row = [
                                house,
                                solution[house]['Name'],
                                solution[house]['height'],
                                solution[house]['mother'],
                                solution[house]['hair_color']
                            ]
                            output["solution"]["rows"].append(row)
                        return output
    return {"solution": {"header": [], "rows": []}}

# Solve the puzzle and print the result as JSON
print(json.dumps(solve_puzzle(), indent=2))