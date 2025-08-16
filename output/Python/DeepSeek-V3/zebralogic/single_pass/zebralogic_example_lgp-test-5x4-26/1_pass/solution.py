import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories
    houses = ['1', '2', '3', '4', '5']
    names = ['Alice', 'Peter', 'Bob', 'Eric', 'Arnold']
    heights = ['very short', 'short', 'tall', 'average', 'very tall']
    mothers = ['Janelle', 'Kailyn', 'Penny', 'Holly', 'Aniya']
    hair_colors = ['blonde', 'black', 'gray', 'red', 'brown']
    
    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for height_perm in permutations(heights):
            for mother_perm in permutations(mothers):
                for hair_perm in permutations(hair_colors):
                    # Create a dictionary to hold the current assignment
                    solution = {}
                    valid = True
                    
                    # Assign values to each house
                    for i in range(5):
                        house = str(i+1)
                        solution[house] = {
                            'Name': name_perm[i],
                            'Height': height_perm[i],
                            'Mother': mother_perm[i],
                            'HairColor': hair_perm[i]
                        }
                    
                    # Check all constraints
                    # Clue 8: Bob is in the fifth house
                    if solution['5']['Name'] != 'Bob':
                        valid = False
                        continue
                    
                    # Clue 5: Eric has black hair
                    eric_house = None
                    for house in houses:
                        if solution[house]['Name'] == 'Eric':
                            eric_house = house
                            if solution[house]['HairColor'] != 'black':
                                valid = False
                            break
                    if not eric_house:
                        valid = False
                        continue
                    
                    # Clue 4: black hair is not in house 4
                    if solution['4']['HairColor'] == 'black':
                        valid = False
                        continue
                    
                    # Clue 7: Eric and gray hair are next to each other
                    gray_house = None
                    for house in houses:
                        if solution[house]['HairColor'] == 'gray':
                            gray_house = house
                            break
                    if not gray_house:
                        valid = False
                        continue
                    if abs(int(eric_house) - int(gray_house)) != 1:
                        valid = False
                        continue
                    
                    # Clue 3: gray hair is directly left of Janelle
                    janelle_house = None
                    for house in houses:
                        if solution[house]['Mother'] == 'Janelle':
                            janelle_house = house
                            break
                    if not janelle_house:
                        valid = False
                        continue
                    if int(gray_house) + 1 != int(janelle_house):
                        valid = False
                        continue
                    
                    # Clue 12: brown hair is left of Janelle
                    brown_house = None
                    for house in houses:
                        if solution[house]['HairColor'] == 'brown':
                            brown_house = house
                            break
                    if not brown_house:
                        valid = False
                        continue
                    if int(brown_house) >= int(janelle_house):
                        valid = False
                        continue
                    
                    # Clue 11: Arnold has brown hair
                    for house in houses:
                        if solution[house]['Name'] == 'Arnold':
                            if solution[house]['HairColor'] != 'brown':
                                valid = False
                            break
                    if not valid:
                        continue
                    
                    # Clue 9: Peter has red hair
                    for house in houses:
                        if solution[house]['Name'] == 'Peter':
                            if solution[house]['HairColor'] != 'red':
                                valid = False
                            break
                    if not valid:
                        continue
                    
                    # Clue 14: Kailyn is in house 3
                    if solution['3']['Mother'] != 'Kailyn':
                        valid = False
                        continue
                    
                    # Clue 10: Kailyn is directly left of short
                    short_house = None
                    for house in houses:
                        if solution[house]['Height'] == 'short':
                            short_house = house
                            break
                    if not short_house:
                        valid = False
                        continue
                    if int(short_house) != 4:
                        valid = False
                        continue
                    
                    # Clue 2: two houses between average and short
                    average_house = None
                    for house in houses:
                        if solution[house]['Height'] == 'average':
                            average_house = house
                            break
                    if not average_house:
                        valid = False
                        continue
                    if abs(int(average_house) - int(short_house)) != 3:
                        valid = False
                        continue
                    
                    # Clue 6: very short's mother is Penny
                    very_short_house = None
                    for house in houses:
                        if solution[house]['Height'] == 'very short':
                            very_short_house = house
                            if solution[house]['Mother'] != 'Penny':
                                valid = False
                            break
                    if not very_short_house:
                        valid = False
                        continue
                    
                    # Clue 13: Aniya and very short are next to each other
                    aniya_house = None
                    for house in houses:
                        if solution[house]['Mother'] == 'Aniya':
                            aniya_house = house
                            break
                    if not aniya_house:
                        valid = False
                        continue
                    if abs(int(aniya_house) - int(very_short_house)) != 1:
                        valid = False
                        continue
                    
                    # Clue 1: tall's mother is Holly
                    tall_house = None
                    for house in houses:
                        if solution[house]['Height'] == 'tall':
                            tall_house = house
                            if solution[house]['Mother'] != 'Holly':
                                valid = False
                            break
                    if not tall_house:
                        valid = False
                        continue
                    
                    if valid:
                        # Prepare the output
                        output = {
                            "solution": {
                                "header": ["House", "Name", "Height", "Mother", "HairColor"],
                                "rows": []
                            }
                        }
                        for house in houses:
                            row = [house]
                            row.append(solution[house]['Name'])
                            row.append(solution[house]['Height'])
                            row.append(solution[house]['Mother'])
                            row.append(solution[house]['HairColor'])
                            output["solution"]["rows"].append(row)
                        return output
    return {"solution": {"header": [], "rows": []}}

# Solve and print the solution
solution = solve_puzzle()
print(json.dumps(solution, indent=2))