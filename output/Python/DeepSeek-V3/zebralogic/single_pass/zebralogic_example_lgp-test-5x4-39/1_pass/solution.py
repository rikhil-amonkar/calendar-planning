import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values for each attribute
    houses = ['1', '2', '3', '4', '5']
    names = ['Arnold', 'Peter', 'Eric', 'Alice', 'Bob']
    hobbies = ['painting', 'cooking', 'knitting', 'gardening', 'photography']
    heights = ['very tall', 'tall', 'very short', 'average', 'short']
    lunches = ['stew', 'grilled cheese', 'stir fry', 'spaghetti', 'pizza']

    # Generate all possible permutations for each attribute
    for name_perm in permutations(names):
        for hobby_perm in permutations(hobbies):
            for height_perm in permutations(heights):
                for lunch_perm in permutations(lunches):
                    solution = {
                        '1': {'Name': None, 'Hobby': None, 'Height': None, 'Lunch': None},
                        '2': {'Name': None, 'Hobby': None, 'Height': None, 'Lunch': None},
                        '3': {'Name': None, 'Hobby': None, 'Height': None, 'Lunch': None},
                        '4': {'Name': None, 'Hobby': None, 'Height': None, 'Lunch': None},
                        '5': {'Name': None, 'Hobby': None, 'Height': None, 'Lunch': None},
                    }
                    
                    # Assign the current permutation to each house
                    for i, house in enumerate(houses):
                        solution[house]['Name'] = name_perm[i]
                        solution[house]['Hobby'] = hobby_perm[i]
                        solution[house]['Height'] = height_perm[i]
                        solution[house]['Lunch'] = lunch_perm[i]
                    
                    # Check all constraints
                    valid = True
                    
                    # 1. Bob is the photography enthusiast.
                    bob_house = None
                    for house in houses:
                        if solution[house]['Name'] == 'Bob':
                            bob_house = house
                            break
                    if solution[bob_house]['Hobby'] != 'photography':
                        valid = False
                        continue
                    
                    # 2. The person who loves eating grilled cheese is the person who is tall.
                    grilled_cheese_house = None
                    for house in houses:
                        if solution[house]['Lunch'] == 'grilled cheese':
                            grilled_cheese_house = house
                            break
                    if grilled_cheese_house is None or solution[grilled_cheese_house]['Height'] != 'tall':
                        valid = False
                        continue
                    
                    # 3. Peter is not in the second house.
                    if solution['2']['Name'] == 'Peter':
                        valid = False
                        continue
                    
                    # 4. The person who is tall is directly left of the person who loves stir fry.
                    tall_house = None
                    for house in houses:
                        if solution[house]['Height'] == 'tall':
                            tall_house = house
                            break
                    if tall_house is None or int(tall_house) >= 5 or solution[str(int(tall_house) + 1)]['Lunch'] != 'stir fry':
                        valid = False
                        continue
                    
                    # 5. The person who loves cooking is the person who has an average height.
                    cooking_house = None
                    for house in houses:
                        if solution[house]['Hobby'] == 'cooking':
                            cooking_house = house
                            break
                    if cooking_house is None or solution[cooking_house]['Height'] != 'average':
                        valid = False
                        continue
                    
                    # 6. Alice is directly left of the person who is a pizza lover.
                    alice_house = None
                    for house in houses:
                        if solution[house]['Name'] == 'Alice':
                            alice_house = house
                            break
                    if alice_house is None or int(alice_house) >= 5 or solution[str(int(alice_house) + 1)]['Lunch'] != 'pizza':
                        valid = False
                        continue
                    
                    # 7. The person who loves the spaghetti eater is not in the second house.
                    spaghetti_house = None
                    for house in houses:
                        if solution[house]['Lunch'] == 'spaghetti':
                            spaghetti_house = house
                            break
                    if spaghetti_house == '2':
                        valid = False
                        continue
                    
                    # 8. Eric is not in the fifth house.
                    if solution['5']['Name'] == 'Eric':
                        valid = False
                        continue
                    
                    # 9. The person who is short is Peter.
                    peter_house = None
                    for house in houses:
                        if solution[house]['Name'] == 'Peter':
                            peter_house = house
                            break
                    if peter_house is None or solution[peter_house]['Height'] != 'short':
                        valid = False
                        continue
                    
                    # 10. The person who has an average height and the person who enjoys gardening are next to each other.
                    average_house = None
                    gardening_house = None
                    for house in houses:
                        if solution[house]['Height'] == 'average':
                            average_house = house
                        if solution[house]['Hobby'] == 'gardening':
                            gardening_house = house
                    if average_house is None or gardening_house is None or abs(int(average_house) - int(gardening_house)) != 1:
                        valid = False
                        continue
                    
                    # 11. The person who paints as a hobby is directly left of the person who loves eating grilled cheese.
                    painting_house = None
                    for house in houses:
                        if solution[house]['Hobby'] == 'painting':
                            painting_house = house
                            break
                    if painting_house is None or int(painting_house) >= 5 or solution[str(int(painting_house) + 1)]['Lunch'] != 'grilled cheese':
                        valid = False
                        continue
                    
                    # 12. The person who is very short is in the fifth house.
                    if solution['5']['Height'] != 'very short':
                        valid = False
                        continue
                    
                    # 13. The person who is tall is in the third house.
                    if solution['3']['Height'] != 'tall':
                        valid = False
                        continue
                    
                    # 14. Alice is somewhere to the right of the photography enthusiast.
                    alice_house = None
                    photography_house = None
                    for house in houses:
                        if solution[house]['Name'] == 'Alice':
                            alice_house = house
                        if solution[house]['Hobby'] == 'photography':
                            photography_house = house
                    if alice_house is None or photography_house is None or int(alice_house) <= int(photography_house):
                        valid = False
                        continue
                    
                    if valid:
                        # Prepare the output
                        output = {
                            "solution": {
                                "header": ["House", "Name", "Hobby", "Height", "Lunch"],
                                "rows": []
                            }
                        }
                        for house in houses:
                            row = [house]
                            row.append(solution[house]['Name'])
                            row.append(solution[house]['Hobby'])
                            row.append(solution[house]['Height'])
                            row.append(solution[house]['Lunch'])
                            output["solution"]["rows"].append(row)
                        return json.dumps(output, indent=2)
    
    return json.dumps({"solution": {"header": [], "rows": []}})

print(solve_puzzle())