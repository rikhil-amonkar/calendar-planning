import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values for each category
    names = ['Eric', 'Peter', 'Alice', 'Arnold']
    cars = ['tesla model 3', 'honda civic', 'toyota camry', 'ford f150']
    birthdays = ['jan', 'april', 'sept', 'feb']
    hobbies = ['painting', 'cooking', 'gardening', 'photography']
    houses = ['1', '2', '3', '4']
    
    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for car_perm in permutations(cars):
            for bday_perm in permutations(birthdays):
                for hobby_perm in permutations(hobbies):
                    # Create assignment for each house
                    assignment = []
                    for i in range(4):
                        house = {
                            'House': str(i + 1),
                            'Name': name_perm[i],
                            'CarModel': car_perm[i],
                            'Birthday': bday_perm[i],
                            'Hobby': hobby_perm[i]
                        }
                        assignment.append(house)
                    
                    # Check all constraints
                    valid = True
                    
                    # Clue 1: The person whose birthday is in January is not in the second house.
                    for house in assignment:
                        if house['Birthday'] == 'jan' and house['House'] == '2':
                            valid = False
                            break
                    if not valid:
                        continue
                    
                    # Clue 2: The photography enthusiast is somewhere to the left of Eric.
                    photo_house = None
                    eric_house = None
                    for house in assignment:
                        if house['Hobby'] == 'photography':
                            photo_house = int(house['House'])
                        if house['Name'] == 'Eric':
                            eric_house = int(house['House'])
                    if photo_house is None or eric_house is None or photo_house >= eric_house:
                        valid = False
                    if not valid:
                        continue
                    
                    # Clue 3: The photography enthusiast is somewhere to the left of Peter.
                    peter_house = None
                    for house in assignment:
                        if house['Name'] == 'Peter':
                            peter_house = int(house['House'])
                    if peter_house is None or photo_house >= peter_house:
                        valid = False
                    if not valid:
                        continue
                    
                    # Clue 4: The person who owns a Honda Civic is directly left of the person who owns a Tesla Model 3.
                    honda_house = None
                    tesla_house = None
                    for house in assignment:
                        if house['CarModel'] == 'honda civic':
                            honda_house = int(house['House'])
                        if house['CarModel'] == 'tesla model 3':
                            tesla_house = int(house['House'])
                    if honda_house is None or tesla_house is None or honda_house + 1 != tesla_house:
                        valid = False
                    if not valid:
                        continue
                    
                    # Clue 5: There is one house between the person who owns a Tesla Model 3 and the person who enjoys gardening.
                    gardening_house = None
                    for house in assignment:
                        if house['Hobby'] == 'gardening':
                            gardening_house = int(house['House'])
                    if gardening_house is None or abs(tesla_house - gardening_house) != 2:
                        valid = False
                    if not valid:
                        continue
                    
                    # Clue 6: The person who owns a Tesla Model 3 is Arnold.
                    for house in assignment:
                        if house['CarModel'] == 'tesla model 3' and house['Name'] != 'Arnold':
                            valid = False
                            break
                    if not valid:
                        continue
                    
                    # Clue 7: The person whose birthday is in February is the person who loves cooking.
                    for house in assignment:
                        if house['Birthday'] == 'feb' and house['Hobby'] != 'cooking':
                            valid = False
                            break
                    if not valid:
                        continue
                    
                    # Clue 8: The person who owns a Toyota Camry is Peter.
                    for house in assignment:
                        if house['CarModel'] == 'toyota camry' and house['Name'] != 'Peter':
                            valid = False
                            break
                    if not valid:
                        continue
                    
                    # Clue 9: The person whose birthday is in April is Arnold.
                    for house in assignment:
                        if house['Birthday'] == 'april' and house['Name'] != 'Arnold':
                            valid = False
                            break
                    if not valid:
                        continue
                    
                    # Clue 10: Alice is the photography enthusiast.
                    for house in assignment:
                        if house['Name'] == 'Alice' and house['Hobby'] != 'photography':
                            valid = False
                            break
                    if not valid:
                        continue
                    
                    # Clue 11: Peter is the person whose birthday is in January.
                    for house in assignment:
                        if house['Name'] == 'Peter' and house['Birthday'] != 'jan':
                            valid = False
                            break
                    if not valid:
                        continue
                    
                    # If all constraints are satisfied, return the solution
                    if valid:
                        result = {
                            "solution": {
                                "header": ["House", "Name", "CarModel", "Birthday", "Hobby"],
                                "rows": []
                            }
                        }
                        
                        for house in sorted(assignment, key=lambda x: int(x['House'])):
                            row = [
                                house['House'],
                                house['Name'],
                                house['CarModel'],
                                house['Birthday'],
                                house['Hobby']
                            ]
                            result["solution"]["rows"].append(row)
                        
                        return result
    
    return None

def main():
    solution = solve_puzzle()
    if solution:
        print(json.dumps(solution, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()