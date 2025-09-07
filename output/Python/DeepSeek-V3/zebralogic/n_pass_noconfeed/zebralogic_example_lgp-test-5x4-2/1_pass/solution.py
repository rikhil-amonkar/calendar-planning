import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values for each category
    names = ['Bob', 'Eric', 'Arnold', 'Alice', 'Peter']
    colors = ['blue', 'green', 'white', 'yellow', 'red']
    phones = ['huawei p50', 'samsung galaxy s21', 'oneplus 9', 'iphone 13', 'google pixel 6']
    occupations = ['artist', 'teacher', 'doctor', 'engineer', 'lawyer']
    
    houses = [1, 2, 3, 4, 5]
    
    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for color_perm in permutations(colors):
            for phone_perm in permutations(phones):
                for occup_perm in permutations(occupations):
                    # Create assignment dictionaries
                    assignment = {}
                    for i, house in enumerate(houses):
                        assignment[house] = {
                            'name': name_perm[i],
                            'color': color_perm[i],
                            'phone': phone_perm[i],
                            'occupation': occup_perm[i]
                        }
                    
                    # Check all constraints
                    # Clue 2: Bob is in the second house
                    if assignment[2]['name'] != 'Bob':
                        continue
                    
                    # Clue 3: The person who uses a Samsung Galaxy S21 is the person who is a doctor
                    samsung_house = None
                    doctor_house = None
                    for house in houses:
                        if assignment[house]['phone'] == 'samsung galaxy s21':
                            samsung_house = house
                        if assignment[house]['occupation'] == 'doctor':
                            doctor_house = house
                    if samsung_house != doctor_house:
                        continue
                    
                    # Clue 4: The person who is a doctor is the person who loves blue
                    blue_house = None
                    for house in houses:
                        if assignment[house]['color'] == 'blue':
                            blue_house = house
                    if doctor_house != blue_house:
                        continue
                    
                    # Clue 5: The person whose favorite color is green is not in the fifth house
                    if assignment[5]['color'] == 'green':
                        continue
                    
                    # Clue 6: The person who is a lawyer is the person who uses a OnePlus 9
                    lawyer_house = None
                    oneplus_house = None
                    for house in houses:
                        if assignment[house]['occupation'] == 'lawyer':
                            lawyer_house = house
                        if assignment[house]['phone'] == 'oneplus 9':
                            oneplus_house = house
                    if lawyer_house != oneplus_house:
                        continue
                    
                    # Clue 7: The person who loves blue is directly left of the person whose favorite color is red
                    red_house = None
                    for house in houses:
                        if assignment[house]['color'] == 'red':
                            red_house = house
                    if blue_house + 1 != red_house:
                        continue
                    
                    # Clue 8: The person who is a lawyer is somewhere to the right of the person who uses a Samsung Galaxy S21
                    if lawyer_house <= samsung_house:
                        continue
                    
                    # Clue 9: There is one house between the person who uses a Google Pixel 6 and the person who uses a Huawei P50
                    pixel_house = None
                    huawei_house = None
                    for house in houses:
                        if assignment[house]['phone'] == 'google pixel 6':
                            pixel_house = house
                        if assignment[house]['phone'] == 'huawei p50':
                            huawei_house = house
                    if abs(pixel_house - huawei_house) != 2:
                        continue
                    
                    # Clue 10: Arnold is the person who is an engineer
                    arnold_house = None
                    engineer_house = None
                    for house in houses:
                        if assignment[house]['name'] == 'Arnold':
                            arnold_house = house
                        if assignment[house]['occupation'] == 'engineer':
                            engineer_house = house
                    if arnold_house != engineer_house:
                        continue
                    
                    # Clue 11: Alice is the person who loves yellow
                    alice_house = None
                    yellow_house = None
                    for house in houses:
                        if assignment[house]['name'] == 'Alice':
                            alice_house = house
                        if assignment[house]['color'] == 'yellow':
                            yellow_house = house
                    if alice_house != yellow_house:
                        continue
                    
                    # Clue 12: The person who uses a Google Pixel 6 is Eric
                    if assignment[pixel_house]['name'] != 'Eric':
                        continue
                    
                    # Clue 13: The person who uses a Google Pixel 6 is the person who is a teacher
                    if assignment[pixel_house]['occupation'] != 'teacher':
                        continue
                    
                    # Clue 14: The person whose favorite color is red is somewhere to the right of the person who is a teacher
                    if red_house <= pixel_house:
                        continue
                    
                    # Clue 1: The person who is an engineer is somewhere to the right of the person who is a lawyer
                    if engineer_house <= lawyer_house:
                        continue
                    
                    # If we reach here, all constraints are satisfied
                    # Format the solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Color", "PhoneModel", "Occupation"],
                            "rows": []
                        }
                    }
                    
                    for house in sorted(assignment.keys()):
                        row = [
                            str(house),
                            assignment[house]['name'],
                            assignment[house]['color'],
                            assignment[house]['phone'],
                            assignment[house]['occupation']
                        ]
                        solution["solution"]["rows"].append(row)
                    
                    return solution
    
    return None

def main():
    solution = solve_puzzle()
    if solution:
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"solution": {"header": [], "rows": []}}, indent=2))

if __name__ == "__main__":
    main()