import json
from itertools import permutations

def solve_puzzle():
    # Define all possible options for each category
    names = ['Arnold', 'Eric']
    occupations = ['engineer', 'doctor']
    birthdays = ['april', 'sept']
    house_styles = ['victorian', 'colonial']
    heights = ['very short', 'short']
    cigars = ['pall mall', 'prince']
    
    # Generate all possible permutations for each house
    for name1, name2 in permutations(names, 2):
        for occ1, occ2 in permutations(occupations, 2):
            for bday1, bday2 in permutations(birthdays, 2):
                for style1, style2 in permutations(house_styles, 2):
                    for height1, height2 in permutations(heights, 2):
                        for cigar1, cigar2 in permutations(cigars, 2):
                            # Assign to houses
                            house1 = {
                                'House': '1',
                                'Name': name1,
                                'Occupation': occ1,
                                'Birthday': bday1,
                                'HouseStyle': style1,
                                'Height': height1,
                                'Cigar': cigar1
                            }
                            house2 = {
                                'House': '2',
                                'Name': name2,
                                'Occupation': occ2,
                                'Birthday': bday2,
                                'HouseStyle': style2,
                                'Height': height2,
                                'Cigar': cigar2
                            }
                            
                            # Apply constraints
                            # Constraint 1: The person who is an engineer is in the first house.
                            if house1['Occupation'] != 'engineer':
                                continue
                            
                            # Constraint 2: The person whose birthday is in April and the person who is a doctor are next to each other.
                            # Since there are only 2 houses, they must be adjacent
                            april_house = house1 if house1['Birthday'] == 'april' else (house2 if house2['Birthday'] == 'april' else None)
                            doctor_house = house1 if house1['Occupation'] == 'doctor' else (house2 if house2['Occupation'] == 'doctor' else None)
                            if april_house is None or doctor_house is None:
                                continue
                            if abs(int(april_house['House']) - int(doctor_house['House'])) != 1:
                                continue
                            
                            # Constraint 3: The person living in a colonial-style house is the person who is an engineer.
                            if house1['HouseStyle'] != 'colonial' or house1['Occupation'] != 'engineer':
                                continue
                            
                            # Constraint 4: The person who is very short is the person who is an engineer.
                            if house1['Height'] != 'very short' or house1['Occupation'] != 'engineer':
                                continue
                            
                            # Constraint 5: The person who is short is the person partial to Pall Mall.
                            if (house1['Height'] == 'short' and house1['Cigar'] != 'pall mall') or (house2['Height'] == 'short' and house2['Cigar'] != 'pall mall'):
                                continue
                            
                            # Constraint 6: The person who is an engineer is Eric.
                            if house1['Name'] != 'Eric':
                                continue
                            
                            # If all constraints are satisfied, return the solution
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Occupation", "Birthday", "HouseStyle", "Height", "Cigar"],
                                    "rows": [
                                        [house1['House'], house1['Name'], house1['Occupation'], house1['Birthday'], house1['HouseStyle'], house1['Height'], house1['Cigar']],
                                        [house2['House'], house2['Name'], house2['Occupation'], house2['Birthday'], house2['HouseStyle'], house2['Height'], house2['Cigar']]
                                    ]
                                }
                            }
                            return json.dumps(solution, indent=2)
    
    return json.dumps({"solution": {"header": [], "rows": []}})

print(solve_puzzle())