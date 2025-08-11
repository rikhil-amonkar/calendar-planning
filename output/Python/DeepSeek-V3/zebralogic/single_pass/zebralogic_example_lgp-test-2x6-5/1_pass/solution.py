import json
from itertools import permutations

def solve_puzzle():
    # Define all possible attributes
    names = ['Arnold', 'Eric']
    occupations = ['engineer', 'doctor']
    birthday_months = ['april', 'sept']
    house_styles = ['victorian', 'colonial']
    heights = ['very short', 'short']
    cigars = ['pall mall', 'prince']
    
    # Generate all possible permutations for each attribute
    for name_perm in permutations(names):
        for occ_perm in permutations(occupations):
            for month_perm in permutations(birthday_months):
                for style_perm in permutations(house_styles):
                    for height_perm in permutations(heights):
                        for cigar_perm in permutations(cigars):
                            # Assign attributes to houses
                            solution = {
                                1: {
                                    'Name': name_perm[0],
                                    'occupation': occ_perm[0],
                                    'birthday month': month_perm[0],
                                    'house style': style_perm[0],
                                    'height': height_perm[0],
                                    'cigar': cigar_perm[0]
                                },
                                2: {
                                    'Name': name_perm[1],
                                    'occupation': occ_perm[1],
                                    'birthday month': month_perm[1],
                                    'house style': style_perm[1],
                                    'height': height_perm[1],
                                    'cigar': cigar_perm[1]
                                }
                            }
                            
                            # Check constraints
                            # Constraint 1: The person who is an engineer is in the first house.
                            if solution[1]['occupation'] != 'engineer':
                                continue
                            
                            # Constraint 2: The person whose birthday is in April and the person who is a doctor are next to each other.
                            april_house = None
                            doctor_house = None
                            for house in [1, 2]:
                                if solution[house]['birthday month'] == 'april':
                                    april_house = house
                                if solution[house]['occupation'] == 'doctor':
                                    doctor_house = house
                            if abs(april_house - doctor_house) != 1:
                                continue
                            
                            # Constraint 3: The person living in a colonial-style house is the person who is an engineer.
                            if solution[1]['house style'] != 'colonial':
                                continue
                            
                            # Constraint 4: The person who is very short is the person who is an engineer.
                            if solution[1]['height'] != 'very short':
                                continue
                            
                            # Constraint 5: The person who is short is the person partial to Pall Mall.
                            for house in [1, 2]:
                                if solution[house]['height'] == 'short' and solution[house]['cigar'] != 'pall mall':
                                    break
                                if solution[house]['height'] != 'short' and solution[house]['cigar'] == 'pall mall':
                                    break
                            else:
                                pass  # All checks passed
                                # Constraint 6: The person who is an engineer is Eric.
                                if solution[1]['Name'] != 'Eric':
                                    continue
                                
                                # Prepare the output
                                output = {
                                    "solution": {
                                        "header": ["House", "Name", "occupation", "birthday month", "house style", "height", "cigar"],
                                        "rows": [
                                            ["1", solution[1]['Name'], solution[1]['occupation'], solution[1]['birthday month'], solution[1]['house style'], solution[1]['height'], solution[1]['cigar']],
                                            ["2", solution[2]['Name'], solution[2]['occupation'], solution[2]['birthday month'], solution[2]['house style'], solution[2]['height'], solution[2]['cigar']]
                                        ]
                                    }
                                }
                                return output
    return {}

solution = solve_puzzle()
print(json.dumps(solution, indent=2))