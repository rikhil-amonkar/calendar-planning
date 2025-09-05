import json
from itertools import permutations

def main():
    # Define all possible values for each attribute
    names = ['Arnold', 'Eric']
    occupations = ['engineer', 'doctor']
    birthdays = ['april', 'sept']
    house_styles = ['victorian', 'colonial']
    heights = ['very short', 'short']
    cigars = ['pall mall', 'prince']
    
    # Generate all possible permutations for each attribute
    for name_perm in permutations(names):
        for occ_perm in permutations(occupations):
            for bday_perm in permutations(birthdays):
                for style_perm in permutations(house_styles):
                    for height_perm in permutations(heights):
                        for cigar_perm in permutations(cigars):
                            
                            # Create assignment for house 1
                            house1 = {
                                'House': '1',
                                'Name': name_perm[0],
                                'Occupation': occ_perm[0],
                                'Birthday': bday_perm[0],
                                'HouseStyle': style_perm[0],
                                'Height': height_perm[0],
                                'Cigar': cigar_perm[0]
                            }
                            
                            # Create assignment for house 2
                            house2 = {
                                'House': '2',
                                'Name': name_perm[1],
                                'Occupation': occ_perm[1],
                                'Birthday': bday_perm[1],
                                'HouseStyle': style_perm[1],
                                'Height': height_perm[1],
                                'Cigar': cigar_perm[1]
                            }
                            
                            # Check clue 1: The person who is an engineer is in the first house.
                            if house1['Occupation'] != 'engineer':
                                continue
                                
                            # Check clue 2: The person whose birthday is in April and the person who is a doctor are next to each other.
                            # Since there are only 2 houses, they are always adjacent
                            april_doctor_found = False
                            for house in [house1, house2]:
                                if house['Birthday'] == 'april':
                                    other_house = house2 if house['House'] == '1' else house1
                                    if other_house['Occupation'] == 'doctor':
                                        april_doctor_found = True
                                        break
                            if not april_doctor_found:
                                continue
                                
                            # Check clue 3: The person living in a colonial-style house is the person who is an engineer.
                            if house1['Occupation'] == 'engineer' and house1['HouseStyle'] != 'colonial':
                                continue
                            if house2['Occupation'] == 'engineer' and house2['HouseStyle'] != 'colonial':
                                continue
                                
                            # Check clue 4: The person who is very short is the person who is an engineer.
                            if house1['Occupation'] == 'engineer' and house1['Height'] != 'very short':
                                continue
                            if house2['Occupation'] == 'engineer' and house2['Height'] != 'very short':
                                continue
                                
                            # Check clue 5: The person who is short is the person partial to Pall Mall.
                            if house1['Height'] == 'short' and house1['Cigar'] != 'pall mall':
                                continue
                            if house2['Height'] == 'short' and house2['Cigar'] != 'pall mall':
                                continue
                                
                            # Check clue 6: The person who is an engineer is Eric.
                            if house1['Occupation'] == 'engineer' and house1['Name'] != 'Eric':
                                continue
                            if house2['Occupation'] == 'engineer' and house2['Name'] != 'Eric':
                                continue
                            
                            # If we get here, all constraints are satisfied
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Occupation", "Birthday", "HouseStyle", "Height", "Cigar"],
                                    "rows": [
                                        [house1['House'], house1['Name'], house1['Occupation'], house1['Birthday'], house1['HouseStyle'], house1['Height'], house1['Cigar']],
                                        [house2['House'], house2['Name'], house2['Occupation'], house2['Birthday'], house2['HouseStyle'], house2['Height'], house2['Cigar']]
                                    ]
                                }
                            }
                            
                            print(json.dumps(solution, indent=2))
                            return
                            
    print('{"solution": {"header": [], "rows": []}}')

if __name__ == "__main__":
    main()