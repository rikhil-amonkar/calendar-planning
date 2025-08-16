import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    houses = ['1', '2', '3', '4', '5']
    names = ['Eric', 'Peter', 'Alice', 'Bob', 'Arnold']
    nationalities = ['norwegian', 'brit', 'swede', 'dane', 'german']
    vacations = ['cruise', 'mountain', 'camping', 'beach', 'city']
    educations = ['bachelor', 'master', 'associate', 'doctorate', 'high school']
    occupations = ['artist', 'doctor', 'engineer', 'teacher', 'lawyer']
    
    # We'll represent each house as a dictionary with the categories
    # Initialize all possibilities
    for name_order in permutations(names):
        for nat_order in permutations(nationalities):
            for vac_order in permutations(vacations):
                for edu_order in permutations(educations):
                    for occ_order in permutations(occupations):
                        # Create a list of houses with current permutation
                        solution = []
                        for i in range(5):
                            house = {
                                'House': str(i+1),
                                'Name': name_order[i],
                                'Nationality': nat_order[i],
                                'Vacation': vac_order[i],
                                'Education': edu_order[i],
                                'Occupation': occ_order[i]
                            }
                            solution.append(house)
                        
                        # Check all constraints
                        valid = True
                        
                        # Clue 5: Peter is not in the first house.
                        if solution[0]['Name'] == 'Peter':
                            valid = False
                        
                        # Clue 6: The person who is an artist is Peter.
                        peter_found = False
                        for house in solution:
                            if house['Name'] == 'Peter' and house['Occupation'] != 'artist':
                                valid = False
                            if house['Occupation'] == 'artist' and house['Name'] != 'Peter':
                                valid = False
                        
                        # Clue 12: The person who is an artist is the Swedish person.
                        for house in solution:
                            if house['Occupation'] == 'artist' and house['Nationality'] != 'swede':
                                valid = False
                        
                        # Clue 14: The person who enjoys camping trips is Eric.
                        for house in solution:
                            if house['Vacation'] == 'camping' and house['Name'] != 'Eric':
                                valid = False
                        
                        # Clue 10: The person who enjoys camping trips is the British person.
                        for house in solution:
                            if house['Vacation'] == 'camping' and house['Nationality'] != 'brit':
                                valid = False
                        
                        # Clue 7: The person who enjoys camping trips is the person with a master's degree.
                        for house in solution:
                            if house['Vacation'] == 'camping' and house['Education'] != 'master':
                                valid = False
                        
                        # Clue 19: The person with a bachelor's degree is in the third house.
                        if solution[2]['Education'] != 'bachelor':
                            valid = False
                        
                        # Clue 11: The Norwegian and the person with a bachelor's degree are next to each other.
                        norwegian_pos = None
                        for i, house in enumerate(solution):
                            if house['Nationality'] == 'norwegian':
                                norwegian_pos = i
                        if norwegian_pos is None:
                            valid = False
                        else:
                            if abs(norwegian_pos - 2) != 1:  # bachelor is in house 3 (index 2)
                                valid = False
                        
                        # Clue 15: Alice is the German.
                        for house in solution:
                            if house['Name'] == 'Alice' and house['Nationality'] != 'german':
                                valid = False
                        
                        # Clue 13: Bob is not in the fourth house.
                        if solution[3]['Name'] == 'Bob':
                            valid = False
                        
                        # Clue 3: The person with a doctorate is somewhere to the left of Bob.
                        doctorate_pos = None
                        bob_pos = None
                        for i, house in enumerate(solution):
                            if house['Education'] == 'doctorate':
                                doctorate_pos = i
                            if house['Name'] == 'Bob':
                                bob_pos = i
                        if doctorate_pos is None or bob_pos is None:
                            valid = False
                        else:
                            if doctorate_pos >= bob_pos:
                                valid = False
                        
                        # Clue 8: The Dane is somewhere to the right of the person who is a doctor.
                        dane_pos = None
                        doctor_pos = None
                        for i, house in enumerate(solution):
                            if house['Nationality'] == 'dane':
                                dane_pos = i
                            if house['Occupation'] == 'doctor':
                                doctor_pos = i
                        if dane_pos is None or doctor_pos is None:
                            valid = False
                        else:
                            if dane_pos <= doctor_pos:
                                valid = False
                        
                        # Clue 4: The person with an associate's degree is the person who likes going on cruises.
                        for house in solution:
                            if house['Education'] == 'associate' and house['Vacation'] != 'cruise':
                                valid = False
                            if house['Vacation'] == 'cruise' and house['Education'] != 'associate':
                                valid = False
                        
                        # Clue 1: The person who likes going on cruises is the person who is a lawyer.
                        for house in solution:
                            if house['Vacation'] == 'cruise' and house['Occupation'] != 'lawyer':
                                valid = False
                            if house['Occupation'] == 'lawyer' and house['Vacation'] != 'cruise':
                                valid = False
                        
                        # Clue 9: The person with an associate's degree is directly left of the person who is an engineer.
                        associate_pos = None
                        for i, house in enumerate(solution):
                            if house['Education'] == 'associate':
                                associate_pos = i
                        if associate_pos is None:
                            valid = False
                        else:
                            if associate_pos == 4 or solution[associate_pos + 1]['Occupation'] != 'engineer':
                                valid = False
                        
                        # Clue 2: The person who loves beach vacations is directly left of Arnold.
                        beach_pos = None
                        arnold_pos = None
                        for i, house in enumerate(solution):
                            if house['Vacation'] == 'beach':
                                beach_pos = i
                            if house['Name'] == 'Arnold':
                                arnold_pos = i
                        if beach_pos is None or arnold_pos is None:
                            valid = False
                        else:
                            if beach_pos + 1 != arnold_pos:
                                valid = False
                        
                        # Clue 16: The person who loves beach vacations is somewhere to the left of the person who prefers city breaks.
                        city_pos = None
                        for i, house in enumerate(solution):
                            if house['Vacation'] == 'city':
                                city_pos = i
                        if beach_pos is None or city_pos is None:
                            valid = False
                        else:
                            if beach_pos >= city_pos:
                                valid = False
                        
                        # Clue 17: The person who enjoys mountain retreats is in the fifth house.
                        if solution[4]['Vacation'] != 'mountain':
                            valid = False
                        
                        # Clue 18: The person who likes going on cruises is somewhere to the right of the person who loves beach vacations.
                        cruise_pos = None
                        for i, house in enumerate(solution):
                            if house['Vacation'] == 'cruise':
                                cruise_pos = i
                        if beach_pos is None or cruise_pos is None:
                            valid = False
                        else:
                            if cruise_pos <= beach_pos:
                                valid = False
                        
                        if valid:
                            # Prepare the output
                            output = {
                                "solution": {
                                    "header": ["House", "Name", "Nationality", "Vacation", "Education", "Occupation"],
                                    "rows": []
                                }
                            }
                            for house in solution:
                                row = [
                                    house['House'],
                                    house['Name'],
                                    house['Nationality'],
                                    house['Vacation'],
                                    house['Education'],
                                    house['Occupation']
                                ]
                                output["solution"]["rows"].append(row)
                            return json.dumps(output, indent=2)
    
    return json.dumps({"solution": {"header": [], "rows": []}})

print(solve_puzzle())