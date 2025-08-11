import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    houses = [1, 2, 3, 4, 5]
    names = ['Eric', 'Peter', 'Alice', 'Bob', 'Arnold']
    nationalities = ['norwegian', 'brit', 'swede', 'dane', 'german']
    vacations = ['cruise', 'mountain', 'camping', 'beach', 'city']
    educations = ['bachelor', 'master', 'associate', 'doctorate', 'high school']
    occupations = ['artist', 'doctor', 'engineer', 'teacher', 'lawyer']

    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for nat_perm in permutations(nationalities):
            for vac_perm in permutations(vacations):
                for edu_perm in permutations(educations):
                    for occ_perm in permutations(occupations):
                        # Create a dictionary to hold the assignments for each house
                        solution = {}
                        for i in range(5):
                            solution[i+1] = {
                                'Name': name_perm[i],
                                'Nationality': nat_perm[i],
                                'Vacation': vac_perm[i],
                                'Education': edu_perm[i],
                                'Occupation': occ_perm[i]
                            }

                        # Apply the constraints one by one
                        valid = True

                        # Constraint 5: Peter is not in the first house.
                        if solution[1]['Name'] == 'Peter':
                            valid = False
                            continue

                        # Constraint 6: The person who is an artist is Peter.
                        peter_house = None
                        for house in solution:
                            if solution[house]['Name'] == 'Peter':
                                peter_house = house
                                break
                        if peter_house is None or solution[peter_house]['Occupation'] != 'artist':
                            valid = False
                            continue

                        # Constraint 12: The person who is an artist is the Swedish person.
                        if solution[peter_house]['Nationality'] != 'swede':
                            valid = False
                            continue

                        # Constraint 14: The person who enjoys camping trips is Eric.
                        eric_house = None
                        for house in solution:
                            if solution[house]['Name'] == 'Eric':
                                eric_house = house
                                break
                        if eric_house is None or solution[eric_house]['Vacation'] != 'camping':
                            valid = False
                            continue

                        # Constraint 10: The person who enjoys camping trips is the British person.
                        if solution[eric_house]['Nationality'] != 'brit':
                            valid = False
                            continue

                        # Constraint 7: The person who enjoys camping trips is the person with a master's degree.
                        if solution[eric_house]['Education'] != 'master':
                            valid = False
                            continue

                        # Constraint 19: The person with a bachelor's degree is in the third house.
                        if solution[3]['Education'] != 'bachelor':
                            valid = False
                            continue

                        # Constraint 11: The Norwegian and the person with a bachelor's degree are next to each other.
                        norwegian_house = None
                        for house in solution:
                            if solution[house]['Nationality'] == 'norwegian':
                                norwegian_house = house
                                break
                        if norwegian_house is None or abs(norwegian_house - 3) != 1:
                            valid = False
                            continue

                        # Constraint 15: Alice is the German.
                        alice_house = None
                        for house in solution:
                            if solution[house]['Name'] == 'Alice':
                                alice_house = house
                                break
                        if alice_house is None or solution[alice_house]['Nationality'] != 'german':
                            valid = False
                            continue

                        # Constraint 4: The person with an associate's degree is the person who likes going on cruises.
                        cruise_house = None
                        for house in solution:
                            if solution[house]['Education'] == 'associate':
                                if solution[house]['Vacation'] != 'cruise':
                                    valid = False
                                    break
                                cruise_house = house
                        if not valid:
                            continue

                        # Constraint 1: The person who likes going on cruises is the person who is a lawyer.
                        if cruise_house is not None and solution[cruise_house]['Occupation'] != 'lawyer':
                            valid = False
                            continue

                        # Constraint 9: The person with an associate's degree is directly left of the person who is an engineer.
                        if cruise_house is not None:
                            engineer_house = cruise_house + 1
                            if engineer_house > 5 or solution[engineer_house]['Occupation'] != 'engineer':
                                valid = False
                                continue

                        # Constraint 2: The person who loves beach vacations is directly left of Arnold.
                        beach_house = None
                        arnold_house = None
                        for house in solution:
                            if solution[house]['Name'] == 'Arnold':
                                arnold_house = house
                                break
                        if arnold_house is None:
                            valid = False
                            continue
                        beach_house = arnold_house - 1
                        if beach_house < 1 or solution[beach_house]['Vacation'] != 'beach':
                            valid = False
                            continue

                        # Constraint 16: The person who loves beach vacations is somewhere to the left of the person who prefers city breaks.
                        city_house = None
                        for house in solution:
                            if solution[house]['Vacation'] == 'city':
                                city_house = house
                                break
                        if city_house is None or beach_house >= city_house:
                            valid = False
                            continue

                        # Constraint 18: The person who likes going on cruises is somewhere to the right of the person who loves beach vacations.
                        if cruise_house is not None and cruise_house <= beach_house:
                            valid = False
                            continue

                        # Constraint 3: The person with a doctorate is somewhere to the left of Bob.
                        bob_house = None
                        doctorate_house = None
                        for house in solution:
                            if solution[house]['Name'] == 'Bob':
                                bob_house = house
                            if solution[house]['Education'] == 'doctorate':
                                doctorate_house = house
                        if bob_house is None or doctorate_house is None or doctorate_house >= bob_house:
                            valid = False
                            continue

                        # Constraint 13: Bob is not in the fourth house.
                        if bob_house == 4:
                            valid = False
                            continue

                        # Constraint 8: The Dane is somewhere to the right of the person who is a doctor.
                        doctor_house = None
                        dane_house = None
                        for house in solution:
                            if solution[house]['Occupation'] == 'doctor':
                                doctor_house = house
                            if solution[house]['Nationality'] == 'dane':
                                dane_house = house
                        if doctor_house is None or dane_house is None or dane_house <= doctor_house:
                            valid = False
                            continue

                        # Constraint 17: The person who enjoys mountain retreats is in the fifth house.
                        if solution[5]['Vacation'] != 'mountain':
                            valid = False
                            continue

                        # If all constraints are satisfied, return the solution
                        if valid:
                            result = {
                                "solution": {
                                    "header": ["House", "Name", "Nationality", "Vacation", "Education", "Occupation"],
                                    "rows": []
                                }
                            }
                            for house in sorted(solution.keys()):
                                row = [
                                    str(house),
                                    solution[house]['Name'],
                                    solution[house]['Nationality'],
                                    solution[house]['Vacation'],
                                    solution[house]['Education'],
                                    solution[house]['Occupation']
                                ]
                                result["solution"]["rows"].append(row)
                            return json.dumps(result, indent=2)

    return json.dumps({"solution": {"header": [], "rows": []}})

print(solve_puzzle())