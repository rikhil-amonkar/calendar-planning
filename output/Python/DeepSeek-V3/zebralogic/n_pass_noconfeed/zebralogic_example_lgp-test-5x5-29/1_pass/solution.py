import json
from itertools import permutations

def main():
    # Define all possible values for each category
    names = ['Eric', 'Peter', 'Alice', 'Bob', 'Arnold']
    nationalities = ['norwegian', 'brit', 'swede', 'dane', 'german']
    vacations = ['cruise', 'mountain', 'camping', 'beach', 'city']
    educations = ['bachelor', 'master', 'associate', 'doctorate', 'high school']
    occupations = ['artist', 'doctor', 'engineer', 'teacher', 'lawyer']
    
    houses = [1, 2, 3, 4, 5]
    
    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for nat_perm in permutations(nationalities):
            for vac_perm in permutations(vacations):
                for edu_perm in permutations(educations):
                    for occ_perm in permutations(occupations):
                        # Create assignment for each house
                        assignment = []
                        for i in range(5):
                            house = {
                                'house': i+1,
                                'name': name_perm[i],
                                'nationality': nat_perm[i],
                                'vacation': vac_perm[i],
                                'education': edu_perm[i],
                                'occupation': occ_perm[i]
                            }
                            assignment.append(house)
                        
                        # Check all constraints
                        valid = True
                        
                        # Clue 1: The person who likes going on cruises is the person who is a lawyer.
                        cruise_house = None
                        lawyer_house = None
                        for house in assignment:
                            if house['vacation'] == 'cruise':
                                cruise_house = house['house']
                            if house['occupation'] == 'lawyer':
                                lawyer_house = house['house']
                        if cruise_house != lawyer_house:
                            valid = False
                        
                        # Clue 2: The person who loves beach vacations is directly left of Arnold.
                        beach_house = None
                        arnold_house = None
                        for house in assignment:
                            if house['vacation'] == 'beach':
                                beach_house = house['house']
                            if house['name'] == 'Arnold':
                                arnold_house = house['house']
                        if beach_house is None or arnold_house is None or beach_house + 1 != arnold_house:
                            valid = False
                        
                        # Clue 3: The person with a doctorate is somewhere to the left of Bob.
                        doctorate_house = None
                        bob_house = None
                        for house in assignment:
                            if house['education'] == 'doctorate':
                                doctorate_house = house['house']
                            if house['name'] == 'Bob':
                                bob_house = house['house']
                        if doctorate_house is None or bob_house is None or doctorate_house >= bob_house:
                            valid = False
                        
                        # Clue 4: The person with an associate's degree is the person who likes going on cruises.
                        associate_house = None
                        for house in assignment:
                            if house['education'] == 'associate':
                                associate_house = house['house']
                        if associate_house != cruise_house:
                            valid = False
                        
                        # Clue 5: Peter is not in the first house.
                        peter_house = None
                        for house in assignment:
                            if house['name'] == 'Peter':
                                peter_house = house['house']
                        if peter_house == 1:
                            valid = False
                        
                        # Clue 6: The person who is an artist is Peter.
                        artist_house = None
                        for house in assignment:
                            if house['occupation'] == 'artist':
                                artist_house = house['house']
                        if artist_house != peter_house:
                            valid = False
                        
                        # Clue 7: The person who enjoys camping trips is the person with a master's degree.
                        camping_house = None
                        master_house = None
                        for house in assignment:
                            if house['vacation'] == 'camping':
                                camping_house = house['house']
                            if house['education'] == 'master':
                                master_house = house['house']
                        if camping_house != master_house:
                            valid = False
                        
                        # Clue 8: The Dane is somewhere to the right of the person who is a doctor.
                        dane_house = None
                        doctor_house = None
                        for house in assignment:
                            if house['nationality'] == 'dane':
                                dane_house = house['house']
                            if house['occupation'] == 'doctor':
                                doctor_house = house['house']
                        if dane_house is None or doctor_house is None or dane_house <= doctor_house:
                            valid = False
                        
                        # Clue 9: The person with an associate's degree is directly left of the person who is an engineer.
                        engineer_house = None
                        for house in assignment:
                            if house['occupation'] == 'engineer':
                                engineer_house = house['house']
                        if associate_house is None or engineer_house is None or associate_house + 1 != engineer_house:
                            valid = False
                        
                        # Clue 10: The person who enjoys camping trips is the British person.
                        brit_house = None
                        for house in assignment:
                            if house['nationality'] == 'brit':
                                brit_house = house['house']
                        if camping_house != brit_house:
                            valid = False
                        
                        # Clue 11: The Norwegian and the person with a bachelor's degree are next to each other.
                        norwegian_house = None
                        bachelor_house = None
                        for house in assignment:
                            if house['nationality'] == 'norwegian':
                                norwegian_house = house['house']
                            if house['education'] == 'bachelor':
                                bachelor_house = house['house']
                        if abs(norwegian_house - bachelor_house) != 1:
                            valid = False
                        
                        # Clue 12: The person who is an artist is the Swedish person.
                        swede_house = None
                        for house in assignment:
                            if house['nationality'] == 'swede':
                                swede_house = house['house']
                        if artist_house != swede_house:
                            valid = False
                        
                        # Clue 13: Bob is not in the fourth house.
                        if bob_house == 4:
                            valid = False
                        
                        # Clue 14: The person who enjoys camping trips is Eric.
                        eric_house = None
                        for house in assignment:
                            if house['name'] == 'Eric':
                                eric_house = house['house']
                        if camping_house != eric_house:
                            valid = False
                        
                        # Clue 15: Alice is the German.
                        alice_house = None
                        german_house = None
                        for house in assignment:
                            if house['name'] == 'Alice':
                                alice_house = house['house']
                            if house['nationality'] == 'german':
                                german_house = house['house']
                        if alice_house != german_house:
                            valid = False
                        
                        # Clue 16: The person who loves beach vacations is somewhere to the left of the person who prefers city breaks.
                        city_house = None
                        for house in assignment:
                            if house['vacation'] == 'city':
                                city_house = house['house']
                        if beach_house is None or city_house is None or beach_house >= city_house:
                            valid = False
                        
                        # Clue 17: The person who enjoys mountain retreats is in the fifth house.
                        mountain_house = None
                        for house in assignment:
                            if house['vacation'] == 'mountain':
                                mountain_house = house['house']
                        if mountain_house != 5:
                            valid = False
                        
                        # Clue 18: The person who likes going on cruises is somewhere to the right of the person who loves beach vacations.
                        if cruise_house is None or beach_house is None or cruise_house <= beach_house:
                            valid = False
                        
                        # Clue 19: The person with a bachelor's degree is in the third house.
                        if bachelor_house != 3:
                            valid = False
                        
                        if valid:
                            # Format the solution
                            result = {
                                "solution": {
                                    "header": ["House", "Name", "Nationality", "Vacation", "Education", "Occupation"],
                                    "rows": []
                                }
                            }
                            
                            for house in assignment:
                                row = [
                                    str(house['house']),
                                    house['name'],
                                    house['nationality'],
                                    house['vacation'],
                                    house['education'],
                                    house['occupation']
                                ]
                                result["solution"]["rows"].append(row)
                            
                            print(json.dumps(result, indent=2))
                            return
    
    print('{"solution": {"header": ["House", "Name", "Nationality", "Vacation", "Education", "Occupation"], "rows": []}}')

if __name__ == "__main__":
    main()