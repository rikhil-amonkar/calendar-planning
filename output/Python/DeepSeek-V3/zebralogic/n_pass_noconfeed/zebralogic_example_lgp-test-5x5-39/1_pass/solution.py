import json
from itertools import permutations

def main():
    # Define all possible values for each category
    names = ['Alice', 'Eric', 'Bob', 'Peter', 'Arnold']
    birthdays = ['mar', 'april', 'sept', 'feb', 'jan']
    mothers = ['Holly', 'Janelle', 'Kailyn', 'Penny', 'Aniya']
    occupations = ['engineer', 'doctor', 'lawyer', 'artist', 'teacher']
    hair_colors = ['red', 'blonde', 'black', 'gray', 'brown']
    
    houses = [1, 2, 3, 4, 5]
    
    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for bday_perm in permutations(birthdays):
            for mother_perm in permutations(mothers):
                for occ_perm in permutations(occupations):
                    for hair_perm in permutations(hair_colors):
                        # Create assignment dictionaries for each house
                        assignment = {}
                        for i, house in enumerate(houses):
                            assignment[house] = {
                                'Name': name_perm[i],
                                'Birthday': bday_perm[i],
                                'Mother': mother_perm[i],
                                'Occupation': occ_perm[i],
                                'HairColor': hair_perm[i]
                            }
                        
                        # Check all constraints
                        # Clue 1: The person whose birthday is in March is in the fifth house.
                        if assignment[5]['Birthday'] != 'mar':
                            continue
                            
                        # Clue 2: The person whose birthday is in February is in the first house.
                        if assignment[1]['Birthday'] != 'feb':
                            continue
                            
                        # Clue 3: The person who is a doctor is Eric.
                        doctor_house = None
                        for house in houses:
                            if assignment[house]['Occupation'] == 'doctor':
                                doctor_house = house
                                break
                        if doctor_house is None or assignment[doctor_house]['Name'] != 'Eric':
                            continue
                            
                        # Clue 4: The person whose mother's name is Janelle is in the third house.
                        if assignment[3]['Mother'] != 'Janelle':
                            continue
                            
                        # Clue 5: The person who is an artist is the person who has brown hair.
                        artist_house = None
                        brown_hair_house = None
                        for house in houses:
                            if assignment[house]['Occupation'] == 'artist':
                                artist_house = house
                            if assignment[house]['HairColor'] == 'brown':
                                brown_hair_house = house
                        if artist_house != brown_hair_house:
                            continue
                            
                        # Clue 6: The person who is an artist is in the fourth house.
                        if assignment[4]['Occupation'] != 'artist':
                            continue
                            
                        # Clue 7: The person whose mother's name is Penny is somewhere to the left of the person who has black hair.
                        penny_mother_house = None
                        black_hair_house = None
                        for house in houses:
                            if assignment[house]['Mother'] == 'Penny':
                                penny_mother_house = house
                            if assignment[house]['HairColor'] == 'black':
                                black_hair_house = house
                        if penny_mother_house is None or black_hair_house is None or penny_mother_house >= black_hair_house:
                            continue
                            
                        # Clue 8: Peter is the person who has black hair.
                        if assignment[black_hair_house]['Name'] != 'Peter':
                            continue
                            
                        # Clue 9: The person who has gray hair is the person who is a teacher.
                        gray_hair_house = None
                        teacher_house = None
                        for house in houses:
                            if assignment[house]['HairColor'] == 'gray':
                                gray_hair_house = house
                            if assignment[house]['Occupation'] == 'teacher':
                                teacher_house = house
                        if gray_hair_house != teacher_house:
                            continue
                            
                        # Clue 10: Alice is The person whose mother's name is Kailyn.
                        alice_house = None
                        kailyn_mother_house = None
                        for house in houses:
                            if assignment[house]['Name'] == 'Alice':
                                alice_house = house
                            if assignment[house]['Mother'] == 'Kailyn':
                                kailyn_mother_house = house
                        if alice_house != kailyn_mother_house:
                            continue
                            
                        # Clue 11: Arnold is somewhere to the right of the person whose birthday is in September.
                        arnold_house = None
                        sept_bday_house = None
                        for house in houses:
                            if assignment[house]['Name'] == 'Arnold':
                                arnold_house = house
                            if assignment[house]['Birthday'] == 'sept':
                                sept_bday_house = house
                        if arnold_house <= sept_bday_house:
                            continue
                            
                        # Clue 12: The person who has brown hair is the person whose birthday is in January.
                        if assignment[brown_hair_house]['Birthday'] != 'jan':
                            continue
                            
                        # Clue 13: Arnold is the person who has blonde hair.
                        if assignment[arnold_house]['HairColor'] != 'blonde':
                            continue
                            
                        # Clue 14: The person whose mother's name is Holly is the person who has black hair.
                        if assignment[black_hair_house]['Mother'] != 'Holly':
                            continue
                            
                        # Clue 15: Peter is the person who is a lawyer.
                        if assignment[black_hair_house]['Occupation'] != 'lawyer':
                            continue
                            
                        # Clue 16: The person whose birthday is in September is somewhere to the left of The person whose mother's name is Kailyn.
                        if sept_bday_house >= kailyn_mother_house:
                            continue
                            
                        # Clue 17: Alice is the person who has gray hair.
                        if assignment[alice_house]['HairColor'] != 'gray':
                            continue
                            
                        # If we reach here, all constraints are satisfied
                        # Format the solution
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Birthday", "Mother", "Occupation", "HairColor"],
                                "rows": []
                            }
                        }
                        
                        for house in sorted(assignment.keys()):
                            row = [
                                str(house),
                                assignment[house]['Name'],
                                assignment[house]['Birthday'],
                                assignment[house]['Mother'],
                                assignment[house]['Occupation'],
                                assignment[house]['HairColor']
                            ]
                            solution["solution"]["rows"].append(row)
                        
                        print(json.dumps(solution, indent=2))
                        return
    
    # If no solution found
    print(json.dumps({"solution": {"header": [], "rows": []}}, indent=2))

if __name__ == "__main__":
    main()