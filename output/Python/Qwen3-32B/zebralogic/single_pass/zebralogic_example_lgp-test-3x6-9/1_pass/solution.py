import itertools
import json

def solve_puzzle():
    names = ['Peter', 'Arnold', 'Eric']
    cars = ['toyota camry', 'ford f150', 'tesla model 3']
    house_styles = ['ranch', 'colonial', 'victorian']
    pets = ['cat', 'dog', 'fish']
    occupations = ['engineer', 'doctor', 'teacher']
    vacations = ['city', 'mountain', 'beach']
    
    # Generate permutations with constraints
    car_model_perms = [p for p in itertools.permutations(cars) if p[1] == 'toyota camry']
    house_style_perms = [p for p in itertools.permutations(house_styles) if p[2] == 'colonial']
    pet_perms = [p for p in itertools.permutations(pets) if p[0] == 'fish']
    name_perms = list(itertools.permutations(names))
    occupation_perms = list(itertools.permutations(occupations))
    vacation_perms = list(itertools.permutations(vacations))
    
    # Iterate through all combinations
    for name_p in name_perms:
        for car_p in car_model_perms:
            for house_p in house_style_perms:
                for pet_p in pet_perms:
                    for occ_p in occupation_perms:
                        for vac_p in vacation_perms:
                            # Check clue 3 and 4: vacation in second house
                            if vac_p[1] == 'mountain' or vac_p[1] == 'city':
                                continue
                            
                            # Check clue 7: Arnold has cat
                            arnold_index = name_p.index('Arnold')
                            if pet_p[arnold_index] != 'cat':
                                continue
                            
                            # Check clue 5: ranch is left of Peter
                            ranch_index = house_p.index('ranch')
                            peter_index = name_p.index('Peter')
                            if ranch_index >= peter_index:
                                continue
                            
                            # Check clue 8: Eric left of mountain
                            eric_index = name_p.index('Eric')
                            mountain_index = vac_p.index('mountain')
                            if eric_index >= mountain_index:
                                continue
                            
                            # Check clue 9: engineer not in third house
                            if occ_p[2] == 'engineer':
                                continue
                            
                            # Check clue 10: Tesla left of teacher
                            tesla_index = car_p.index('tesla model 3')
                            teacher_index = occ_p.index('teacher')
                            if tesla_index >= teacher_index:
                                continue
                            
                            # Check clue 11: dog is engineer
                            dog_index = pet_p.index('dog')
                            if occ_p[dog_index] != 'engineer':
                                continue
                            
                            # If all constraints are met, build the solution
                            rows = []
                            for i in range(3):
                                house_num = str(i + 1)
                                name = name_p[i]
                                car = car_p[i]
                                style = house_p[i]
                                pet = pet_p[i]
                                occ = occ_p[i]
                                vac = vac_p[i]
                                rows.append([house_num, name, car, style, pet, occ, vac])
                            
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "CarModel", "HouseStyle", "Pet", "Occupation", "Vacation"],
                                    "rows": rows
                                }
                            }
                            print(json.dumps(solution, indent=2))
                            return

solve_puzzle()