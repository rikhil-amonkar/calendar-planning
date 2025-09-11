import itertools
import json

names = ['Eric', 'Peter', 'Alice', 'Arnold']
cars = ['tesla model 3', 'honda civic', 'toyota camry', 'ford f150']
birthdays = ['jan', 'april', 'sept', 'feb']
hobbies = ['painting', 'cooking', 'gardening', 'photography']

for names_perm in itertools.permutations(names):
    p = names_perm.index('Peter')  # position of Peter
    a = names_perm.index('Arnold')  # position of Arnold
    
    # Generate car permutations
    other_car_positions = [i for i in range(4) if i != p and i != a]
    remaining_cars = ['honda civic', 'ford f150']
    for car_options in itertools.permutations(remaining_cars):
        cars_perm = [''] * 4
        cars_perm[p] = 'toyota camry'
        cars_perm[a] = 'tesla model 3'
        cars_perm[other_car_positions[0]] = car_options[0]
        cars_perm[other_car_positions[1]] = car_options[1]
        
        # Check clue 4: Honda directly left of Tesla
        tesla_pos = a
        if tesla_pos > 0 and cars_perm[tesla_pos - 1] == 'honda civic':
            # proceed
            pass
        else:
            continue  # skip if clue 4 not satisfied
        
        # Generate birthday permutations
        other_bday_positions = [i for i in range(4) if i != p and i != a]
        remaining_bdays = ['sept', 'feb']
        for bday_options in itertools.permutations(remaining_bdays):
            bdays_perm = [''] * 4
            bdays_perm[p] = 'jan'
            bdays_perm[a] = 'april'
            bdays_perm[other_bday_positions[0]] = bday_options[0]
            bdays_perm[other_bday_positions[1]] = bday_options[1]
            
            # Find feb_pos
            feb_pos = None
            for i in range(4):
                if bdays_perm[i] == 'feb':
                    feb_pos = i
                    break
            
            # Generate hobby permutations
            alice_pos = names_perm.index('Alice')
            eric_pos = names_perm.index('Eric')
            
            # The hobbies_perm must have 'photography' at alice_pos and 'cooking' at feb_pos
            remaining_hobbies = ['painting', 'gardening']
            other_hobby_positions = []
            for i in range(4):
                if i != alice_pos and i != feb_pos:
                    other_hobby_positions.append(i)
            # other_hobby_positions has two elements
            for hobby_options in itertools.permutations(remaining_hobbies):
                hobbies_perm = [''] * 4
                hobbies_perm[alice_pos] = 'photography'
                hobbies_perm[feb_pos] = 'cooking'
                hobbies_perm[other_hobby_positions[0]] = hobby_options[0]
                hobbies_perm[other_hobby_positions[1]] = hobby_options[1]
                
                # Check clue 5: one house between Tesla (a) and gardening
                gardening_pos = None
                for i in range(4):
                    if hobbies_perm[i] == 'gardening':
                        gardening_pos = i
                        break
                if abs(gardening_pos - a) != 2:
                    continue
                
                # Check clue 2: Alice is left of Eric
                if alice_pos >= eric_pos:
                    continue
                
                # Check clue 3: Alice is left of Peter
                if alice_pos >= p:
                    continue
                
                # Check clue 1: jan (Peter's position) is not in house 2 (index 1)
                if p == 1:
                    continue
                
                # All constraints satisfied. Now build the solution.
                solution_rows = []
                for i in range(4):
                    house_num = str(i + 1)
                    name = names_perm[i]
                    car = cars_perm[i]
                    birthday = bdays_perm[i]
                    hobby = hobbies_perm[i]
                    solution_rows.append([house_num, name, car, birthday, hobby])
                
                # Output JSON
                output = {
                    "solution": {
                        "header": ["House", "Name", "CarModel", "Birthday", "Hobby"],
                        "rows": solution_rows
                    }
                }
                print(json.dumps(output, indent=2))
                exit()  # since the solution is unique, exit after first found