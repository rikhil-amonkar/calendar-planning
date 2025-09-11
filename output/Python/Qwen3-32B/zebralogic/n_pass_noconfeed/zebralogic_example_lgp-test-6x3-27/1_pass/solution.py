import itertools
import json

def solve_puzzle():
    names = ['Alice', 'Arnold', 'Eric', 'Peter', 'Bob', 'Carol']
    occupations = ['engineer', 'artist', 'doctor', 'teacher', 'nurse', 'lawyer']
    cars = ['chevrolet silverado', 'ford f150', 'honda civic', 'toyota camry', 'bmw 3 series', 'tesla model 3']
    
    for name_perm in itertools.permutations(names):
        # Check Carol is to the right of Eric and not in the sixth house
        eric_pos = name_perm.index('Eric')
        carol_pos = name_perm.index('Carol')
        if carol_pos <= eric_pos or carol_pos == 5:
            continue
        
        # Assign fixed occupations
        fixed_occupations = []
        remaining_occ_indices = []
        for i, name in enumerate(name_perm):
            if name == 'Eric':
                fixed_occupations.append('doctor')
            elif name == 'Arnold':
                fixed_occupations.append('artist')
            elif name == 'Bob':
                fixed_occupations.append('engineer')
            else:
                fixed_occupations.append(None)
                remaining_occ_indices.append(i)
        
        remaining_occupations = ['teacher', 'lawyer', 'nurse']
        for occ_perm in itertools.permutations(remaining_occupations):
            occupations_list = fixed_occupations.copy()
            for idx, occ in zip(remaining_occ_indices, occ_perm):
                occupations_list[idx] = occ
            
            # Check clue 4: lawyer not in house 5
            lawyer_pos = occupations_list.index('lawyer') if 'lawyer' in occupations_list else -1
            if lawyer_pos == 4:
                continue
            
            # Check clue 5: nurse directly left of artist (Arnold)
            arnold_house = name_perm.index('Arnold')
            nurse_house = arnold_house - 1
            if nurse_house < 0 or occupations_list[nurse_house] != 'nurse':
                continue
            
            # Check clue 8: teacher left of nurse
            teacher_pos = occupations_list.index('teacher')
            if teacher_pos >= nurse_house:
                continue
            
            # Check clue 12: one house between Peter and lawyer
            peter_pos = name_perm.index('Peter')
            if abs(peter_pos - lawyer_pos) != 2:
                continue
            
            # Check car models
            for car_perm in itertools.permutations(cars):
                # Clue 1: Ford F-150 in house 5
                if car_perm[4] != 'ford f150':
                    continue
                # Clue 2: Chevrolet not in house 2
                if car_perm[1] == 'chevrolet silverado':
                    continue
                # Clue 11: Toyota Camry is nurse
                if car_perm[nurse_house] != 'toyota camry':
                    continue
                
                # Clue 3: Honda Civic next to Peter
                honda_pos = car_perm.index('honda civic')
                if abs(peter_pos - honda_pos) != 1:
                    continue
                
                # Clue 13: one house between Tesla and Bob
                bob_pos = name_perm.index('Bob')
                tesla_pos = car_perm.index('tesla model 3')
                if abs(bob_pos - tesla_pos) != 2:
                    continue
                
                # Build solution
                solution_rows = []
                for i in range(6):
                    house_num = str(i + 1)
                    name = name_perm[i]
                    occ = occupations_list[i]
                    car = car_perm[i]
                    solution_rows.append([house_num, name, occ, car])
                
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Occupation", "CarModel"],
                        "rows": solution_rows
                    }
                }
                
                print(json.dumps(solution))
                return

solve_puzzle()