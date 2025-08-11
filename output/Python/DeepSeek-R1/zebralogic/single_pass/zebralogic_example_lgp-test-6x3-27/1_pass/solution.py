import itertools
import json

def main():
    names_list = ['Alice', 'Arnold', 'Eric', 'Peter', 'Bob', 'Carol']
    occupations_list = ['engineer', 'artist', 'doctor', 'teacher', 'nurse', 'lawyer']
    cars_list = ['chevrolet silverado', 'ford f150', 'honda civic', 'toyota camry', 'bmw 3 series', 'tesla model 3']
    
    solution_found = False
    solution_data = None
    
    for names in itertools.permutations(names_list):
        if names[5] == 'Carol':
            continue
        try:
            eric_index = names.index('Eric')
            carol_index = names.index('Carol')
            if carol_index <= eric_index:
                continue
        except:
            continue
        
        for occupations in itertools.permutations(occupations_list):
            if occupations[4] == 'lawyer':
                continue
                
            eric_doctor_ok = True
            for i in range(6):
                if names[i] == 'Eric':
                    if occupations[i] != 'doctor':
                        eric_doctor_ok = False
                        break
            if not eric_doctor_ok:
                continue
                
            bob_engineer_ok = True
            for i in range(6):
                if names[i] == 'Bob':
                    if occupations[i] != 'engineer':
                        bob_engineer_ok = False
                        break
            if not bob_engineer_ok:
                continue
                
            artist_arnold_ok = True
            for i in range(6):
                if occupations[i] == 'artist':
                    if names[i] != 'Arnold':
                        artist_arnold_ok = False
                        break
            if not artist_arnold_ok:
                continue
                
            nurse_artist_adjacent = False
            for i in range(5):
                if occupations[i] == 'nurse' and occupations[i+1] == 'artist':
                    nurse_artist_adjacent = True
                    break
            if not nurse_artist_adjacent:
                continue
                
            try:
                teacher_index = occupations.index('teacher')
                nurse_index = occupations.index('nurse')
                if teacher_index >= nurse_index:
                    continue
            except:
                continue
                
            for cars in itertools.permutations(cars_list):
                if cars[4] != 'ford f150':
                    continue
                if cars[1] == 'chevrolet silverado':
                    continue
                    
                nurse_car_ok = True
                for i in range(6):
                    if occupations[i] == 'nurse':
                        if cars[i] != 'toyota camry':
                            nurse_car_ok = False
                            break
                if not nurse_car_ok:
                    continue
                    
                try:
                    honda_index = cars.index('honda civic')
                    peter_index = names.index('Peter')
                    if abs(honda_index - peter_index) != 1:
                        continue
                except:
                    continue
                    
                try:
                    peter_index = names.index('Peter')
                    lawyer_index = occupations.index('lawyer')
                    if abs(peter_index - lawyer_index) != 2:
                        continue
                except:
                    continue
                    
                try:
                    tesla_index = cars.index('tesla model 3')
                    bob_index = names.index('Bob')
                    if abs(tesla_index - bob_index) != 2:
                        continue
                except:
                    continue
                
                solution_found = True
                solution_data = (names, occupations, cars)
                break
            if solution_found:
                break
        if solution_found:
            break
            
    if not solution_found:
        print('{"solution": {}}')
        return
        
    names, occupations, cars = solution_data
    result = {
        "solution": {
            "header": ["House", "Name", "Occupation", "Car"],
            "rows": []
        }
    }
    
    for i in range(6):
        house_number = str(i+1)
        row = [house_number, names[i], occupations[i], cars[i]]
        result["solution"]["rows"].append(row)
        
    json_output = json.dumps(result, indent=2)
    print(json_output)

if __name__ == "__main__":
    main()