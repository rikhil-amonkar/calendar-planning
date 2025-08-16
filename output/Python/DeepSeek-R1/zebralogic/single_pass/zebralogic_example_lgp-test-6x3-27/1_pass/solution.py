import json

def main():
    names = ['Alice', 'Arnold', 'Eric', 'Peter', 'Bob', 'Carol']
    occupations = ['engineer', 'artist', 'doctor', 'teacher', 'nurse', 'lawyer']
    car_models = ['chevrolet silverado', 'ford f150', 'honda civic', 'toyota camry', 'bmw 3 series', 'tesla model 3']
    
    houses = [{'name': None, 'occupation': None, 'car_model': None} for _ in range(6)]
    available_names = set(names)
    available_occupations = set(occupations)
    available_car_models = set(car_models)
    
    houses[4]['car_model'] = 'ford f150'
    available_car_models.remove('ford f150')
    
    def c1(houses):
        if houses[4]['car_model'] is None:
            return True
        return houses[4]['car_model'] == 'ford f150'
    
    def c2(houses):
        if houses[1]['car_model'] is None:
            return True
        return houses[1]['car_model'] != 'chevrolet silverado'
    
    def c3(houses):
        honda_index = None
        peter_index = None
        for idx, h in enumerate(houses):
            if h['car_model'] == 'honda civic':
                honda_index = idx
            if h['name'] == 'Peter':
                peter_index = idx
        if honda_index is None or peter_index is None:
            return True
        return abs(honda_index - peter_index) == 1
    
    def c4(houses):
        if houses[4]['occupation'] is None:
            return True
        return houses[4]['occupation'] != 'lawyer'
    
    def c5(houses):
        nurse_index = None
        artist_index = None
        for idx, h in enumerate(houses):
            if h['occupation'] == 'nurse':
                nurse_index = idx
            if h['occupation'] == 'artist':
                artist_index = idx
        if nurse_index is None or artist_index is None:
            return True
        return artist_index == nurse_index + 1
    
    def c6(houses):
        eric_index = None
        carol_index = None
        for idx, h in enumerate(houses):
            if h['name'] == 'Eric':
                eric_index = idx
            if h['name'] == 'Carol':
                carol_index = idx
        if eric_index is None or carol_index is None:
            return True
        return carol_index > eric_index
    
    def c7(houses):
        for h in houses:
            if h['name'] == 'Eric' and h['occupation'] != 'doctor':
                return False
            if h['occupation'] == 'doctor' and h['name'] != 'Eric':
                return False
        return True
    
    def c8(houses):
        teacher_index = None
        nurse_index = None
        for idx, h in enumerate(houses):
            if h['occupation'] == 'teacher':
                teacher_index = idx
            if h['occupation'] == 'nurse':
                nurse_index = idx
        if teacher_index is None or nurse_index is None:
            return True
        return teacher_index < nurse_index
    
    def c9(houses):
        if houses[5]['name'] is None:
            return True
        return houses[5]['name'] != 'Carol'
    
    def c10(houses):
        for h in houses:
            if h['name'] == 'Bob' and h['occupation'] != 'engineer':
                return False
            if h['occupation'] == 'engineer' and h['name'] != 'Bob':
                return False
        return True
    
    def c11(houses):
        for h in houses:
            if h['car_model'] == 'toyota camry' and h['occupation'] != 'nurse':
                return False
            if h['occupation'] == 'nurse' and h['car_model'] != 'toyota camry':
                return False
        return True
    
    def c12(houses):
        peter_index = None
        lawyer_index = None
        for idx, h in enumerate(houses):
            if h['name'] == 'Peter':
                peter_index = idx
            if h['occupation'] == 'lawyer':
                lawyer_index = idx
        if peter_index is None or lawyer_index is None:
            return True
        return abs(peter_index - lawyer_index) == 2
    
    def c13(houses):
        tesla_index = None
        bob_index = None
        for idx, h in enumerate(houses):
            if h['car_model'] == 'tesla model 3':
                tesla_index = idx
            if h['name'] == 'Bob':
                bob_index = idx
        if tesla_index is None or bob_index is None:
            return True
        return abs(tesla_index - bob_index) == 2
    
    def c14(houses):
        for h in houses:
            if h['name'] == 'Arnold' and h['occupation'] != 'artist':
                return False
            if h['occupation'] == 'artist' and h['name'] != 'Arnold':
                return False
        return True
    
    constraints = [c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14]
    
    def backtrack(i):
        if i == 4:
            for name in list(available_names):
                houses[4]['name'] = name
                available_names.remove(name)
                
                for occupation in list(available_occupations):
                    if occupation == 'lawyer':
                        continue
                    if name == 'Eric' and occupation != 'doctor':
                        continue
                    if name == 'Bob' and occupation != 'engineer':
                        continue
                    if name == 'Arnold' and occupation != 'artist':
                        continue
                    if occupation == 'nurse':
                        continue
                    
                    houses[4]['occupation'] = occupation
                    available_occupations.remove(occupation)
                    
                    if all(constraint(houses) for constraint in constraints):
                        if backtrack(5):
                            return True
                    
                    available_occupations.add(occupation)
                    houses[4]['occupation'] = None
                
                available_names.add(name)
                houses[4]['name'] = None
            return False
        
        elif i == 5:
            if len(available_names) == 1 and len(available_occupations) == 1 and len(available_car_models) == 1:
                name = available_names.pop()
                occupation = available_occupations.pop()
                car_model = available_car_models.pop()
                houses[5]['name'] = name
                houses[5]['occupation'] = occupation
                houses[5]['car_model'] = car_model
                
                if (name == 'Eric' and occupation != 'doctor') or \
                   (name == 'Bob' and occupation != 'engineer') or \
                   (name == 'Arnold' and occupation != 'artist') or \
                   (occupation == 'nurse' and car_model != 'toyota camry') or \
                   (car_model == 'toyota camry' and occupation != 'nurse'):
                    houses[5]['name'] = None
                    houses[5]['occupation'] = None
                    houses[5]['car_model'] = None
                    available_names.add(name)
                    available_occupations.add(occupation)
                    available_car_models.add(car_model)
                    return False
                
                if all(constraint(houses) for constraint in constraints):
                    return True
                else:
                    houses[5]['name'] = None
                    houses[5]['occupation'] = None
                    houses[5]['car_model'] = None
                    available_names.add(name)
                    available_occupations.add(occupation)
                    available_car_models.add(car_model)
                    return False
            else:
                for name in list(available_names):
                    houses[5]['name'] = name
                    available_names.remove(name)
                    for occupation in list(available_occupations):
                        houses[5]['occupation'] = occupation
                        available_occupations.remove(occupation)
                        for car_model in list(available_car_models):
                            if (name == 'Eric' and occupation != 'doctor') or \
                               (name == 'Bob' and occupation != 'engineer') or \
                               (name == 'Arnold' and occupation != 'artist') or \
                               (occupation == 'nurse' and car_model != 'toyota camry') or \
                               (car_model == 'toyota camry' and occupation != 'nurse'):
                                continue
                            
                            houses[5]['car_model'] = car_model
                            available_car_models.remove(car_model)
                            
                            if all(constraint(houses) for constraint in constraints):
                                return True
                            
                            available_car_models.add(car_model)
                            houses[5]['car_model'] = None
                        available_occupations.add(occupation)
                        houses[5]['occupation'] = None
                    available_names.add(name)
                    houses[5]['name'] = None
                return False
        else:
            for name in list(available_names):
                houses[i]['name'] = name
                available_names.remove(name)
                for occupation in list(available_occupations):
                    houses[i]['occupation'] = occupation
                    available_occupations.remove(occupation)
                    for car_model in list(available_car_models):
                        if (name == 'Eric' and occupation != 'doctor') or \
                           (name == 'Bob' and occupation != 'engineer') or \
                           (name == 'Arnold' and occupation != 'artist') or \
                           (occupation == 'nurse' and car_model != 'toyota camry') or \
                           (car_model == 'toyota camry' and occupation != 'nurse'):
                            continue
                        
                        houses[i]['car_model'] = car_model
                        available_car_models.remove(car_model)
                        
                        if all(constraint(houses) for constraint in constraints):
                            if backtrack(i+1):
                                return True
                        
                        available_car_models.add(car_model)
                        houses[i]['car_model'] = None
                    available_occupations.add(occupation)
                    houses[i]['occupation'] = None
                available_names.add(name)
                houses[i]['name'] = None
            return False
    
    found = backtrack(0)
    if not found:
        print(json.dumps({"error": "No solution found"}))
        return
    
    solution = {
        "solution": {
            "header": ["House", "Name", "Occupation", "CarModel"],
            "rows": []
        }
    }
    for i in range(6):
        row = [str(i+1), houses[i]['name'], houses[i]['occupation'], houses[i]['car_model']]
        solution["solution"]["rows"].append(row)
    
    print(json.dumps(solution))

if __name__ == "__main__":
    main()