import itertools
import json

def main():
    attributes = {
        'name': ['Peter', 'Arnold', 'Eric'],
        'car': ['toyota camry', 'ford f150', 'tesla model 3'],
        'house_style': ['ranch', 'colonial', 'victorian'],
        'pet': ['cat', 'dog', 'fish'],
        'occupation': ['engineer', 'doctor', 'teacher'],
        'vacation': ['city', 'mountain', 'beach']
    }
    
    solution_found = None
    
    for names in itertools.permutations(attributes['name']):
        for cars in itertools.permutations(attributes['car']):
            if cars[1] != 'toyota camry':
                continue
            for styles in itertools.permutations(attributes['house_style']):
                if styles[2] != 'colonial':
                    continue
                for pets in itertools.permutations(attributes['pet']):
                    if pets[0] != 'fish':
                        continue
                    for occupations in itertools.permutations(attributes['occupation']):
                        if occupations[2] == 'engineer':
                            continue
                        for vacations in itertools.permutations(attributes['vacation']):
                            if vacations[1] != 'beach':
                                continue
                            
                            houses = [
                                {'name': names[0], 'car': cars[0], 'house_style': styles[0], 'pet': pets[0], 'occupation': occupations[0], 'vacation': vacations[0]},
                                {'name': names[1], 'car': cars[1], 'house_style': styles[1], 'pet': pets[1], 'occupation': occupations[1], 'vacation': vacations[1]},
                                {'name': names[2], 'car': cars[2], 'house_style': styles[2], 'pet': pets[2], 'occupation': occupations[2], 'vacation': vacations[2]}
                            ]
                            
                            ranch_index = None
                            peter_index = None
                            for i, house in enumerate(houses):
                                if house['house_style'] == 'ranch':
                                    ranch_index = i
                                if house['name'] == 'Peter':
                                    peter_index = i
                            if ranch_index is None or peter_index is None or ranch_index >= peter_index:
                                continue
                            
                            arnold_has_cat = False
                            for house in houses:
                                if house['name'] == 'Arnold' and house['pet'] == 'cat':
                                    arnold_has_cat = True
                                    break
                            if not arnold_has_cat:
                                continue
                            
                            eric_index = None
                            mountain_index = None
                            for i, house in enumerate(houses):
                                if house['name'] == 'Eric':
                                    eric_index = i
                                if house['vacation'] == 'mountain':
                                    mountain_index = i
                            if eric_index is None or mountain_index is None or eric_index >= mountain_index:
                                continue
                            
                            tesla_index = None
                            teacher_index = None
                            for i, house in enumerate(houses):
                                if house['car'] == 'tesla model 3':
                                    tesla_index = i
                                if house['occupation'] == 'teacher':
                                    teacher_index = i
                            if tesla_index is None or teacher_index is None or tesla_index >= teacher_index:
                                continue
                            
                            dog_engineer_consistent = True
                            for house in houses:
                                if house['pet'] == 'dog' and house['occupation'] != 'engineer':
                                    dog_engineer_consistent = False
                                    break
                                if house['occupation'] == 'engineer' and house['pet'] != 'dog':
                                    dog_engineer_consistent = False
                                    break
                            if not dog_engineer_consistent:
                                continue
                            
                            solution_found = houses
                            break
                        if solution_found:
                            break
                    if solution_found:
                        break
                if solution_found:
                    break
            if solution_found:
                break
        if solution_found:
            break
    
    if solution_found is None:
        print('{"error": "No solution found"}')
        return
    
    header = ["House", "Name", "Car", "HouseStyle", "Pet", "Occupation", "Vacation"]
    rows = []
    for i, house in enumerate(solution_found):
        row = [
            str(i+1),
            house['name'],
            house['car'],
            house['house_style'],
            house['pet'],
            house['occupation'],
            house['vacation']
        ]
        rows.append(row)
    
    result = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()