import itertools
import json

def main():
    # Predefined nationality assignments for the four cases
    nat_assignments = [
        ['norwegian', 'brit', 'swede', 'german', 'dane'],
        ['norwegian', 'german', 'swede', 'brit', 'dane'],
        ['brit', 'norwegian', 'swede', 'german', 'dane'],
        ['german', 'norwegian', 'swede', 'brit', 'dane']
    ]
    
    all_names = ['Alice', 'Bob', 'Arnold', 'Eric', 'Peter']
    all_vacations = ['cruise', 'city', 'camping', 'beach', 'mountain']
    all_children = ['Bella', 'Samantha', 'Fred', 'Meredith', 'Timothy']
    
    found_solution = False
    solution = None
    
    for nats in nat_assignments:
        names = [None] * 5
        names[4] = 'Arnold'
        norwegian_house = None
        brit_house = None
        for i in range(5):
            if nats[i] == 'norwegian':
                norwegian_house = i
                names[i] = 'Peter'
            elif nats[i] == 'brit':
                brit_house = i
                names[i] = 'Alice'
        
        free_name_houses = [i for i in range(5) if names[i] is None]
        used_names = {n for n in names if n is not None}
        free_names = [n for n in all_names if n not in used_names]
        
        for name_perm in itertools.permutations(free_names):
            for idx, name_val in zip(free_name_houses, name_perm):
                names[idx] = name_val
            
            bob_house = None
            for i in range(5):
                if names[i] == 'Bob':
                    bob_house = i
                    break
            if bob_house is None:
                continue
            
            vacations = [None] * 5
            vacations[0] = 'cruise'
            vacations[bob_house] = 'camping'
            
            free_vac_houses = [i for i in range(5) if vacations[i] is None]
            used_vacs = {'cruise', 'camping'}
            free_vacs = [v for v in all_vacations if v not in used_vacs]
            
            for vac_perm in itertools.permutations(free_vacs):
                for idx, vac_val in zip(free_vac_houses, vac_perm):
                    vacations[idx] = vac_val
                
                children = [None] * 5
                children[2] = 'Bella'
                children[3] = 'Meredith'
                
                free_child_houses = [i for i in range(5) if children[i] is None]
                used_children = {'Bella', 'Meredith'}
                free_children = [c for c in all_children if c not in used_children]
                
                for child_perm in itertools.permutations(free_children):
                    for idx, child_val in zip(free_child_houses, child_perm):
                        children[idx] = child_val
                    
                    beach_house = None
                    for i in range(5):
                        if vacations[i] == 'beach':
                            beach_house = i
                            break
                    valid3 = False
                    if beach_house is not None and beach_house < 4:
                        if children[beach_house+1] == 'Samantha':
                            valid3 = True
                    
                    fred_house = None
                    for i in range(5):
                        if children[i] == 'Fred':
                            fred_house = i
                            break
                    city_house = None
                    for i in range(5):
                        if vacations[i] == 'city':
                            city_house = i
                            break
                    valid10 = False
                    if fred_house is not None and city_house is not None:
                        if abs(fred_house - city_house) == 2:
                            valid10 = True
                    
                    if valid3 and valid10:
                        found_solution = True
                        solution = []
                        for i in range(5):
                            solution.append({
                                'House': str(i+1),
                                'Name': names[i],
                                'Vacation': vacations[i],
                                'Child': children[i],
                                'Nationality': nats[i]
                            })
                        break
                if found_solution:
                    break
            if found_solution:
                break
        if found_solution:
            break
    
    if found_solution:
        rows = []
        for house in solution:
            rows.append([house['House'], house['Name'], house['Vacation'], house['Child'], house['Nationality']])
        solution_json = {
            "solution": {
                "header": ["House", "Name", "Vacation", "Child", "Nationality"],
                "rows": rows
            }
        }
    else:
        solution_json = {
            "solution": {
                "header": ["House", "Name", "Vacation", "Child", "Nationality"],
                "rows": []
            }
        }
    
    print(json.dumps(solution_json))

if __name__ == "__main__":
    main()