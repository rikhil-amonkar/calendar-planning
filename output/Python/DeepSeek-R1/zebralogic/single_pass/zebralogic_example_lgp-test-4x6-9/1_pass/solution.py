import json
import itertools

def main():
    attributes = ['Name', 'Flower', 'Height', 'Mother', 'Occupation', 'Sport']
    possible_values = {
        'Name': ['Peter', 'Arnold', 'Eric', 'Alice'],
        'Flower': ['daffodils', 'carnations', 'roses', 'lilies'],
        'Height': ['very short', 'short', 'tall', 'average'],
        'Mother': ['Janelle', 'Kailyn', 'Holly', 'Aniya'],
        'Occupation': ['engineer', 'doctor', 'teacher', 'artist'],
        'Sport': ['swimming', 'basketball', 'tennis', 'soccer']
    }
    
    n_houses = 4
    state = [dict((attr, None) for attr in attributes) for _ in range(n_houses)]
    domains = dict()
    for house in range(n_houses):
        for attr in attributes:
            domains[(house, attr)] = set(possible_values[attr])
    
    def assign(house, attr, value):
        state[house][attr] = value
        domains[(house, attr)] = {value}
        for h in range(n_houses):
            if h != house and value in domains.get((h, attr), set()):
                domains[(h, attr)].remove(value)
    
    def unary_constraints():
        assign(0, 'Occupation', 'teacher')
        assign(2, 'Name', None)  # Clue 9: Arnold not in third house (index 2)
        domains[(2, 'Name')] = domains.get((2, 'Name'), set()) - {'Arnold'}
    
    unary_constraints()
    
    def is_assigned(house, attr):
        return state[house][attr] is not None
    
    def is_fully_assigned():
        for house in range(n_houses):
            for attr in attributes:
                if state[house][attr] is None:
                    return False
        return True
    
    def get_unassigned_vars():
        unassigned = []
        for house in range(n_houses):
            for attr in attributes:
                if state[house][attr] is None:
                    unassigned.append((house, attr))
        return unassigned
    
    def get_mrv_var():
        unassigned = get_unassigned_vars()
        if not unassigned:
            return None
        mrv_var = min(unassigned, key=lambda x: len(domains[x]))
        return mrv_var
    
    def check_value_consistency(house, attr, value):
        temp_state = [dict(h) for h in state]
        temp_state[house][attr] = value
        
        for h in range(n_houses):
            for a in attributes:
                if a == attr and h == house:
                    continue
                if temp_state[h][a] == value:
                    return False
        
        return True
    
    def check_all_constraints():
        for house in range(n_houses):
            for attr in attributes:
                value = state[house][attr]
                if value is None:
                    continue
                for other_house in range(n_houses):
                    if other_house != house:
                        for other_attr in attributes:
                            if state[other_house][other_attr] == value:
                                return False
        
        clues = [
            (1, lambda: any(state[i]['Sport'] == 'swimming' and state[i]['Flower'] == 'roses' for i in range(4)) or
                   not any(state[i]['Sport'] == 'swimming' for i in range(4)) and
                   not any(state[i]['Flower'] == 'roses' for i in range(4)),
            (2, lambda: any(state[i]['Name'] == 'Eric' and state[i]['Flower'] == 'roses' for i in range(4))),
            (3, lambda: any(state[i]['Name'] == 'Arnold' and state[i]['Height'] == 'tall' for i in range(4))),
            (4, lambda: any(state[i]['Flower'] == 'daffodils' for i in range(4)) and
                   any(state[j]['Occupation'] == 'engineer' for j in range(4)) and
                   (next((i for i in range(4) if state[i]['Flower'] == 'daffodils'), -1) >
                    next((j for j in range(4) if state[j]['Occupation'] == 'engineer'), -2)),
            (5, lambda: any(state[i]['Sport'] == 'soccer' and state[i]['Height'] == 'short' for i in range(4))),
            (6, lambda: state[0]['Occupation'] == 'teacher'),
            (7, lambda: any(state[i]['Mother'] == 'Janelle' and state[i]['Flower'] == 'carnations' for i in range(4))),
            (8, lambda: any(state[i]['Sport'] == 'basketball' and state[i]['Height'] == 'average' for i in range(4))),
            (9, lambda: state[2]['Name'] != 'Arnold'),
            (10, lambda: any(state[i]['Mother'] == 'Holly' for i in range(4)) and
                    any(state[j]['Height'] == 'average' for j in range(4)) and
                    next((i for i in range(4) if state[i]['Mother'] == 'Holly'), -1) >
                    next((j for j in range(4) if state[j]['Height'] == 'average'), -2)),
            (11, lambda: any(state[i]['Name'] == 'Peter' and state[i]['Occupation'] == 'doctor' for i in range(4))),
            (12, lambda: any(state[i]['Mother'] == 'Aniya' and state[i]['Name'] == 'Alice' for i in range(4))),
            (13, lambda: any(state[i]['Name'] == 'Arnold' and state[i]['Flower'] == 'lilies' for i in range(4)))
        ]
        
        for clue_num, constraint in clues:
            if not constraint():
                return False
        return True
    
    def backtrack():
        if is_fully_assigned():
            if check_all_constraints():
                return True
            return False
        
        var = get_mrv_var()
        if var is None:
            return check_all_constraints()
        
        house, attr = var
        domain_copy = set(domains[var])
        for value in domain_copy:
            if not check_value_consistency(house, attr, value):
                continue
            old_domains = {key: set(val) for key, val in domains.items()}
            assign(house, attr, value)
            if backtrack():
                return True
            for key in domains:
                domains[key] = set(old_domains[key])
            state[house][attr] = None
        return False
    
    backtrack()
    
    solution = {
        "solution": {
            "header": ["House", "Name", "Flower", "Height", "Mother", "Occupation", "Sport"],
            "rows": []
        }
    }
    
    for i in range(n_houses):
        row = [str(i+1)]
        for attr in attributes:
            row.append(state[i][attr])
        solution["solution"]["rows"].append(row)
    
    print(json.dumps(solution, indent=2))

if __name__ == '__main__':
    main()