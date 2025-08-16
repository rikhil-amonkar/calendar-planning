import json

def c1(state):
    if state['names'][1] is None:
        return None
    return state['names'][1] != 'Bob'

def c2(state):
    cat_pos = None
    rabbit_pos = None
    for i in range(6):
        if state['pets'][i] == 'cat':
            cat_pos = i
        if state['pets'][i] == 'rabbit':
            rabbit_pos = i
    if cat_pos is None or rabbit_pos is None:
        return None
    return abs(cat_pos - rabbit_pos) == 3

def c3(state):
    for i in range(5):
        if state['pets'][i] == 'cat':
            if state['mothers'][i+1] is None:
                return None
            if state['mothers'][i+1] != 'Holly':
                return False
            return True
    if any(state['pets'][i]=='cat' for i in [5]):
        return False
    return None

def c4(state):
    for i in range(5):
        if state['pets'][i] == 'hamster':
            if state['pets'][i+1] is None:
                return None
            if state['pets'][i+1] != 'rabbit':
                return False
            return True
    if any(state['pets'][i]=='hamster' for i in [5]):
        return False
    return None

def c5(state):
    for i in range(6):
        if state['pets'][i] == 'rabbit':
            if state['names'][i] is None:
                return None
            return state['names'][i] == 'Eric'
    return None

def c6(state):
    cat_pos = None
    dog_pos = None
    for i in range(6):
        if state['pets'][i] == 'cat':
            cat_pos = i
        if state['pets'][i] == 'dog':
            dog_pos = i
    if cat_pos is None or dog_pos is None:
        return None
    return abs(cat_pos - dog_pos) == 2

def c7(state):
    for i in range(6):
        if state['pets'][i] == 'cat':
            if state['mothers'][i] is None:
                return None
            return state['mothers'][i] == 'Janelle'
    return None

def c8(state):
    alice_pos = None
    carol_pos = None
    for i in range(6):
        if state['names'][i] == 'Alice':
            alice_pos = i
        if state['names'][i] == 'Carol':
            carol_pos = i
    if alice_pos is None or carol_pos is None:
        return None
    return alice_pos + 1 == carol_pos

def c9(state):
    for i in range(6):
        if state['names'][i] == 'Carol':
            if state['mothers'][i] is None:
                return None
            return state['mothers'][i] == 'Aniya'
    return None

def c10(state):
    for i in range(6):
        if state['pets'][i] == 'cat':
            if state['names'][i] is None:
                return None
            return state['names'][i] == 'Arnold'
    return None

def c11(state):
    for i in range(6):
        if state['mothers'][i] == 'Kailyn':
            if state['pets'][i] is None:
                return None
            return state['pets'][i] == 'rabbit'
    return None

def c12(state):
    for i in range(6):
        if state['pets'][i] == 'fish':
            if state['mothers'][i] is None:
                return None
            return state['mothers'][i] == 'Sarah'
    return None

def check_constraints(state):
    constraints = [c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12]
    for constraint in constraints:
        res = constraint(state)
        if res is False:
            return False
    return True

def backtrack_remaining(state, available_names, available_mothers, available_pets, remaining_indices):
    if not remaining_indices:
        if check_constraints(state):
            return state
        else:
            return None

    i = remaining_indices[0]
    for name in list(available_names):
        state['names'][i] = name
        new_avail_names = available_names - {name}
        for mother in list(available_mothers):
            state['mothers'][i] = mother
            new_avail_mothers = available_mothers - {mother}
            for pet in list(available_pets):
                state['pets'][i] = pet
                new_avail_pets = available_pets - {pet}
                
                if check_constraints(state) != False:
                    result = backtrack_remaining(state, new_avail_names, new_avail_mothers, new_avail_pets, remaining_indices[1:])
                    if result is not None:
                        return result
                
                state['pets'][i] = None
            state['mothers'][i] = None
        state['names'][i] = None
    return None

def main():
    names_all = ['Arnold', 'Eric', 'Bob', 'Alice', 'Carol', 'Peter']
    mothers_all = ['Sarah', 'Holly', 'Janelle', 'Aniya', 'Penny', 'Kailyn']
    pets_all = ['hamster', 'dog', 'bird', 'cat', 'fish', 'rabbit']
    
    cases = [(0,3), (1,4), (2,5), (4,1)]
    
    for (cat_index, rabbit_index) in cases:
        state = {
            'names': [None] * 6,
            'mothers': [None] * 6,
            'pets': [None] * 6
        }
        state['names'][cat_index] = 'Arnold'
        state['mothers'][cat_index] = 'Janelle'
        state['pets'][cat_index] = 'cat'
        state['names'][rabbit_index] = 'Eric'
        state['mothers'][rabbit_index] = 'Kailyn'
        state['pets'][rabbit_index] = 'rabbit'
        
        used_names = {'Arnold', 'Eric'}
        used_mothers = {'Janelle', 'Kailyn'}
        used_pets = {'cat', 'rabbit'}
        
        available_names = set(names_all) - used_names
        available_mothers = set(mothers_all) - used_mothers
        available_pets = set(pets_all) - used_pets
        
        remaining_indices = [i for i in range(6) if i != cat_index and i != rabbit_index]
        
        result_state = backtrack_remaining(state, available_names, available_mothers, available_pets, remaining_indices)
        if result_state is not None:
            break
    
    if result_state is None:
        print('{"error": "No solution found"}')
        return
    
    rows = []
    for i in range(6):
        row = [str(i+1), result_state['names'][i], result_state['mothers'][i], result_state['pets'][i]]
        rows.append(row)
    
    solution_dict = {
        "solution": {
            "header": ["House", "Name", "Mother", "Pet"],
            "rows": rows
        }
    }
    print(json.dumps(solution_dict))

if __name__ == '__main__':
    main()