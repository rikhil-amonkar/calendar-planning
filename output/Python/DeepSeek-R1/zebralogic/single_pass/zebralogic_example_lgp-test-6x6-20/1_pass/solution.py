import json

attributes = ['name', 'cigar', 'music', 'drink', 'mother', 'lunch']
all_values = {
    'name': ['Alice', 'Peter', 'Eric', 'Bob', 'Arnold', 'Carol'],
    'cigar': ['pall mall', 'yellow monster', 'dunhill', 'blue master', 'prince', 'blends'],
    'music': ['hip hop', 'jazz', 'country', 'pop', 'classical', 'rock'],
    'drink': ['water', 'milk', 'boba tea', 'tea', 'root beer', 'coffee'],
    'mother': ['Kailyn', 'Penny', 'Janelle', 'Holly', 'Sarah', 'Aniya'],
    'lunch': ['soup', 'pizza', 'spaghetti', 'stir fry', 'stew', 'grilled cheese']
}

def c1(state):
    carol_house = None
    grilled_cheese_house = None
    for i in range(6):
        if state['name'][i] == 'Carol':
            carol_house = i
        if state['lunch'][i] == 'grilled cheese':
            grilled_cheese_house = i
    if carol_house is not None and grilled_cheese_house is not None:
        return carol_house + 1 == grilled_cheese_house
    return True

def c2(state):
    if state['name'][1] is not None:
        return state['name'][1] != 'Eric'
    return True

def c3(state):
    carol_house = None
    holly_house = None
    for i in range(6):
        if state['name'][i] == 'Carol':
            carol_house = i
        if state['mother'][i] == 'Holly':
            holly_house = i
    if carol_house is not None and holly_house is not None:
        return holly_house > carol_house
    return True

def c4(state):
    grilled_cheese_house = None
    rock_house = None
    for i in range(6):
        if state['lunch'][i] == 'grilled cheese':
            grilled_cheese_house = i
        if state['music'][i] == 'rock':
            rock_house = i
    if grilled_cheese_house is not None and rock_house is not None:
        return grilled_cheese_house > rock_house
    return True

def c5(state):
    eric_house = None
    carol_house = None
    for i in range(6):
        if state['name'][i] == 'Eric':
            eric_house = i
        if state['name'][i] == 'Carol':
            carol_house = i
    if eric_house is not None and carol_house is not None:
        return eric_house + 1 == carol_house
    return True

def c6(state):
    if state['music'][2] is not None:
        return state['music'][2] != 'pop'
    return True

def c7(state):
    for i in range(6):
        if state['name'][i] == 'Eric':
            if state['music'][i] is not None:
                return state['music'][i] == 'country'
            else:
                return True
    return True

def c8(state):
    if state['music'][5] is not None:
        return state['music'][5] == 'classical'
    return True

def c9(state):
    for i in range(6):
        if state['drink'][i] == 'coffee':
            if state['name'][i] is not None:
                return state['name'][i] == 'Bob'
            else:
                return True
    return True

def c10(state):
    for i in range(6):
        if state['cigar'][i] == 'blends':
            if state['name'][i] is not None:
                return state['name'][i] == 'Peter'
            else:
                return True
    return True

def c11(state):
    if state['lunch'][4] is not None:
        return state['lunch'][4] != 'stew'
    return True

def c12(state):
    root_beer_house = None
    janelle_house = None
    for i in range(6):
        if state['drink'][i] == 'root beer':
            root_beer_house = i
        if state['mother'][i] == 'Janelle':
            janelle_house = i
    if root_beer_house is not None and janelle_house is not None:
        return root_beer_house + 1 == janelle_house
    return True

def c13(state):
    sarah_house = None
    yellow_house = None
    for i in range(6):
        if state['mother'][i] == 'Sarah':
            sarah_house = i
        if state['cigar'][i] == 'yellow monster':
            yellow_house = i
    if sarah_house is not None and yellow_house is not None:
        return abs(sarah_house - yellow_house) == 3
    return True

def c14(state):
    for i in range(6):
        if state['name'][i] == 'Eric':
            if state['drink'][i] is not None:
                return state['drink'][i] == 'tea'
            else:
                return True
    return True

def c15(state):
    pall_house = None
    stir_fry_house = None
    for i in range(6):
        if state['cigar'][i] == 'pall mall':
            pall_house = i
        if state['lunch'][i] == 'stir fry':
            stir_fry_house = i
    if pall_house is not None and stir_fry_house is not None:
        return pall_house > stir_fry_house
    return True

def c16(state):
    for i in range(6):
        if state['lunch'][i] == 'soup':
            if state['name'][i] is not None:
                return state['name'][i] == 'Bob'
            else:
                return True
    return True

def c17(state):
    hiphop_house = None
    kailyn_house = None
    for i in range(6):
        if state['music'][i] == 'hip hop':
            hiphop_house = i
        if state['mother'][i] == 'Kailyn':
            kailyn_house = i
    if hiphop_house is not None and kailyn_house is not None:
        return hiphop_house + 1 == kailyn_house
    return True

def c18(state):
    arnold_house = None
    kailyn_house = None
    for i in range(6):
        if state['name'][i] == 'Arnold':
            arnold_house = i
        if state['mother'][i] == 'Kailyn':
            kailyn_house = i
    if arnold_house is not None and kailyn_house is not None:
        return arnold_house > kailyn_house
    return True

def c19(state):
    water_house = None
    blue_house = None
    for i in range(6):
        if state['drink'][i] == 'water':
            water_house = i
        if state['cigar'][i] == 'blue master':
            blue_house = i
    if water_house is not None and blue_house is not None:
        return blue_house == water_house + 1
    return True

def c20(state):
    spaghetti_house = None
    blends_house = None
    for i in range(6):
        if state['lunch'][i] == 'spaghetti':
            spaghetti_house = i
        if state['cigar'][i] == 'blends':
            blends_house = i
    if spaghetti_house is not None and blends_house is not None:
        return spaghetti_house < blends_house
    return True

def c21(state):
    sarah_house = None
    jazz_house = None
    for i in range(6):
        if state['mother'][i] == 'Sarah':
            sarah_house = i
        if state['music'][i] == 'jazz':
            jazz_house = i
    if sarah_house is not None and jazz_house is not None:
        return sarah_house + 1 == jazz_house
    return True

def c22(state):
    hiphop_house = None
    rootbeer_house = None
    for i in range(6):
        if state['music'][i] == 'hip hop':
            hiphop_house = i
        if state['drink'][i] == 'root beer':
            rootbeer_house = i
    if hiphop_house is not None and rootbeer_house is not None:
        return rootbeer_house == hiphop_house + 1
    return True

def c23(state):
    for i in range(6):
        if state['drink'][i] == 'water':
            if state['lunch'][i] is not None:
                if state['lunch'][i] != 'stew':
                    return False
        if state['lunch'][i] == 'stew':
            if state['drink'][i] is not None:
                if state['drink'][i] != 'water':
                    return False
    water_house = None
    stew_house = None
    for i in range(6):
        if state['drink'][i] == 'water':
            water_house = i
        if state['lunch'][i] == 'stew':
            stew_house = i
    if water_house is not None and stew_house is not None:
        return water_house == stew_house
    return True

def c24(state):
    if state['cigar'][1] is not None:
        return state['cigar'][1] != 'dunhill'
    return True

def c25(state):
    for i in range(6):
        if state['drink'][i] == 'milk':
            if state['mother'][i] is not None:
                return state['mother'][i] == 'Janelle'
            else:
                return True
    return True

def c26(state):
    for i in range(6):
        if state['name'][i] == 'Eric':
            if state['mother'][i] is not None:
                return state['mother'][i] == 'Aniya'
            else:
                return True
    return True

def get_available(state, attr, house):
    assigned_vals = [v for v in state[attr] if v is not None]
    base_available = set(all_values[attr]) - set(assigned_vals)
    if attr == 'name' and house == 1:
        base_available.discard('Eric')
    elif attr == 'cigar' and house == 1:
        base_available.discard('dunhill')
    elif attr == 'music' and house == 2:
        base_available.discard('pop')
    elif attr == 'lunch' and house == 4:
        base_available.discard('stew')
    if attr == 'music' and state['name'][house] == 'Eric' and 'country' in base_available:
        return {'country'}
    return base_available

def check_constraints(state, constraints_list):
    for c in constraints_list:
        if not c(state):
            return False
    return True

def backtrack(state, constraints_list, attributes, all_values):
    unassigned = []
    for attr in attributes:
        for house in range(6):
            if state[attr][house] is None:
                unassigned.append((attr, house))
    if not unassigned:
        return state
    min_available_size = float('inf')
    chosen_var = None
    choices = None
    for (attr, house) in unassigned:
        avail = get_available(state, attr, house)
        size = len(avail)
        if size < min_available_size:
            min_available_size = size
            chosen_var = (attr, house)
            choices = avail
    if chosen_var is None:
        return None
    attr, house = chosen_var
    for candidate in choices:
        state[attr][house] = candidate
        if check_constraints(state, constraints_list):
            result = backtrack(state, constraints_list, attributes, all_values)
            if result is not None:
                return result
        state[attr][house] = None
    return None

def main():
    state = {attr: [None] * 6 for attr in attributes}
    state['music'][5] = 'classical'
    constraints_list = [c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26]
    sol = backtrack(state, constraints_list, attributes, all_values)
    if sol is None:
        print(json.dumps({"solution": {}}))
        return
    header = ["House", "Name", "Cigar", "Music", "Drink", "Mother", "Lunch"]
    rows = []
    for i in range(6):
        row = [
            str(i+1),
            sol['name'][i],
            sol['cigar'][i],
            sol['music'][i],
            sol['drink'][i],
            sol['mother'][i],
            sol['lunch'][i]
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