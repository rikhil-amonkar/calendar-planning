import json

def per_house_constraints(house_index, name, cigar, music, drink, mother, food):
    if house_index == 1:
        if name == 'Eric':
            return False
        if cigar == 'dunhill':
            return False
    if house_index == 2:
        if music == 'pop':
            return False
    if house_index == 4:
        if food == 'stew':
            return False
    if house_index == 5:
        if music != 'classical':
            return False
            
    if name == 'Eric':
        if music != 'country' or drink != 'tea' or mother != 'Aniya':
            return False
    if name == 'Bob':
        if drink != 'coffee' or food != 'soup':
            return False
    if name == 'Peter':
        if cigar != 'blends':
            return False
    if mother == 'Janelle':
        if drink != 'milk':
            return False
    if drink == 'water':
        if food != 'stew':
            return False
    if drink == 'coffee':
        if name != 'Bob':
            return False
    if food == 'soup':
        if name != 'Bob':
            return False
    if cigar == 'blends':
        if name != 'Peter':
            return False
    if music == 'country':
        if name != 'Eric':
            return False
    if drink == 'tea':
        if name != 'Eric':
            return False
    if mother == 'Aniya':
        if name != 'Eric':
            return False
            
    return True

def check_all_constraints(state):
    try:
        carol_index = next(i for i, name in enumerate(state['names']) if name == 'Carol')
        if carol_index >= 5:
            return False
        if state['foods'][carol_index+1] != 'grilled cheese':
            return False
    except StopIteration:
        return False
        
    try:
        carol_index = next(i for i, name in enumerate(state['names']) if name == 'Carol')
        holly_index = next(i for i, mother in enumerate(state['mothers']) if mother == 'Holly')
        if holly_index <= carol_index:
            return False
    except StopIteration:
        return False
        
    try:
        grilled_index = next(i for i, food in enumerate(state['foods']) if food == 'grilled cheese')
        rock_index = next(i for i, music in enumerate(state['music']) if music == 'rock')
        if grilled_index <= rock_index:
            return False
    except StopIteration:
        return False
        
    try:
        eric_index = next(i for i, name in enumerate(state['names']) if name == 'Eric')
        carol_index = next(i for i, name in enumerate(state['names']) if name == 'Carol')
        if eric_index + 1 != carol_index:
            return False
    except StopIteration:
        return False
        
    try:
        rootbeer_index = next(i for i, drink in enumerate(state['drinks']) if drink == 'root beer')
        janelle_index = next(i for i, mother in enumerate(state['mothers']) if mother == 'Janelle')
        if rootbeer_index + 1 != janelle_index:
            return False
    except StopIteration:
        return False
        
    try:
        sarah_index = next(i for i, mother in enumerate(state['mothers']) if mother == 'Sarah')
        yellow_index = next(i for i, cigar in enumerate(state['cigars']) if cigar == 'yellow monster')
        if abs(sarah_index - yellow_index) != 3:
            return False
    except StopIteration:
        return False
        
    try:
        pallmall_index = next(i for i, cigar in enumerate(state['cigars']) if cigar == 'pall mall')
        stirfry_index = next(i for i, food in enumerate(state['foods']) if food == 'stir fry')
        if pallmall_index <= stirfry_index:
            return False
    except StopIteration:
        return False
        
    try:
        hiphop_index = next(i for i, music in enumerate(state['music']) if music == 'hip hop')
        kailyn_index = next(i for i, mother in enumerate(state['mothers']) if mother == 'Kailyn')
        if hiphop_index + 1 != kailyn_index:
            return False
    except StopIteration:
        return False
        
    try:
        kailyn_index = next(i for i, mother in enumerate(state['mothers']) if mother == 'Kailyn')
        arnold_index = next(i for i, name in enumerate(state['names']) if name == 'Arnold')
        if arnold_index <= kailyn_index:
            return False
    except StopIteration:
        return False
        
    try:
        water_index = next(i for i, drink in enumerate(state['drinks']) if drink == 'water')
        blue_index = next(i for i, cigar in enumerate(state['cigars']) if cigar == 'blue master')
        if water_index + 1 != blue_index:
            return False
    except StopIteration:
        return False
        
    try:
        spaghetti_index = next(i for i, food in enumerate(state['foods']) if food == 'spaghetti')
        blends_index = next(i for i, cigar in enumerate(state['cigars']) if cigar == 'blends')
        if spaghetti_index >= blends_index:
            return False
    except StopIteration:
        return False
        
    try:
        sarah_index = next(i for i, mother in enumerate(state['mothers']) if mother == 'Sarah')
        jazz_index = next(i for i, music in enumerate(state['music']) if music == 'jazz')
        if sarah_index + 1 != jazz_index:
            return False
    except StopIteration:
        return False
        
    try:
        hiphop_index = next(i for i, music in enumerate(state['music']) if music == 'hip hop')
        rootbeer_index = next(i for i, drink in enumerate(state['drinks']) if drink == 'root beer')
        if hiphop_index + 1 != rootbeer_index:
            return False
    except StopIteration:
        return False
        
    try:
        milk_index = next(i for i, drink in enumerate(state['drinks']) if drink == 'milk')
        if state['mothers'][milk_index] != 'Janelle':
            return False
    except StopIteration:
        return False
        
    return True

def backtrack(house_index, state, available):
    if house_index == 6:
        if check_all_constraints(state):
            return state
        else:
            return None
            
    for name in list(available['names']):
        for cigar in list(available['cigars']):
            for music in list(available['music']):
                for drink in list(available['drinks']):
                    for mother in list(available['mothers']):
                        for food in list(available['foods']):
                            if not per_house_constraints(house_index, name, cigar, music, drink, mother, food):
                                continue
                            
                            state['names'][house_index] = name
                            state['cigars'][house_index] = cigar
                            state['music'][house_index] = music
                            state['drinks'][house_index] = drink
                            state['mothers'][house_index] = mother
                            state['foods'][house_index] = food
                            
                            available['names'].remove(name)
                            available['cigars'].remove(cigar)
                            available['music'].remove(music)
                            available['drinks'].remove(drink)
                            available['mothers'].remove(mother)
                            available['foods'].remove(food)
                            
                            result = backtrack(house_index+1, state, available)
                            if result is not None:
                                return result
                                
                            available['names'].add(name)
                            available['cigars'].add(cigar)
                            available['music'].add(music)
                            available['drinks'].add(drink)
                            available['mothers'].add(mother)
                            available['foods'].add(food)
                            
    state['names'][house_index] = None
    state['cigars'][house_index] = None
    state['music'][house_index] = None
    state['drinks'][house_index] = None
    state['mothers'][house_index] = None
    state['foods'][house_index] = None
    return None

def solve():
    state = {
        'names': [None] * 6,
        'cigars': [None] * 6,
        'music': [None] * 6,
        'drinks': [None] * 6,
        'mothers': [None] * 6,
        'foods': [None] * 6
    }
    available = {
        'names': set(['Alice', 'Peter', 'Eric', 'Bob', 'Arnold', 'Carol']),
        'cigars': set(['pall mall', 'yellow monster', 'dunhill', 'blue master', 'prince', 'blends']),
        'music': set(['hip hop', 'jazz', 'country', 'pop', 'classical', 'rock']),
        'drinks': set(['water', 'milk', 'boba tea', 'tea', 'root beer', 'coffee']),
        'mothers': set(['Kailyn', 'Penny', 'Janelle', 'Holly', 'Sarah', 'Aniya']),
        'foods': set(['soup', 'pizza', 'spaghetti', 'stir fry', 'stew', 'grilled cheese'])
    }
    result = backtrack(0, state, available)
    return result

def main():
    solution = solve()
    if solution is None:
        print("No solution found")
        return
        
    header = ["House", "Name", "Cigar", "MusicGenre", "Drink", "Mother", "Food"]
    rows = []
    for i in range(6):
        house_number = str(i+1)
        row = [house_number, solution['names'][i], solution['cigars'][i], solution['music'][i], solution['drinks'][i], solution['mothers'][i], solution['foods'][i]]
        rows.append(row)
        
    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(output, indent=2))

if __name__ == '__main__':
    main()