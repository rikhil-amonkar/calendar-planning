import json

def main():
    attributes = ['name', 'hobby', 'sport', 'house_style', 'child', 'height']
    domains = {
        'name': ['Bob', 'Arnold', 'Alice', 'Peter', 'Eric'],
        'hobby': ['cooking', 'gardening', 'painting', 'photography', 'knitting'],
        'sport': ['swimming', 'tennis', 'soccer', 'baseball', 'basketball'],
        'house_style': ['ranch', 'craftsman', 'victorian', 'modern', 'colonial'],
        'child': ['Timothy', 'Samantha', 'Bella', 'Meredith', 'Fred'],
        'height': ['average', 'very tall', 'very short', 'short', 'tall']
    }
    
    state = {attr: [None] * 5 for attr in attributes}
    
    state['name'][1] = 'Alice'
    state['hobby'][1] = 'gardening'
    state['height'][1] = 'tall'
    state['name'][3] = 'Peter'
    state['height'][3] = 'very tall'
    state['sport'][3] = 'baseball'
    state['house_style'][4] = 'victorian'
    state['child'][4] = 'Fred'
    
    available = {}
    for attr in attributes:
        available[attr] = set(domains[attr])
        for i in range(5):
            if state[attr][i] is not None:
                if state[attr][i] in available[attr]:
                    available[attr].remove(state[attr][i])
    
    unassigned = []
    for house in range(5):
        for attr in attributes:
            if state[attr][house] is None:
                unassigned.append((house, attr))
                
    def clue1(state):
        for i in range(5):
            if state['height'][i] == 'average' and state['child'][i] is not None:
                if state['child'][i] != 'Meredith':
                    return False
            if state['child'][i] == 'Meredith' and state['height'][i] is not None:
                if state['height'][i] != 'average':
                    return False
        avg_house = None
        meredith_house = None
        for i in range(5):
            if state['height'][i] == 'average':
                avg_house = i
            if state['child'][i] == 'Meredith':
                meredith_house = i
        if avg_house is not None and meredith_house is not None and avg_house != meredith_house:
            return False
        return True

    def clue2(state):
        if state['height'][1] is not None and state['height'][1] != 'tall':
            return False
        return True

    def clue3(state):
        peter_index = None
        for i in range(5):
            if state['name'][i] == 'Peter':
                peter_index = i
                break
        if peter_index is not None:
            if peter_index == 4:
                return False
            if state['house_style'][peter_index+1] is not None:
                if state['house_style'][peter_index+1] != 'victorian':
                    return False
        victorian_index = None
        for i in range(5):
            if state['house_style'][i] == 'victorian':
                victorian_index = i
                break
        if victorian_index is not None:
            if victorian_index == 0:
                return False
            if state['name'][victorian_index-1] is not None:
                if state['name'][victorian_index-1] != 'Peter':
                    return False
        return True

    def clue4(state):
        for i in range(5):
            if state['name'][i] == 'Alice' and state['height'][i] is not None:
                if state['height'][i] != 'tall':
                    return False
            if state['height'][i] == 'tall' and state['name'][i] is not None:
                if state['name'][i] != 'Alice':
                    return False
        return True

    def clue5(state):
        for i in range(5):
            if state['sport'][i] == 'baseball' and state['height'][i] is not None:
                if state['height'][i] != 'very tall':
                    return False
            if state['height'][i] == 'very tall' and state['sport'][i] is not None:
                if state['sport'][i] != 'baseball':
                    return False
        return True

    def clue6(state):
        meri_house = None
        tim_house = None
        for i in range(5):
            if state['child'][i] == 'Meredith':
                meri_house = i
            if state['child'][i] == 'Timothy':
                tim_house = i
        if meri_house is not None and tim_house is not None:
            if abs(meri_house - tim_house) != 1:
                return False
        return True

    def clue7(state):
        for i in range(5):
            if state['name'][i] == 'Bob' and state['hobby'][i] is not None:
                if state['hobby'][i] != 'painting':
                    return False
            if state['hobby'][i] == 'painting' and state['name'][i] is not None:
                if state['name'][i] != 'Bob':
                    return False
        return True

    def clue8(state):
        if state['hobby'][1] is not None and state['hobby'][1] != 'gardening':
            return False
        return True

    def clue9(state):
        eric_house = None
        very_short_house = None
        for i in range(5):
            if state['name'][i] == 'Eric':
                eric_house = i
            if state['height'][i] == 'very short':
                very_short_house = i
        if eric_house is not None and very_short_house is not None:
            if very_short_house <= eric_house:
                return False
        return True

    def clue10(state):
        for i in range(5):
            if state['sport'][i] == 'tennis' and state['child'][i] is not None:
                if state['child'][i] != 'Samantha':
                    return False
            if state['child'][i] == 'Samantha' and state['sport'][i] is not None:
                if state['sport'][i] != 'tennis':
                    return False
        return True

    def clue11(state):
        if state['sport'][0] is not None and state['sport'][0] == 'soccer':
            return False
        return True

    def clue12(state):
        for i in range(5):
            if state['child'][i] == 'Samantha' and state['house_style'][i] is not None:
                if state['house_style'][i] != 'modern':
                    return False
            if state['house_style'][i] == 'modern' and state['child'][i] is not None:
                if state['child'][i] != 'Samantha':
                    return False
        return True

    def clue13(state):
        for i in range(5):
            if state['house_style'][i] == 'craftsman' and state['height'][i] is not None:
                if state['height'][i] != 'average':
                    return False
            if state['height'][i] == 'average' and state['house_style'][i] is not None:
                if state['house_style'][i] != 'craftsman':
                    return False
        return True

    def clue14(state):
        for i in range(5):
            if state['child'][i] == 'Fred' and state['house_style'][i] is not None:
                if state['house_style'][i] != 'victorian':
                    return False
            if state['house_style'][i] == 'victorian' and state['child'][i] is not None:
                if state['child'][i] != 'Fred':
                    return False
        return True

    def clue15(state):
        for i in range(5):
            if state['height'][i] == 'short' and state['sport'][i] is not None:
                if state['sport'][i] != 'basketball':
                    return False
            if state['sport'][i] == 'basketball' and state['height'][i] is not None:
                if state['height'][i] != 'short':
                    return False
        return True

    def clue16(state):
        for i in range(5):
            if state['name'][i] == 'Peter' and state['height'][i] is not None:
                if state['height'][i] != 'very tall':
                    return False
            if state['height'][i] == 'very tall' and state['name'][i] is not None:
                if state['name'][i] != 'Peter':
                    return False
        return True

    def clue17(state):
        ranch_house = None
        cooking_house = None
        for i in range(5):
            if state['house_style'][i] == 'ranch':
                ranch_house = i
            if state['hobby'][i] == 'cooking':
                cooking_house = i
        if ranch_house is not None and cooking_house is not None:
            if ranch_house >= cooking_house:
                return False
        return True

    def clue18(state):
        gardening_house = None
        knitting_house = None
        for i in range(5):
            if state['hobby'][i] == 'gardening':
                gardening_house = i
            if state['hobby'][i] == 'knitting':
                knitting_house = i
        if gardening_house is not None and knitting_house is not None:
            if abs(gardening_house - knitting_house) != 1:
                return False
        return True

    def clue19(state):
        for i in range(5):
            if state['house_style'][i] == 'modern' and state['hobby'][i] is not None:
                if state['hobby'][i] != 'cooking':
                    return False
            if state['hobby'][i] == 'cooking' and state['house_style'][i] is not None:
                if state['house_style'][i] != 'modern':
                    return False
        return True

    def clue20(state):
        if state['house_style'][4] is not None and state['house_style'][4] != 'victorian':
            return False
        return True

    def check_all_constraints(state):
        clues = [clue1, clue2, clue3, clue4, clue5, clue6, clue7, clue8, clue9, clue10,
                 clue11, clue12, clue13, clue14, clue15, clue16, clue17, clue18, clue19, clue20]
        for clue_func in clues:
            if not clue_func(state):
                return False
        return True

    def backtrack(state, available, unassigned):
        if len(unassigned) == 0:
            if check_all_constraints(state):
                return state
            else:
                return None
                
        min_domain_size = float('inf')
        best_var = None
        for (house, attr) in unassigned:
            domain_size = len(available[attr])
            if domain_size < min_domain_size:
                min_domain_size = domain_size
                best_var = (house, attr)
                
        if best_var is None:
            return None
            
        house, attr = best_var
        old_available = available[attr].copy()
        for value in list(old_available):
            state[attr][house] = value
            available[attr].remove(value)
            unassigned.remove(best_var)
            
            if check_all_constraints(state):
                result = backtrack(state, available, unassigned)
                if result is not None:
                    return result
                    
            state[attr][house] = None
            available[attr].add(value)
            unassigned.append(best_var)
            
        return None

    solution_state = backtrack(state, available, unassigned)
    if solution_state is None:
        print('No solution found')
        exit(1)
        
    header = ["House", "Name", "Hobby", "Sport", "House Style", "Child", "Height"]
    rows = []
    for i in range(5):
        row = [str(i+1)]
        for attr in attributes:
            row.append(solution_state[attr][i])
        rows.append(row)
        
    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()