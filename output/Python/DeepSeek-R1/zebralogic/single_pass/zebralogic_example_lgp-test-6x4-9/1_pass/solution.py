import json

def main():
    names = ['Carol', 'Bob', 'Alice', 'Arnold', 'Eric', 'Peter']
    phones = ['samsung galaxy s21', 'google pixel 6', 'iphone 13', 'huawei p50', 'oneplus 9', 'xiaomi mi 11']
    nationalities = ['swede', 'chinese', 'norwegian', 'dane', 'german', 'brit']
    colors = ['blue', 'red', 'yellow', 'green', 'white', 'purple']
    
    state = {
        'name': [None] * 6,
        'phone': [None] * 6,
        'nationality': [None] * 6,
        'color': [None] * 6
    }
    
    # Preassign fixed values from clues
    state['name'][4] = 'Bob'
    state['name'][5] = 'Peter'
    state['phone'][4] = 'samsung galaxy s21'
    state['phone'][5] = 'iphone 13'
    state['nationality'][3] = 'dane'
    state['nationality'][5] = 'brit'
    state['color'][3] = 'yellow'
    state['color'][5] = 'blue'
    
    available = {
        'name': set(names) - {'Bob', 'Peter'},
        'phone': set(phones) - {'samsung galaxy s21', 'iphone 13'},
        'nationality': set(nationalities) - {'dane', 'brit'},
        'color': set(colors) - {'yellow', 'blue'}
    }
    
    variables = []
    for house in [0, 1, 2]:
        for attr in ['name', 'phone', 'nationality', 'color']:
            variables.append((house, attr))
    for house in [3]:
        for attr in ['name', 'phone']:
            variables.append((house, attr))
    for house in [4]:
        for attr in ['nationality', 'color']:
            variables.append((house, attr))
    
    def satisfies_all_constraints(state):
        if state['name'][2] is not None:
            if state['name'][2] == 'Carol':
                return False
        
        dane_index = None
        brit_index = None
        for i in range(6):
            if state['nationality'][i] == 'dane':
                dane_index = i
            if state['nationality'][i] == 'brit':
                brit_index = i
        if dane_index is not None and brit_index is not None:
            if abs(dane_index - brit_index) != 2:
                return False
        
        for i in range(6):
            if state['name'][i] is not None and state['color'][i] is not None:
                if state['name'][i] == 'Carol' and state['color'][i] != 'green':
                    return False
                if state['color'][i] == 'green' and state['name'][i] != 'Carol':
                    return False
        
        arnold_index = None
        alice_index = None
        for i in range(6):
            if state['name'][i] == 'Arnold':
                arnold_index = i
            if state['name'][i] == 'Alice':
                alice_index = i
        if arnold_index is not None and alice_index is not None:
            if alice_index != arnold_index + 1:
                return False
        
        for i in range(6):
            if state['name'][i] is not None and state['nationality'][i] is not None:
                if state['name'][i] == 'Alice' and state['nationality'][i] != 'german':
                    return False
                if state['nationality'][i] == 'german' and state['name'][i] != 'Alice':
                    return False
        
        for i in range(6):
            if state['phone'][i] is not None and state['color'][i] is not None:
                if state['phone'][i] == 'oneplus 9' and state['color'][i] != 'purple':
                    return False
                if state['color'][i] == 'purple' and state['phone'][i] != 'oneplus 9':
                    return False
        
        if state['phone'][2] is not None:
            if state['phone'][2] == 'huawei p50':
                return False
        
        if state['phone'][4] != 'samsung galaxy s21':
            return False
        
        red_index = None
        white_index = None
        for i in range(6):
            if state['color'][i] == 'red':
                red_index = i
            if state['color'][i] == 'white':
                white_index = i
        if red_index is not None and white_index is not None:
            if white_index <= red_index:
                return False
        
        if state['name'][4] != 'Bob' or state['phone'][4] != 'samsung galaxy s21':
            return False
        
        for i in range(6):
            if state['nationality'][i] is not None and state['color'][i] is not None:
                if state['nationality'][i] == 'dane' and state['color'][i] != 'yellow':
                    return False
                if state['color'][i] == 'yellow' and state['nationality'][i] != 'dane':
                    return False
        
        if state['name'][5] != 'Peter':
            return False
        if state['phone'][4] != 'samsung galaxy s21':
            return False
        
        if state['color'][5] != 'blue':
            return False
        
        if state['nationality'][5] != 'brit':
            return False
        
        if state['phone'][4] != 'samsung galaxy s21' or state['phone'][5] != 'iphone 13':
            return False
        
        for i in range(6):
            if state['nationality'][i] is not None and state['color'][i] is not None:
                if state['nationality'][i] == 'norwegian' and state['color'][i] != 'purple':
                    return False
                if state['color'][i] == 'purple' and state['nationality'][i] != 'norwegian':
                    return False
        
        for i in range(6):
            if state['phone'][i] is not None and state['nationality'][i] is not None:
                if state['phone'][i] == 'xiaomi mi 11' and state['nationality'][i] != 'chinese':
                    return False
                if state['nationality'][i] == 'chinese' and state['phone'][i] != 'xiaomi mi 11':
                    return False
        
        return True
    
    def backtrack(idx):
        if idx == len(variables):
            return state
        
        house, attr = variables[idx]
        for value in list(available[attr]):
            state[attr][house] = value
            available[attr].remove(value)
            
            if satisfies_all_constraints(state):
                result = backtrack(idx + 1)
                if result is not None:
                    return result
            
            state[attr][house] = None
            available[attr].add(value)
        
        return None
    
    solution_state = backtrack(0)
    if solution_state is None:
        print("No solution found")
        return
    
    header = ["House", "Name", "Phone", "Nationality", "Color"]
    rows = []
    for i in range(6):
        house_num = str(i + 1)
        row = [house_num, solution_state['name'][i], solution_state['phone'][i], solution_state['nationality'][i], solution_state['color'][i]]
        rows.append(row)
    
    result = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()