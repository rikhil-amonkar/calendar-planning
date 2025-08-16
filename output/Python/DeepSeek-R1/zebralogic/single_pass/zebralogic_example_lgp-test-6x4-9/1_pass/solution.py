import json

def satisfies(assignment):
    if assignment[2]['name'] == 'Carol':
        return False

    for i in range(6):
        if assignment[i]['name'] == 'Carol':
            if assignment[i]['color'] != 'green':
                return False

    found = False
    for i in range(5):
        if assignment[i]['name'] == 'Arnold' and assignment[i+1]['name'] == 'Alice':
            found = True
            break
    if not found:
        return False

    for i in range(6):
        if assignment[i]['name'] == 'Alice':
            if assignment[i]['nationality'] != 'german':
                return False

    for i in range(6):
        if assignment[i]['phone'] == 'oneplus 9':
            if assignment[i]['color'] != 'purple':
                return False

    for i in range(6):
        if assignment[i]['phone'] == 'huawei p50':
            if i == 2:
                return False

    if assignment[4]['phone'] != 'samsung galaxy s21':
        return False

    red_index = None
    white_index = None
    for i in range(6):
        if assignment[i]['color'] == 'red':
            red_index = i
        if assignment[i]['color'] == 'white':
            white_index = i
    if red_index is None or white_index is None:
        return False
    if white_index <= red_index:
        return False

    if assignment[4]['name'] != 'Bob':
        return False

    for i in range(6):
        if assignment[i]['nationality'] == 'dane':
            if assignment[i]['color'] != 'yellow':
                return False

    for i in range(6):
        if assignment[i]['nationality'] == 'norwegian':
            if assignment[i]['color'] != 'purple':
                return False

    for i in range(6):
        if assignment[i]['phone'] == 'xiaomi mi 11':
            if assignment[i]['nationality'] != 'chinese':
                return False

    return True

def backtrack(assignment, house_index, available_names, available_phones, available_nationalities, available_colors):
    if house_index == 6:
        if satisfies(assignment):
            return assignment
        else:
            return None

    if house_index == 3:
        for name in list(available_names):
            for phone in list(available_phones):
                assignment[3]['name'] = name
                assignment[3]['phone'] = phone
                new_avail_names = available_names - {name}
                new_avail_phones = available_phones - {phone}
                res = backtrack(assignment, house_index+1, new_avail_names, new_avail_phones, available_nationalities, available_colors)
                if res is not None:
                    return res
                assignment[3]['name'] = None
                assignment[3]['phone'] = None
        return None

    elif house_index == 4:
        for nation in list(available_nationalities):
            for color in list(available_colors):
                assignment[4]['nationality'] = nation
                assignment[4]['color'] = color
                new_avail_nats = available_nationalities - {nation}
                new_avail_colors = available_colors - {color}
                res = backtrack(assignment, house_index+1, available_names, available_phones, new_avail_nats, new_avail_colors)
                if res is not None:
                    return res
                assignment[4]['nationality'] = None
                assignment[4]['color'] = None
        return None

    elif house_index == 5:
        return backtrack(assignment, house_index+1, available_names, available_phones, available_nationalities, available_colors)

    else:
        for name in list(available_names):
            for phone in list(available_phones):
                for nation in list(available_nationalities):
                    for color in list(available_colors):
                        assignment[house_index] = {
                            'name': name,
                            'phone': phone,
                            'nationality': nation,
                            'color': color
                        }
                        new_avail_names = available_names - {name}
                        new_avail_phones = available_phones - {phone}
                        new_avail_nats = available_nationalities - {nation}
                        new_avail_colors = available_colors - {color}
                        res = backtrack(assignment, house_index+1, new_avail_names, new_avail_phones, new_avail_nats, new_avail_colors)
                        if res is not None:
                            return res
                        assignment[house_index] = None
        return None

def main():
    assignment = [None] * 6
    assignment[5] = {'name': 'Peter', 'phone': 'iphone 13', 'nationality': 'brit', 'color': 'blue'}
    assignment[4] = {'name': 'Bob', 'phone': 'samsung galaxy s21', 'nationality': None, 'color': None}
    assignment[3] = {'nationality': 'dane', 'color': 'yellow', 'name': None, 'phone': None}
    
    available_names = {'Carol', 'Alice', 'Arnold', 'Eric'}
    available_phones = {'google pixel 6', 'huawei p50', 'oneplus 9', 'xiaomi mi 11'}
    available_nationalities = {'swede', 'chinese', 'norwegian', 'german'}
    available_colors = {'red', 'green', 'white', 'purple'}
    
    sol = backtrack(assignment, 0, available_names, available_phones, available_nationalities, available_colors)
    if sol is None:
        print("No solution found")
        return
    
    rows = []
    for i in range(6):
        house_num = str(i+1)
        name = sol[i]['name']
        phone = sol[i]['phone']
        nationality = sol[i]['nationality']
        color = sol[i]['color']
        rows.append([house_num, name, phone, nationality, color])
    
    result = {
        "solution": {
            "header": ["House", "Name", "PhoneModel", "Nationality", "Color"],
            "rows": rows
        }
    }
    print(json.dumps(result))

if __name__ == "__main__":
    main()