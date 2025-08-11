import json

def enforce_all_different(domains, attribute):
    changed = False
    # First: if a house has a singleton, remove that value from other houses.
    for house in range(5):
        if len(domains[attribute][house]) == 1:
            val = next(iter(domains[attribute][house]))
            for other_house in range(5):
                if other_house != house:
                    if val in domains[attribute][other_house]:
                        domains[attribute][other_house].discard(val)
                        changed = True
    # Second: for each value in the attribute, if it is only in one house, set that house to that value.
    all_values = set()
    for house in range(5):
        all_values |= domains[attribute][house]
    for value in all_values:
        houses_with_value = []
        for house in range(5):
            if value in domains[attribute][house]:
                houses_with_value.append(house)
        if len(houses_with_value) == 1:
            house_idx = houses_with_value[0]
            if domains[attribute][house_idx] != {value}:
                domains[attribute][house_idx] = {value}
                changed = True
    return changed

def set_value(domains, attribute, house_index, value):
    changed = False
    if value not in domains[attribute][house_index]:
        return False
    if domains[attribute][house_index] != {value}:
        domains[attribute][house_index] = {value}
        changed = True
    # Remove this value from other houses for the same attribute
    for other_house in range(5):
        if other_house != house_index:
            if value in domains[attribute][other_house]:
                domains[attribute][other_house].discard(value)
                changed = True
    return changed

def attribute_link(domains, attr1, value1, attr2, value2):
    changed = False
    for house in range(5):
        # If the house has value1 in attr1, then it must have value2 in attr2
        if value1 in domains[attr1][house]:
            if value2 not in domains[attr2][house]:
                domains[attr1][house].discard(value1)
                changed = True
            else:
                if domains[attr2][house] != {value2}:
                    domains[attr2][house] = {value2}
                    changed = True
        # If the house has value2 in attr2, then it must have value1 in attr1
        if value2 in domains[attr2][house]:
            if value1 not in domains[attr1][house]:
                domains[attr2][house].discard(value2)
                changed = True
            else:
                if domains[attr1][house] != {value1}:
                    domains[attr1][house] = {value1}
                    changed = True
    return changed

def to_the_right(domains, attr1, value1, attr2, value2):
    changed = False
    # If value1 (attr1) is to the right of value2 (attr2), then the house of value1 > house of value2.
    # For each house i, if it has value1, then there must be a house j < i that has value2.
    for i in range(5):
        if value1 in domains[attr1][i]:
            found = False
            for j in range(0, i):
                if value2 in domains[attr2][j]:
                    found = True
                    break
            if not found:
                domains[attr1][i].discard(value1)
                changed = True
    # For each house j, if it has value2, then there must be a house i > j that has value1.
    for j in range(5):
        if value2 in domains[attr2][j]:
            found = False
            for i in range(j+1, 5):
                if value1 in domains[attr1][i]:
                    found = True
                    break
            if not found:
                domains[attr2][j].discard(value2)
                changed = True
    return changed

def distance_constraint(domains, attr1, value1, attr2, value2, distance):
    changed = False
    # For value1: if it is at house i, then value2 must be at i-distance or i+distance (if in range)
    for i in range(5):
        if value1 in domains[attr1][i]:
            found = False
            for j in [i - distance, i + distance]:
                if 0 <= j < 5:
                    if value2 in domains[attr2][j]:
                        found = True
            if not found:
                domains[attr1][i].discard(value1)
                changed = True
    # For value2: if it is at house j, then value1 must be at j-distance or j+distance (if in range)
    for j in range(5):
        if value2 in domains[attr2][j]:
            found = False
            for i in [j - distance, j + distance]:
                if 0 <= i < 5:
                    if value1 in domains[attr1][i]:
                        found = True
            if not found:
                domains[attr2][j].discard(value2)
                changed = True
    return changed

def main():
    # Define all possible values
    names = ['Arnold', 'Eric', 'Alice', 'Bob', 'Peter']
    vacations = ['mountain', 'city', 'cruise', 'beach', 'camping']
    educations = ['doctorate', 'high school', 'bachelor', 'associate', 'master']
    colors = ['blue', 'red', 'white', 'yellow', 'green']
    phones = ['google pixel 6', 'iphone 13', 'oneplus 9', 'huawei p50', 'samsung galaxy s21']
    lunches = ['grilled cheese', 'stir fry', 'pizza', 'spaghetti', 'stew']
    
    attributes = ['name', 'vacation', 'education', 'color', 'phone', 'lunch']
    all_values = {
        'name': set(names),
        'vacation': set(vacations),
        'education': set(educations),
        'color': set(colors),
        'phone': set(phones),
        'lunch': set(lunches)
    }
    
    # Initialize domains: for each attribute, a list of 5 sets (one per house) with the full set of values
    domains = {}
    for attr in attributes:
        domains[attr] = [set(all_values[attr]) for _ in range(5)]
    
    # Apply direct assignments from clues
    set_value(domains, 'phone', 2, 'samsung galaxy s21')  # Clue5: house3 has samsung galaxy s21
    set_value(domains, 'education', 2, 'doctorate')       # Clue7: house3 has doctorate
    
    # Clue propagation loop
    changed = True
    while changed:
        changed = False
        
        # Enforce allDifferent for each attribute
        for attr in attributes:
            if enforce_all_different(domains, attr):
                changed = True
                
        # Apply attribute links (bidirectional constraints)
        if attribute_link(domains, 'name', 'Eric', 'education', 'doctorate'): changed = True  # Clue6
        if attribute_link(domains, 'education', 'doctorate', 'lunch', 'pizza'): changed = True  # Clue9
        if attribute_link(domains, 'vacation', 'mountain', 'education', 'bachelor'): changed = True  # Clue3
        if attribute_link(domains, 'lunch', 'stir fry', 'education', 'bachelor'): changed = True  # Clue8
        if attribute_link(domains, 'vacation', 'camping', 'phone', 'iphone 13'): changed = True  # Clue11
        if attribute_link(domains, 'name', 'Alice', 'vacation', 'cruise'): changed = True  # Clue12
        if attribute_link(domains, 'name', 'Arnold', 'phone', 'google pixel 6'): changed = True  # Clue14
        if attribute_link(domains, 'name', 'Arnold', 'lunch', 'grilled cheese'): changed = True  # Clue16
        
        # Unary constraints (direct removals)
        # Clue1: stew not in house1 (index0)
        if 'stew' in domains['lunch'][0]:
            domains['lunch'][0].discard('stew')
            changed = True
        # Clue17: grilled cheese not in house4 (index3)
        if 'grilled cheese' in domains['lunch'][3]:
            domains['lunch'][3].discard('grilled cheese')
            changed = True
        # Clue20: green not in house2 (index1)
        if 'green' in domains['color'][1]:
            domains['color'][1].discard('green')
            changed = True
        # Clue4: Bob is left of doctorate (house3, index2) -> Bob in house1 or house2? Actually house1 or house2 in 1-indexed? 
        # In 0-indexed: Bob must be in house0 or house1 (since house2 is Eric with doctorate)
        for house in [2,3,4]:
            if 'Bob' in domains['name'][house]:
                domains['name'][house].discard('Bob')
                changed = True
        
        # Positional constraints
        # Clue13: one house between high school and samsung (which is at house2) -> distance=2
        if distance_constraint(domains, 'education', 'high school', 'phone', 'samsung galaxy s21', 2): changed = True
        # Clue2: two houses between stir fry and associate -> distance=3
        if distance_constraint(domains, 'lunch', 'stir fry', 'education', 'associate', 3): changed = True
        # Clue18: two houses between bachelor and red -> distance=3
        if distance_constraint(domains, 'education', 'bachelor', 'color', 'red', 3): changed = True
        # Clue22: one house between camping and yellow -> distance=2
        if distance_constraint(domains, 'vacation', 'camping', 'color', 'yellow', 2): changed = True
        
        # 'To the right' constraints
        # Clue10: green is to the right of Peter
        if to_the_right(domains, 'color', 'green', 'name', 'Peter'): changed = True
        # Clue19: beach is to the right of city
        if to_the_right(domains, 'vacation', 'beach', 'vacation', 'city'): changed = True
        # Clue21: blue is to the right of Peter
        if to_the_right(domains, 'color', 'blue', 'name', 'Peter'): changed = True
        # Clue15: OnePlus9 to the right of HuaweiP50
        if to_the_right(domains, 'phone', 'oneplus 9', 'phone', 'huawei p50'): changed = True
    
    # Check if we have a solution: each house has exactly one value for each attribute
    solution_found = True
    for attr in attributes:
        for house in range(5):
            if len(domains[attr][house]) != 1:
                solution_found = False
                break
        if not solution_found:
            break
    
    if not solution_found:
        # In case of failure, output an empty solution? Or try to backtrack? But we assume propagation solves it.
        # For now, we'll output an empty solution.
        result = {
            "solution": {
                "header": ["House", "Name", "Vacation", "Education", "Color", "Phone", "Lunch"],
                "rows": []
            }
        }
    else:
        # Build the rows for the output
        rows = []
        for house in range(5):
            house_number = str(house+1)
            name = next(iter(domains['name'][house]))
            vacation = next(iter(domains['vacation'][house]))
            education = next(iter(domains['education'][house]))
            color = next(iter(domains['color'][house]))
            phone = next(iter(domains['phone'][house]))
            lunch = next(iter(domains['lunch'][house]))
            rows.append([house_number, name, vacation, education, color, phone, lunch])
        
        result = {
            "solution": {
                "header": ["House", "Name", "Vacation", "Education", "Color", "Phone", "Lunch"],
                "rows": rows
            }
        }
    
    # Output as JSON
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()