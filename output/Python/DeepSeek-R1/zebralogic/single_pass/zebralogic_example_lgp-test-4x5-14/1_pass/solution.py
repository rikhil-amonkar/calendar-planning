import json

def main():
    attributes = {
        'name': ['Peter', 'Alice', 'Eric', 'Arnold'],
        'mother': ['Janelle', 'Holly', 'Aniya', 'Kailyn'],
        'smoothie': ['watermelon', 'dragonfruit', 'desert', 'cherry'],
        'height': ['tall', 'average', 'short', 'very short'],
        'education': ['high school', 'associate', 'master', 'bachelor']
    }
    
    # Initialize state: list of houses, each house is a dict of attributes with sets of possible values
    houses = []
    for _ in range(4):
        house = {}
        for attr, values in attributes.items():
            house[attr] = set(values)
        houses.append(house)
    
    # We'll define an assign function
    def assign(state, house_index, attribute, value):
        current = state[house_index][attribute]
        if isinstance(current, str):
            if current == value:
                return False  # no change
            else:
                raise Exception(f"Contradiction: house {house_index} {attribute} was {current} now {value}")
        else:
            if value not in current:
                raise Exception(f"Contradiction: house {house_index} {attribute} cannot be {value}")
            # Assign the value
            state[house_index][attribute] = value
            # Remove this value from the same attribute in other houses
            for i in range(4):
                if i == house_index:
                    continue
                if isinstance(state[i][attribute], str):
                    if state[i][attribute] == value:
                        raise Exception(f"Contradiction: value {value} for {attribute} appears in house {i} and {house_index}")
                else:
                    if value in state[i][attribute]:
                        state[i][attribute].remove(value)
                        if len(state[i][attribute]) == 1:
                            single_val = next(iter(state[i][attribute]))
                            assign(state, i, attribute, single_val)
            return True
    
    # Define the same_house constraint function
    def same_house(state, attr1, value1, attr2, value2):
        updated = False
        for i in range(4):
            if isinstance(state[i][attr1], str) and state[i][attr1] == value1:
                if isinstance(state[i][attr2], set):
                    if value2 in state[i][attr2]:
                        if assign(state, i, attr2, value2):
                            updated = True
                    else:
                        raise Exception(f"Contradiction: house {i} has {attr1}={value1} but {attr2} cannot be {value2}")
                else:
                    if state[i][attr2] != value2:
                        raise Exception(f"Contradiction: house {i} has {attr1}={value1} but {attr2}={state[i][attr2]} not {value2}")
            if isinstance(state[i][attr2], str) and state[i][attr2] == value2:
                if isinstance(state[i][attr1], set):
                    if value1 in state[i][attr1]:
                        if assign(state, i, attr1, value1):
                            updated = True
                    else:
                        raise Exception(f"Contradiction: house {i} has {attr2}={value2} but {attr1} cannot be {value1}")
                else:
                    if state[i][attr1] != value1:
                        raise Exception(f"Contradiction: house {i} has {attr2}={value2} but {attr1}={state[i][attr1]} not {value1}")
        
        for i in range(4):
            if isinstance(state[i][attr1], set) and value1 not in state[i][attr1]:
                if isinstance(state[i][attr2], set):
                    if value2 in state[i][attr2]:
                        state[i][attr2].remove(value2)
                        updated = True
                        if len(state[i][attr2]) == 1:
                            val = next(iter(state[i][attr2]))
                            if assign(state, i, attr2, val):
                                updated = True
                else:
                    if state[i][attr2] == value2:
                        raise Exception(f"Contradiction: house {i} cannot have {attr1}={value1} but has {attr2}={value2}")
            if isinstance(state[i][attr1], str) and state[i][attr1] != value1:
                if isinstance(state[i][attr2], set):
                    if value2 in state[i][attr2]:
                        state[i][attr2].remove(value2)
                        updated = True
                        if len(state[i][attr2]) == 1:
                            val = next(iter(state[i][attr2]))
                            if assign(state, i, attr2, val):
                                updated = True
                else:
                    if state[i][attr2] == value2:
                        raise Exception(f"Contradiction: house {i} has {attr1}={state[i][attr1]} not {value1} but has {attr2}={value2}")
            if isinstance(state[i][attr2], set) and value2 not in state[i][attr2]:
                if isinstance(state[i][attr1], set):
                    if value1 in state[i][attr1]:
                        state[i][attr1].remove(value1)
                        updated = True
                        if len(state[i][attr1]) == 1:
                            val = next(iter(state[i][attr1]))
                            if assign(state, i, attr1, val):
                                updated = True
                else:
                    if state[i][attr1] == value1:
                        raise Exception(f"Contradiction: house {i} cannot have {attr2}={value2} but has {attr1}={value1}")
            if isinstance(state[i][attr2], str) and state[i][attr2] != value2:
                if isinstance(state[i][attr1], set):
                    if value1 in state[i][attr1]:
                        state[i][attr1].remove(value1)
                        updated = True
                        if len(state[i][attr1]) == 1:
                            val = next(iter(state[i][attr1]))
                            if assign(state, i, attr1, val):
                                updated = True
                else:
                    if state[i][attr1] == value1:
                        raise Exception(f"Contradiction: house {i} has {attr2}={state[i][attr2]} not {value2} but has {attr1}={value1}")
        return updated
    
    # Define constraints as functions
    def constraint1(state):
        # Janelle in third house (index2)
        return assign(state, 2, 'mother', 'Janelle')
    
    def constraint9(state):
        # tall in third house
        return assign(state, 2, 'height', 'tall')
    
    def constraint12(state):
        # Alice in third house
        return assign(state, 2, 'name', 'Alice')
    
    def constraint3(state):
        # desert not in first house (index0)
        updated = False
        if isinstance(state[0]['smoothie'], set):
            if 'desert' in state[0]['smoothie']:
                state[0]['smoothie'].remove('desert')
                updated = True
                if len(state[0]['smoothie']) == 1:
                    val = next(iter(state[0]['smoothie']))
                    if assign(state, 0, 'smoothie', val):
                        updated = True
        return updated
    
    def constraint6(state):
        # high school not in third house (index2)
        updated = False
        if isinstance(state[2]['education'], set):
            if 'high school' in state[2]['education']:
                state[2]['education'].remove('high school')
                updated = True
                if len(state[2]['education']) == 1:
                    val = next(iter(state[2]['education']))
                    if assign(state, 2, 'education', val):
                        updated = True
        return updated
    
    def constraint2(state):
        # desert smoothie and master education same house
        return same_house(state, 'smoothie', 'desert', 'education', 'master')
    
    def constraint7(state):
        # mother Kailyn and education associate same house
        return same_house(state, 'mother', 'Kailyn', 'education', 'associate')
    
    def constraint8(state):
        # cherry smoothie and mother Aniya same house
        return same_house(state, 'smoothie', 'cherry', 'mother', 'Aniya')
    
    def constraint4(state):
        # very short left of high school: house(very short) < house(high school)
        updated = False
        for i in range(4):
            # If house i is very short or might be
            is_very_short = False
            if isinstance(state[i]['height'], str):
                is_very_short = (state[i]['height'] == 'very short')
            elif 'very short' in state[i]['height']:
                is_very_short = True
            if is_very_short:
                # Check if there exists a j>i that can be high school
                found = False
                for j in range(i+1, 4):
                    if isinstance(state[j]['education'], str):
                        if state[j]['education'] == 'high school':
                            found = True
                            break
                    elif 'high school' in state[j]['education']:
                        found = True
                        break
                if not found:
                    if isinstance(state[i]['height'], set):
                        if 'very short' in state[i]['height']:
                            state[i]['height'].remove('very short')
                            updated = True
                            if len(state[i]['height']) == 1:
                                val = next(iter(state[i]['height']))
                                if assign(state, i, 'height', val):
                                    updated = True
                    else:
                        if state[i]['height'] == 'very short':
                            raise Exception("Contradiction: no high school to the right of very short")
        for j in range(4):
            is_high_school = False
            if isinstance(state[j]['education'], str):
                is_high_school = (state[j]['education'] == 'high school')
            elif 'high school' in state[j]['education']:
                is_high_school = True
            if is_high_school:
                found = False
                for i in range(j):
                    if isinstance(state[i]['height'], str):
                        if state[i]['height'] == 'very short':
                            found = True
                            break
                    elif 'very short' in state[i]['height']:
                        found = True
                        break
                if not found:
                    if isinstance(state[j]['education'], set):
                        if 'high school' in state[j]['education']:
                            state[j]['education'].remove('high school')
                            updated = True
                            if len(state[j]['education']) == 1:
                                val = next(iter(state[j]['education']))
                                if assign(state, j, 'education', val):
                                    updated = True
                    else:
                        if state[j]['education'] == 'high school':
                            raise Exception("Contradiction: no very short to the left of high school")
        return updated
    
    def constraint10(state):
        # Arnold is right of average height: house(Arnold) > house(average height)
        updated = False
        for i in range(4):
            is_avg = False
            if isinstance(state[i]['height'], str):
                is_avg = (state[i]['height'] == 'average')
            elif 'average' in state[i]['height']:
                is_avg = True
            if is_avg:
                found = False
                for j in range(i+1, 4):
                    if isinstance(state[j]['name'], str):
                        if state[j]['name'] == 'Arnold':
                            found = True
                            break
                    elif 'Arnold' in state[j]['name']:
                        found = True
                        break
                if not found:
                    if isinstance(state[i]['height'], set):
                        if 'average' in state[i]['height']:
                            state[i]['height'].remove('average')
                            updated = True
                            if len(state[i]['height']) == 1:
                                val = next(iter(state[i]['height']))
                                if assign(state, i, 'height', val):
                                    updated = True
                    else:
                        if state[i]['height'] == 'average':
                            raise Exception("Contradiction: no Arnold to the right of average")
        for j in range(4):
            is_arnold = False
            if isinstance(state[j]['name'], str):
                is_arnold = (state[j]['name'] == 'Arnold')
            elif 'Arnold' in state[j]['name']:
                is_arnold = True
            if is_arnold:
                found = False
                for i in range(j):
                    if isinstance(state[i]['height'], str):
                        if state[i]['height'] == 'average':
                            found = True
                            break
                    elif 'average' in state[i]['height']:
                        found = True
                        break
                if not found:
                    if isinstance(state[j]['name'], set):
                        if 'Arnold' in state[j]['name']:
                            state[j]['name'].remove('Arnold')
                            updated = True
                            if len(state[j]['name']) == 1:
                                val = next(iter(state[j]['name']))
                                if assign(state, j, 'name', val):
                                    updated = True
                    else:
                        if state[j]['name'] == 'Arnold':
                            raise Exception("Contradiction: no average height to the left of Arnold")
        return updated
    
    def constraint11(state):
        # dragonfruit directly left of short: house(dragonfruit) = house(short) - 1
        updated = False
        for i in range(3):  # dragonfruit can only be in 0,1,2
            is_dragonfruit = False
            if isinstance(state[i]['smoothie'], str):
                is_dragonfruit = (state[i]['smoothie'] == 'dragonfruit')
            elif 'dragonfruit' in state[i]['smoothie']:
                is_dragonfruit = True
            if is_dragonfruit:
                j = i+1
                is_short = False
                if isinstance(state[j]['height'], str):
                    is_short = (state[j]['height'] == 'short')
                elif 'short' in state[j]['height']:
                    is_short = True
                if not is_short:
                    if isinstance(state[i]['smoothie'], set):
                        if 'dragonfruit' in state[i]['smoothie']:
                            state[i]['smoothie'].remove('dragonfruit')
                            updated = True
                            if len(state[i]['smoothie']) == 1:
                                val = next(iter(state[i]['smoothie']))
                                if assign(state, i, 'smoothie', val):
                                    updated = True
                    else:
                        if state[i]['smoothie'] == 'dragonfruit':
                            raise Exception("Contradiction: no short to the right of dragonfruit")
        for j in range(1,4):  # short can only be in 1,2,3
            is_short = False
            if isinstance(state[j]['height'], str):
                is_short = (state[j]['height'] == 'short')
            elif 'short' in state[j]['height']:
                is_short = True
            if is_short:
                i = j-1
                is_dragonfruit = False
                if isinstance(state[i]['smoothie'], str):
                    is_dragonfruit = (state[i]['smoothie'] == 'dragonfruit')
                elif 'dragonfruit' in state[i]['smoothie']:
                    is_dragonfruit = True
                if not is_dragonfruit:
                    if isinstance(state[j]['height'], set):
                        if 'short' in state[j]['height']:
                            state[j]['height'].remove('short')
                            updated = True
                            if len(state[j]['height']) == 1:
                                val = next(iter(state[j]['height']))
                                if assign(state, j, 'height', val):
                                    updated = True
                    else:
                        if state[j]['height'] == 'short':
                            raise Exception("Contradiction: no dragonfruit to the left of short")
        return updated
    
    def constraint5(state):
        # Eric and cherry smoothie adjacent: |house(Eric) - house(cherry)|=1
        updated = False
        eric_house = None
        cherry_house = None
        possible_eric = []
        possible_cherry = []
        for i in range(4):
            if isinstance(state[i]['name'], str):
                if state[i]['name'] == 'Eric':
                    eric_house = i
            elif isinstance(state[i]['name'], set) and 'Eric' in state[i]['name']:
                possible_eric.append(i)
            if isinstance(state[i]['smoothie'], str):
                if state[i]['smoothie'] == 'cherry':
                    cherry_house = i
            elif isinstance(state[i]['smoothie'], set) and 'cherry' in state[i]['smoothie']:
                possible_cherry.append(i)
        if eric_house is not None and cherry_house is not None:
            if abs(eric_house - cherry_house) != 1:
                raise Exception("Contradiction: Eric and cherry not adjacent")
        elif eric_house is not None:
            possible = []
            if eric_house > 0:
                possible.append(eric_house-1)
            if eric_house < 3:
                possible.append(eric_house+1)
            for i in range(4):
                if i not in possible:
                    if isinstance(state[i]['smoothie'], set) and 'cherry' in state[i]['smoothie']:
                        state[i]['smoothie'].remove('cherry')
                        updated = True
                        if len(state[i]['smoothie']) == 1:
                            val = next(iter(state[i]['smoothie']))
                            if assign(state, i, 'smoothie', val):
                                updated = True
        elif cherry_house is not None:
            possible = []
            if cherry_house > 0:
                possible.append(cherry_house-1)
            if cherry_house < 3:
                possible.append(cherry_house+1)
            for i in range(4):
                if i not in possible:
                    if isinstance(state[i]['name'], set) and 'Eric' in state[i]['name']:
                        state[i]['name'].remove('Eric')
                        updated = True
                        if len(state[i]['name']) == 1:
                            val = next(iter(state[i]['name']))
                            if assign(state, i, 'name', val):
                                updated = True
        # Remove Eric from houses that are not adjacent to any possible cherry
        for i in possible_eric:
            adj = []
            if i>0: adj.append(i-1)
            if i<3: adj.append(i+1)
            found = False
            for j in adj:
                if j in possible_cherry:
                    found = True
                    break
            if not found:
                if isinstance(state[i]['name'], set) and 'Eric' in state[i]['name']:
                    state[i]['name'].remove('Eric')
                    updated = True
                    if len(state[i]['name']) == 1:
                        val = next(iter(state[i]['name']))
                        if assign(state, i, 'name', val):
                            updated = True
        for j in possible_cherry:
            adj = []
            if j>0: adj.append(j-1)
            if j<3: adj.append(j+1)
            found = False
            for i in adj:
                if i in possible_eric:
                    found = True
                    break
            if not found:
                if isinstance(state[j]['smoothie'], set) and 'cherry' in state[j]['smoothie']:
                    state[j]['smoothie'].remove('cherry')
                    updated = True
                    if len(state[j]['smoothie']) == 1:
                        val = next(iter(state[j]['smoothie']))
                        if assign(state, j, 'smoothie', val):
                            updated = True
        return updated
    
    constraints = [
        constraint1,
        constraint9,
        constraint12,
        constraint3,
        constraint6,
        constraint2,
        constraint7,
        constraint8,
        constraint4,
        constraint10,
        constraint11,
        constraint5
    ]
    
    # Propagate constraints until no changes
    changed = True
    while changed:
        changed = False
        for constraint in constraints:
            if constraint(houses):
                changed = True
    
    # Check if solved: all attributes are strings
    for i in range(4):
        for attr in attributes:
            if not isinstance(houses[i][attr], str):
                # If not, we try to assign the only remaining possibility?
                if isinstance(houses[i][attr], set) and len(houses[i][attr]) == 1:
                    val = next(iter(houses[i][attr]))
                    assign(houses, i, attr, val)
                    changed = True
                else:
                    # If still not solved, we have a problem
                    raise Exception(f"House {i} {attr} not solved: {houses[i][attr]}")
    
    # Prepare the solution in JSON format
    header = ["House", "Name", "Mother", "Smoothie", "Height", "Education"]
    rows = []
    for i in range(4):
        row = [str(i+1)]
        for attr in ['name', 'mother', 'smoothie', 'height', 'education']:
            row.append(houses[i][attr])
        rows.append(row)
    
    solution = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    
    print(json.dumps(solution))

if __name__ == "__main__":
    main()