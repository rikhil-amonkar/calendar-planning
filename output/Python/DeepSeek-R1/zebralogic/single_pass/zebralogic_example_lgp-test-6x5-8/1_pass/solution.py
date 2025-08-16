import json

attributes = ['name', 'animal', 'occupation', 'sport', 'height']
all_values = {
    'name': ['Arnold', 'Peter', 'Bob', 'Eric', 'Carol', 'Alice'],
    'animal': ['horse', 'rabbit', 'fish', 'cat', 'bird', 'dog'],
    'occupation': ['engineer', 'nurse', 'lawyer', 'teacher', 'artist', 'doctor'],
    'sport': ['basketball', 'volleyball', 'soccer', 'tennis', 'baseball', 'swimming'],
    'height': ['average', 'tall', 'short', 'very short', 'very tall', 'super tall']
}

preassigned = {
    (0, 'sport'): 'baseball',
    (1, 'occupation'): 'engineer',
    (1, 'animal'): 'dog',
    (4, 'occupation'): 'lawyer',
    (4, 'height'): 'super tall'
}

assignment = {}
for key, value in preassigned.items():
    assignment[key] = value

unassigned_vars = []
for house in range(6):
    for att in attributes:
        if (house, att) not in preassigned:
            unassigned_vars.append((house, att))

def check_constraints(assignment):
    # Check all-different for each attribute
    for att in attributes:
        values = []
        for house in range(6):
            key = (house, att)
            if key in assignment:
                values.append(assignment[key])
        if len(values) != len(set(values)):
            return False

    # Clue 1: engineer is dog owner
    for house in range(6):
        occ_key = (house, 'occupation')
        ani_key = (house, 'animal')
        if occ_key in assignment and ani_key in assignment:
            occ_val = assignment[occ_key]
            ani_val = assignment[ani_key]
            if (occ_val == 'engineer') != (ani_val == 'dog'):
                return False

    # Clue 2: average height left of short
    avg_house = None
    short_house = None
    for house in range(6):
        key = (house, 'height')
        if key in assignment:
            h_val = assignment[key]
            if h_val == 'average':
                avg_house = house
            if h_val == 'short':
                short_house = house
    if avg_house is not None and short_house is not None:
        if avg_house >= short_house:
            return False

    # Clue 3: average height directly left of rabbit
    for house in range(6):
        key = (house, 'height')
        if key in assignment and assignment[key] == 'average':
            if house+1 >= 6:
                return False
            key_rabbit = (house+1, 'animal')
            if key_rabbit in assignment:
                if assignment[key_rabbit] != 'rabbit':
                    return False
    for house in range(6):
        key = (house, 'animal')
        if key in assignment and assignment[key] == 'rabbit':
            if house == 0:
                return False
            key_avg = (house-1, 'height')
            if key_avg in assignment:
                if assignment[key_avg] != 'average':
                    return False

    # Clue 4: tall left of very short
    tall_house = None
    very_short_house = None
    for house in range(6):
        key = (house, 'height')
        if key in assignment:
            h_val = assignment[key]
            if h_val == 'tall':
                tall_house = house
            if h_val == 'very short':
                very_short_house = house
    if tall_house is not None and very_short_house is not None:
        if tall_house >= very_short_house:
            return False

    # Clue 5: Arnold has cat
    for house in range(6):
        name_key = (house, 'name')
        ani_key = (house, 'animal')
        if name_key in assignment and ani_key in assignment:
            name_val = assignment[name_key]
            ani_val = assignment[ani_key]
            if name_val == 'Arnold' and ani_val != 'cat':
                return False
            if ani_val == 'cat' and name_val != 'Arnold':
                return False

    # Clue 6: horse owner is teacher
    for house in range(6):
        ani_key = (house, 'animal')
        occ_key = (house, 'occupation')
        if ani_key in assignment and occ_key in assignment:
            ani_val = assignment[ani_key]
            occ_val = assignment[occ_key]
            if (ani_val == 'horse') != (occ_val == 'teacher'):
                return False

    # Clue 7: Carol loves soccer
    for house in range(6):
        name_key = (house, 'name')
        sport_key = (house, 'sport')
        if name_key in assignment and sport_key in assignment:
            name_val = assignment[name_key]
            sport_val = assignment[sport_key]
            if name_val == 'Carol' and sport_val != 'soccer':
                return False
            if sport_val == 'soccer' and name_val != 'Carol':
                return False

    # Clue 8: tall height loves volleyball
    for house in range(6):
        height_key = (house, 'height')
        sport_key = (house, 'sport')
        if height_key in assignment and sport_key in assignment:
            height_val = assignment[height_key]
            sport_val = assignment[sport_key]
            if height_val == 'tall' and sport_val != 'volleyball':
                return False
            if sport_val == 'volleyball' and height_val != 'tall':
                return False

    # Clue 9: lawyer in fifth house (index4)
    key = (4, 'occupation')
    if key in assignment:
        if assignment[key] != 'lawyer':
            return False

    # Clue 10: tennis lover is teacher
    for house in range(6):
        sport_key = (house, 'sport')
        occ_key = (house, 'occupation')
        if sport_key in assignment and occ_key in assignment:
            sport_val = assignment[sport_key]
            occ_val = assignment[occ_key]
            if (sport_val == 'tennis') != (occ_val == 'teacher'):
                return False

    # Clue 11: average height is swimming
    for house in range(6):
        height_key = (house, 'height')
        sport_key = (house, 'sport')
        if height_key in assignment and sport_key in assignment:
            height_val = assignment[height_key]
            sport_val = assignment[sport_key]
            if (height_val == 'average') != (sport_val == 'swimming'):
                return False

    # Clue 12: baseball directly left of engineer
    for house in range(5):
        sport_key = (house, 'sport')
        if sport_key in assignment and assignment[sport_key] == 'baseball':
            occ_key_next = (house+1, 'occupation')
            if occ_key_next in assignment:
                if assignment[occ_key_next] != 'engineer':
                    return False
    for house in range(1,6):
        occ_key = (house, 'occupation')
        if occ_key in assignment and assignment[occ_key] == 'engineer':
            sport_key_prev = (house-1, 'sport')
            if sport_key_prev in assignment:
                if assignment[sport_key_prev] != 'baseball':
                    return False

    # Clue 13: Peter is nurse
    for house in range(6):
        name_key = (house, 'name')
        occ_key = (house, 'occupation')
        if name_key in assignment and occ_key in assignment:
            name_val = assignment[name_key]
            occ_val = assignment[occ_key]
            if name_val == 'Peter' and occ_val != 'nurse':
                return False
            if occ_val == 'nurse' and name_val != 'Peter':
                return False

    # Clue 14: Bob is right of artist
    bob_house = None
    artist_house = None
    for house in range(6):
        name_key = (house, 'name')
        if name_key in assignment and assignment[name_key] == 'Bob':
            bob_house = house
        occ_key = (house, 'occupation')
        if occ_key in assignment and assignment[occ_key] == 'artist':
            artist_house = house
    if bob_house is not None and artist_house is not None:
        if bob_house <= artist_house:
            return False

    # Clue 15: teacher directly left of soccer
    for house in range(5):
        occ_key = (house, 'occupation')
        if occ_key in assignment and assignment[occ_key] == 'teacher':
            sport_key_next = (house+1, 'sport')
            if sport_key_next in assignment:
                if assignment[sport_key_next] != 'soccer':
                    return False
    for house in range(1,6):
        sport_key = (house, 'sport')
        if sport_key in assignment and assignment[sport_key] == 'soccer':
            occ_key_prev = (house-1, 'occupation')
            if occ_key_prev in assignment:
                if assignment[occ_key_prev] != 'teacher':
                    return False

    # Clue 16: rabbit owner is Alice
    for house in range(6):
        ani_key = (house, 'animal')
        name_key = (house, 'name')
        if ani_key in assignment and name_key in assignment:
            ani_val = assignment[ani_key]
            name_val = assignment[name_key]
            if (ani_val == 'rabbit') != (name_val == 'Alice'):
                return False

    # Clue 17: fish enthusiast is Carol
    for house in range(6):
        ani_key = (house, 'animal')
        name_key = (house, 'name')
        if ani_key in assignment and name_key in assignment:
            ani_val = assignment[ani_key]
            name_val = assignment[name_key]
            if (ani_val == 'fish') != (name_val == 'Carol'):
                return False

    # Clue 18: baseball in first house (index0)
    key = (0, 'sport')
    if key in assignment:
        if assignment[key] != 'baseball':
            return False

    # Clue 19: cat lover right of very short
    cat_house = None
    very_short_house = None
    for house in range(6):
        key_ani = (house, 'animal')
        if key_ani in assignment and assignment[key_ani] == 'cat':
            cat_house = house
        key_ht = (house, 'height')
        if key_ht in assignment and assignment[key_ht] == 'very short':
            very_short_house = house
    if cat_house is not None and very_short_house is not None:
        if cat_house <= very_short_house:
            return False

    # Clue 20: super tall in fifth house (index4)
    key = (4, 'height')
    if key in assignment:
        if assignment[key] != 'super tall':
            return False

    return True

def backtrack(assignment, unassigned):
    if len(unassigned) == 0:
        if check_constraints(assignment):
            return assignment
        else:
            return None

    var = unassigned[0]
    house, att = var

    used = set()
    for h in range(6):
        key = (h, att)
        if key in assignment:
            used.add(assignment[key])
    
    available = list(set(all_values[att]) - used)
    
    for value in available:
        assignment[var] = value
        if check_constraints(assignment):
            result = backtrack(assignment, unassigned[1:])
            if result is not None:
                return result
        del assignment[var]
    
    return None

result_assignment = backtrack(assignment, unassigned_vars)

if result_assignment is None:
    print('No solution found')
    exit(1)

output = {}
output['solution'] = {
    'header': ["House", "Name", "Animal", "Occupation", "FavoriteSport", "Height"],
    'rows': []
}

for house in range(6):
    row = [str(house+1)]
    for att in ['name', 'animal', 'occupation', 'sport', 'height']:
        key = (house, att)
        value = result_assignment.get(key)
        row.append(value)
    output['solution']['rows'].append(row)

json_output = json.dumps(output, indent=2)
print(json_output)