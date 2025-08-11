import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values for each category
    names = ['Alice', 'Bob', 'Arnold', 'Eric', 'Peter']
    vacations = ['cruise', 'city', 'camping', 'beach', 'mountain']
    children = ['Bella', 'Samantha', 'Fred', 'Meredith', 'Timothy']
    nationalities = ['dane', 'norwegian', 'brit', 'german', 'swede']
    houses = ['1', '2', '3', '4', '5']
    
    # We'll represent each house as a dictionary with the attributes
    # Initialize all possible values for each attribute in each house
    possibilities = []
    for house in houses:
        possibilities.append({
            'House': house,
            'Name': names.copy(),
            'Vacation': vacations.copy(),
            'Child': children.copy(),
            'Nationality': nationalities.copy()
        })
    
    # Apply the clues one by one to narrow down possibilities
    
    # Clue 6: The person who likes going on cruises is in the first house.
    for attr in possibilities[0]['Vacation'][:]:
        if attr != 'cruise':
            possibilities[0]['Vacation'].remove(attr)
    
    # Clue 1: The Norwegian is Peter.
    for i in range(5):
        if 'Peter' in possibilities[i]['Name']:
            for nat in possibilities[i]['Nationality'][:]:
                if nat != 'norwegian':
                    possibilities[i]['Nationality'].remove(nat)
        if 'norwegian' in possibilities[i]['Nationality']:
            for name in possibilities[i]['Name'][:]:
                if name != 'Peter':
                    possibilities[i]['Name'].remove(name)
    
    # Clue 5: Alice is the British person.
    for i in range(5):
        if 'Alice' in possibilities[i]['Name']:
            for nat in possibilities[i]['Nationality'][:]:
                if nat != 'brit':
                    possibilities[i]['Nationality'].remove(nat)
        if 'brit' in possibilities[i]['Nationality']:
            for name in possibilities[i]['Name'][:]:
                if name != 'Alice':
                    possibilities[i]['Name'].remove(name)
    
    # Clue 12: The Dane is in the fifth house.
    for nat in possibilities[4]['Nationality'][:]:
        if nat != 'dane':
            possibilities[4]['Nationality'].remove(nat)
    
    # Clue 8: Eric is not in the fifth house.
    if 'Eric' in possibilities[4]['Name']:
        possibilities[4]['Name'].remove('Eric')
    
    # Clue 11: Bob is the person who enjoys camping trips.
    for i in range(5):
        if 'Bob' in possibilities[i]['Name']:
            for vac in possibilities[i]['Vacation'][:]:
                if vac != 'camping':
                    possibilities[i]['Vacation'].remove(vac)
        if 'camping' in possibilities[i]['Vacation']:
            for name in possibilities[i]['Name'][:]:
                if name != 'Bob':
                    possibilities[i]['Name'].remove(name)
    
    # Clue 13: The person who enjoys camping trips is not in the fifth house.
    if 'camping' in possibilities[4]['Vacation']:
        possibilities[4]['Vacation'].remove('camping')
    
    # Clue 7: The person's child is named Meredith is in the fourth house.
    for child in possibilities[3]['Child'][:]:
        if child != 'Meredith':
            possibilities[3]['Child'].remove(child)
    
    # Clue 4: The person's child is named Bella is not in the second house.
    if 'Bella' in possibilities[1]['Child']:
        possibilities[1]['Child'].remove('Bella')
    
    # Clue 2: The Swedish person is the person's child is named Bella.
    # This means that in the house where nationality is swede, child is Bella
    for i in range(5):
        if 'swede' in possibilities[i]['Nationality']:
            for child in possibilities[i]['Child'][:]:
                if child != 'Bella':
                    possibilities[i]['Child'].remove(child)
        if 'Bella' in possibilities[i]['Child']:
            for nat in possibilities[i]['Nationality'][:]:
                if nat != 'swede':
                    possibilities[i]['Nationality'].remove(nat)
    
    # Clue 9: The Swedish person is somewhere to the right of the Norwegian.
    # Find Norwegian's house index
    norwegian_house = None
    for i in range(5):
        if 'norwegian' in possibilities[i]['Nationality']:
            norwegian_house = i
            break
    # Swedish person must be in a house with index > norwegian_house
    for i in range(5):
        if i <= norwegian_house and 'swede' in possibilities[i]['Nationality']:
            possibilities[i]['Nationality'].remove('swede')
    
    # Clue 3: The person who loves beach vacations is directly left of the person's child is named Samantha.
    # This means beach is in house X, and Samantha is in house X+1
    for i in range(4):
        if 'beach' not in possibilities[i]['Vacation']:
            continue
        # If beach is in i, then Samantha must be in i+1
        if 'Samantha' not in possibilities[i+1]['Child']:
            # Remove beach from i
            possibilities[i]['Vacation'].remove('beach')
    
    # Also, for any house j > 0, if Samantha is in j, then beach must be in j-1
    for j in range(1,5):
        if 'Samantha' in possibilities[j]['Child']:
            if 'beach' not in possibilities[j-1]['Vacation']:
                # Remove Samantha from j
                possibilities[j]['Child'].remove('Samantha')
    
    # Clue 10: There is one house between the person's child is named Fred and the person who prefers city breaks.
    # This means if Fred is in X, city is in X+2, or city is in X, Fred is in X-2
    # We'll check all possible positions
    for fred_pos in range(5):
        if 'Fred' not in possibilities[fred_pos]['Child']:
            continue
        city_pos = fred_pos + 2
        if city_pos < 5:
            if 'city' not in possibilities[city_pos]['Vacation']:
                # Remove Fred from fred_pos
                possibilities[fred_pos]['Child'].remove('Fred')
    
    for city_pos in range(5):
        if 'city' not in possibilities[city_pos]['Vacation']:
            continue
        fred_pos = city_pos - 2
        if fred_pos >= 0:
            if 'Fred' not in possibilities[fred_pos]['Child']:
                # Remove city from city_pos
                possibilities[city_pos]['Vacation'].remove('city')
    
    # Now we need to find a consistent assignment
    # We'll use backtracking to find a solution that satisfies all constraints
    
    # Let's extract the remaining possibilities for each house
    house_possibilities = []
    for house in possibilities:
        hp = {
            'House': house['House'],
            'Name': house['Name'],
            'Vacation': house['Vacation'],
            'Child': house['Child'],
            'Nationality': house['Nationality']
        }
        house_possibilities.append(hp)
    
    # We'll try all possible combinations
    from itertools import product
    
    # Generate all possible combinations for each house
    possible_solutions = []
    
    # Since the search space might be large, we'll try to find a solution step by step
    # Let's try to assign names first
    names_left = names.copy()
    assigned_names = [None] * 5
    
    # Assign names based on current possibilities
    for i in range(5):
        if len(house_possibilities[i]['Name']) == 1:
            name = house_possibilities[i]['Name'][0]
            assigned_names[i] = name
            names_left.remove(name)
    
    # Now assign remaining names
    from itertools import permutations
    for name_perm in permutations(names_left):
        current_assignment = assigned_names.copy()
        name_index = 0
        valid = True
        for i in range(5):
            if current_assignment[i] is None:
                current_assignment[i] = name_perm[name_index]
                name_index += 1
                # Check if this name is allowed in this house
                if current_assignment[i] not in house_possibilities[i]['Name']:
                    valid = False
                    break
        if not valid:
            continue
        
        # Check if all names are unique
        if len(set(current_assignment)) != 5:
            continue
        
        # Now assign nationalities
        nationalities_left = nationalities.copy()
        assigned_nationalities = [None] * 5
        for i in range(5):
            if len(house_possibilities[i]['Nationality']) == 1:
                nat = house_possibilities[i]['Nationality'][0]
                assigned_nationalities[i] = nat
                nationalities_left.remove(nat)
        
        for nat_perm in permutations(nationalities_left):
            nat_assignment = assigned_nationalities.copy()
            nat_index = 0
            nat_valid = True
            for i in range(5):
                if nat_assignment[i] is None:
                    nat_assignment[i] = nat_perm[nat_index]
                    nat_index += 1
                    # Check if this nationality is allowed in this house
                    if nat_assignment[i] not in house_possibilities[i]['Nationality']:
                        nat_valid = False
                        break
            if not nat_valid:
                continue
            
            # Check if all nationalities are unique
            if len(set(nat_assignment)) != 5:
                continue
            
            # Now assign vacations
            vacations_left = vacations.copy()
            assigned_vacations = [None] * 5
            for i in range(5):
                if len(house_possibilities[i]['Vacation']) == 1:
                    vac = house_possibilities[i]['Vacation'][0]
                    assigned_vacations[i] = vac
                    vacations_left.remove(vac)
            
            for vac_perm in permutations(vacations_left):
                vac_assignment = assigned_vacations.copy()
                vac_index = 0
                vac_valid = True
                for i in range(5):
                    if vac_assignment[i] is None:
                        vac_assignment[i] = vac_perm[vac_index]
                        vac_index += 1
                        # Check if this vacation is allowed in this house
                        if vac_assignment[i] not in house_possibilities[i]['Vacation']:
                            vac_valid = False
                            break
                if not vac_valid:
                    continue
                
                # Check if all vacations are unique
                if len(set(vac_assignment)) != 5:
                    continue
                
                # Now assign children
                children_left = children.copy()
                assigned_children = [None] * 5
                for i in range(5):
                    if len(house_possibilities[i]['Child']) == 1:
                        child = house_possibilities[i]['Child'][0]
                        assigned_children[i] = child
                        children_left.remove(child)
                
                for child_perm in permutations(children_left):
                    child_assignment = assigned_children.copy()
                    child_index = 0
                    child_valid = True
                    for i in range(5):
                        if child_assignment[i] is None:
                            child_assignment[i] = child_perm[child_index]
                            child_index += 1
                            # Check if this child is allowed in this house
                            if child_assignment[i] not in house_possibilities[i]['Child']:
                                child_valid = False
                                break
                    if not child_valid:
                        continue
                    
                    # Check if all children are unique
                    if len(set(child_assignment)) != 5:
                        continue
                    
                    # Now check all clues to see if this assignment works
                    # We've already applied most clues during the narrowing down,
                    # but we need to check some complex ones again
                    
                    # Clue 3: beach is directly left of Samantha
                    beach_pos = None
                    samantha_pos = None
                    for i in range(5):
                        if vac_assignment[i] == 'beach':
                            beach_pos = i
                        if child_assignment[i] == 'Samantha':
                            samantha_pos = i
                    if beach_pos is not None and samantha_pos is not None:
                        if samantha_pos != beach_pos + 1:
                            continue
                    
                    # Clue 10: one house between Fred and city
                    fred_pos = None
                    city_pos = None
                    for i in range(5):
                        if child_assignment[i] == 'Fred':
                            fred_pos = i
                        if vac_assignment[i] == 'city':
                            city_pos = i
                    if fred_pos is not None and city_pos is not None:
                        if abs(fred_pos - city_pos) != 2:
                            continue
                    
                    # If we get here, this is a valid solution
                    solution = []
                    for i in range(5):
                        solution.append([
                            str(i+1),
                            current_assignment[i],
                            vac_assignment[i],
                            child_assignment[i],
                            nat_assignment[i]
                        ])
                    
                    # Format the solution as required
                    result = {
                        "solution": {
                            "header": ["House", "Name", "Vacation", "Child", "Nationality"],
                            "rows": solution
                        }
                    }
                    return json.dumps(result, indent=2)
    
    return json.dumps({"error": "No solution found"}, indent=2)

print(solve_puzzle())