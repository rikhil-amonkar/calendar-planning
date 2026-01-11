import json

def is_valid(houses):
    # Constraint 2: The person who smokes Blue Master is in the fifth house.
    if houses[4]['cigar'] == 'blue master':
        pass
    else:
        return False
    
    # Constraint 5: The person partial to Pall Mall is in the third house.
    if houses[2]['cigar'] == 'pall mall':
        pass
    else:
        return False
    
    # Constraint 6: Eric is in the sixth house.
    if houses[5]['name'] == 'eric':
        pass
    else:
        return False
    
    # Constraint 8: Peter is in the first house.
    if houses[0]['name'] == 'peter':
        pass
    else:
        return False
    
    # Constraint 9: Bob is in the third house.
    if houses[2]['name'] == 'bob':
        pass
    else:
        return False
    
    # Find indices of specific people and cigars
    arnold_index = next((i for i, house in enumerate(houses) if house['name'] == 'arnold'), None)
    prince_index = next((i for i, house in enumerate(houses) if house['cigar'] == 'prince'), None)
    yellow_monster_index = next((i for i, house in enumerate(houses) if house['cigar'] == 'yellow monster'), None)
    blends_index = next((i for i, house in enumerate(houses) if house['cigar'] == 'blends'), None)
    
    # Constraint 1: Arnold is somewhere to the left of the person who smokes many unique blends.
    if arnold_index is not None and blends_index is not None and arnold_index < blends_index:
        pass
    else:
        return False
    
    # Constraint 3: Arnold is somewhere to the left of the Prince smoker.
    if arnold_index is not None and prince_index is not None and arnold_index < prince_index:
        pass
    else:
        return False
    
    # Constraint 4: There is one house between the person who smokes Yellow Monster and the person who smokes many unique blends.
    if yellow_monster_index is not None and blends_index is not None and abs(yellow_monster_index - blends_index) == 2:
        pass
    else:
        return False
    
    # Constraint 7: Carol and Eric are next to each other.
    carol_index = next((i for i, house in enumerate(houses) if house['name'] == 'carol'), None)
    eric_index = next((i for i, house in enumerate(houses) if house['name'] == 'eric'), None)
    if carol_index is not None and eric_index is not None and abs(carol_index - eric_index) == 1:
        pass
    else:
        return False
    
    return True

def solve(houses, names, cigars):
    if len(names) == 0:
        if is_valid(houses):
            return houses
        else:
            return None
    
    for i in range(len(houses)):
        if houses[i]['name'] is None and houses[i]['cigar'] is None:
            for name in names:
                for cigar in cigars:
                    houses[i]['name'] = name
                    houses[i]['cigar'] = cigar
                    remaining_names = [n for n in names if n != name]
                    remaining_cigars = [c for c in cigars if c != cigar]
                    result = solve(houses, remaining_names, remaining_cigars)
                    if result is not None:
                        return result
                    houses[i]['name'] = None
                    houses[i]['cigar'] = None
    return None

# Initialize the houses
houses = [{'house': i+1, 'name': None, 'cigar': None} for i in range(6)]

# Define the names and cigars
names = ['carol', 'peter', 'eric', 'arnold', 'alice', 'bob']
cigars = ['blends', 'yellow monster', 'pall mall', 'blue master', 'dunhill', 'prince']

# Solve the puzzle
solution = solve(houses, names, cigars)

# Format the solution as JSON
json_solution = {
    "solution": {
        "header": ["House", "Name", "Cigar"],
        "rows": [[str(house['house']), house['name'], house['cigar']] for house in solution]
    }
}

print(json.dumps(json_solution, indent=2))