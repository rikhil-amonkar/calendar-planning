import json
from itertools import permutations

def solve_puzzle():
    names = ['Peter', 'Alice', 'Bob', 'Eric', 'Arnold']
    heights = ['very tall', 'average', 'tall', 'very short', 'short']
    
    # We'll represent each house as a dictionary with position 1-5
    houses = [{'House': str(i+1)} for i in range(5)]
    
    # Apply clue 7: average height is in house 5
    for height in heights:
        if height == 'average':
            houses[4]['Height'] = height
            heights.remove(height)
            break
    
    # Apply clue 1: short is in house 2
    for height in heights:
        if height == 'short':
            houses[1]['Height'] = height
            heights.remove(height)
            break
    
    # Apply clue 6: short and very short are next to each other
    # short is in house 2, so very short must be in house 1 or 3
    if 'very short' in heights:
        if 1 in [0, 2]:  # house indices are 0-4
            possible_positions = [0, 2]  # house 1 or 3
        else:
            possible_positions = [0, 2]
    
    # Apply clue 4: very tall is directly left of Peter
    # So very tall is in house X, Peter in X+1
    # Apply clue 2: Peter is directly left of Bob
    # So Peter in Y, Bob in Y+1
    # Therefore: very tall in X, Peter in X+1, Bob in X+2
    
    # Apply clue 3: Eric is left of Peter
    # So Eric is in any house left of Peter
    
    # Apply clue 5: Alice is directly left of average height
    # average is in house 5, so Alice is in house 4
    
    # Assign Alice to house 4
    for name in names:
        if name == 'Alice':
            houses[3]['Name'] = name
            names.remove(name)
            break
    
    # Now, Peter must be left of Bob, and very tall is left of Peter
    # Possible positions for Peter and Bob:
    # Peter can be in 1,2,3; Bob in 2,3,4
    # But very tall is left of Peter, so Peter can't be in 1
    # Also, Alice is in 4, so Bob can't be in 4 (since names are unique)
    # So Peter must be in 2 or 3, Bob in 3 or 4
    # But Alice is in 4, so Bob can't be in 4, so Bob must be in 3, Peter in 2
    
    # Assign Peter to house 2, Bob to house 3
    for name in names:
        if name == 'Peter':
            houses[1]['Name'] = name
            names.remove(name)
            break
    for name in names:
        if name == 'Bob':
            houses[2]['Name'] = name
            names.remove(name)
            break
    
    # Now, very tall is directly left of Peter (house 2), so very tall is in house 1
    for height in heights:
        if height == 'very tall':
            houses[0]['Height'] = height
            heights.remove(height)
            break
    
    # From clue 6: short (house 2) and very short are next to each other
    # So very short must be in house 1 or 3
    # house 1 has height very tall, so very short must be in house 3
    if 'very short' in heights:
        houses[2]['Height'] = 'very short'
        heights.remove('very short')
    
    # Remaining height is tall, which must be in house 3 or 4
    # house 3 is very short, house 4's height is not assigned yet
    # but average is in 5, very tall in 1, short in 2, very short in 3
    # so tall must be in 4
    if 'tall' in heights:
        houses[3]['Height'] = 'tall'
        heights.remove('tall')
    
    # Now assign names: remaining names are Eric and Arnold
    # From clue 3: Eric is left of Peter (house 2)
    # So Eric must be in house 1
    for name in names:
        if name == 'Eric':
            houses[0]['Name'] = name
            names.remove(name)
            break
    # Arnold is the only name left, must be in house 4 or 5
    # Alice is in 4, so Arnold is in 5
    for name in names:
        if name == 'Arnold':
            houses[4]['Name'] = name
            names.remove(name)
            break
    
    # Prepare the output
    solution = {
        "solution": {
            "header": ["House", "Name", "Height"],
            "rows": []
        }
    }
    
    for house in houses:
        row = [house['House'], house.get('Name', ''), house.get('Height', '')]
        solution["solution"]["rows"].append(row)
    
    return json.dumps(solution)

print(solve_puzzle())