import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Bob', 'Peter', 'Eric', 'Alice', 'Arnold', 'Carol']
    hair_colors = ['auburn', 'blonde', 'brown', 'black', 'red', 'gray']
    heights = ['very tall', 'average', 'very short', 'tall', 'super tall', 'short']

    # Initialize possible assignments
    solution = None

    # Generate all possible permutations for names, hair colors, and heights
    # Since brute force is impractical, we'll use a more logical approach with constraints

    # We'll represent each house as a dictionary
    houses_data = [{'House': str(i)} for i in range(1, 7)]

    # Apply clue 2: Alice is in the fourth house
    for house in houses_data:
        if house['House'] == '4':
            house['Name'] = 'Alice'

    # Apply clue 12: gray hair is in the third house
    for house in houses_data:
        if house['House'] == '3':
            house['HairColor'] = 'gray'

    # Apply clue 6: Eric has red hair
    # So wherever Eric is, his hair is red, and vice versa

    # Apply clue 9: one house between gray (house 3) and red hair
    # So red hair is in house 5 (since gray is in 3, +2)
    for house in houses_data:
        if house['House'] == '5':
            house['HairColor'] = 'red'
            house['Name'] = 'Eric'  # From clue 6

    # Apply clue 10: very short is in the fifth house
    for house in houses_data:
        if house['House'] == '5':
            house['Height'] = 'very short'

    # Apply clue 3: Arnold is short
    # short is not in 5 (very short is there), so must be elsewhere
    # From heights: 'very tall', 'average', 'very short', 'tall', 'super tall', 'short'
    # 5 is very short, so short is elsewhere

    # Apply clue 4: tall is in the sixth house
    for house in houses_data:
        if house['House'] == '6':
            house['Height'] = 'tall'

    # Apply clue 7: super tall is right of average
    # So average is left of super tall

    # Apply clue 8: Carol has blonde hair
    # And from clue 1: person with blonde hair is directly left of Bob
    # So Carol is directly left of Bob

    # So Carol is in house X, Bob in X+1
    possible_positions_for_carol = [1, 2, 3, 4, 5]  # since Bob must be to her right

    # Also, from clue 13: blonde hair (Carol) is very tall
    # So Carol's height is very tall

    # From clue 11: Bob has brown hair
    # So in the house where name is Bob, hair is brown

    # Let's find Carol's position
    for pos in possible_positions_for_carol:
        bob_pos = pos + 1
        if bob_pos > 6:
            continue

        # Check if the positions are available for names
        # House pos has Carol, bob_pos has Bob
        # Also, house 4 is Alice, house 5 is Eric
        if pos == 4 or bob_pos == 4 or pos == 5 or bob_pos == 5:
            continue  # can't be, since 4 is Alice, 5 is Eric

        # Assign Carol and Bob
        temp_houses = [house.copy() for house in houses_data]
        temp_houses[pos - 1]['Name'] = 'Carol'
        temp_houses[pos - 1]['HairColor'] = 'blonde'
        temp_houses[pos - 1]['Height'] = 'very tall'
        temp_houses[bob_pos - 1]['Name'] = 'Bob'
        temp_houses[bob_pos - 1]['HairColor'] = 'brown'

        # Now assign remaining names: Peter, Arnold
        remaining_names = set(names) - {'Alice', 'Eric', 'Carol', 'Bob'}
        remaining_houses = [i for i in range(6) if 'Name' not in temp_houses[i]]

        # Assign Arnold (clue 3: Arnold is short)
        # short is not assigned yet (not in 5, which is very short)
        # possible heights left: average, super tall, short
        # Arnold is short
        for house_idx in remaining_houses:
            if temp_houses[house_idx]['House'] == '6':
                continue  # height is tall there
            if 'Height' not in temp_houses[house_idx]:
                temp_houses[house_idx]['Name'] = 'Arnold'
                temp_houses[house_idx]['Height'] = 'short'
                remaining_names.remove('Arnold')
                remaining_houses.remove(house_idx)
                break

        # Assign Peter to remaining house
        for house_idx in remaining_houses:
            if 'Name' not in temp_houses[house_idx]:
                temp_houses[house_idx]['Name'] = 'Peter'
                remaining_names.remove('Peter')
                break

        # Assign hair colors
        # Used so far: gray (3), red (5), blonde (Carol), brown (Bob)
        remaining_hair_colors = set(hair_colors) - {'gray', 'red', 'blonde', 'brown'}
        # black and auburn left
        # clue 5: black is not in house 4
        # Assign black to possible houses
        for house_idx in range(6):
            if 'HairColor' not in temp_houses[house_idx]:
                if temp_houses[house_idx]['House'] == '4':
                    temp_houses[house_idx]['HairColor'] = 'auburn'
                else:
                    # Can be black or auburn, but house 4 can't be black
                    # Assign black first to non-4
                    if 'black' in remaining_hair_colors:
                        temp_houses[house_idx]['HairColor'] = 'black'
                        remaining_hair_colors.remove('black')
                    else:
                        temp_houses[house_idx]['HairColor'] = 'auburn'

        # Assign heights
        # Used so far: very tall (Carol), very short (5), tall (6), short (Arnold)
        remaining_heights = set(heights) - {'very tall', 'very short', 'tall', 'short'}
        # average and super tall left
        # clue 7: super tall is right of average
        # So average must be left of super tall
        # Possible houses left for heights: 1, 2, 4 (3 has gray hair but height not assigned)
        # Assign average to leftmost possible, super tall to right
        for house_idx in range(6):
            if 'Height' not in temp_houses[house_idx]:
                if house_idx < 5 and 'average' in remaining_heights:
                    temp_houses[house_idx]['Height'] = 'average'
                    remaining_heights.remove('average')
                else:
                    temp_houses[house_idx]['Height'] = 'super tall'

        # Verify clue 7: super tall is right of average
        average_pos = None
        super_tall_pos = None
        for house_idx in range(6):
            if temp_houses[house_idx]['Height'] == 'average':
                average_pos = int(temp_houses[house_idx]['House'])
            elif temp_houses[house_idx]['Height'] == 'super tall':
                super_tall_pos = int(temp_houses[house_idx]['House'])
        if average_pos is not None and super_tall_pos is not None and average_pos >= super_tall_pos:
            continue  # invalid, skip

        # Check all constraints are satisfied
        solution = temp_houses
        break

    # Prepare the output
    output = {
        "solution": {
            "header": ["House", "Name", "HairColor", "Height"],
            "rows": []
        }
    }

    for house in solution:
        row = [
            house['House'],
            house.get('Name', ''),
            house.get('HairColor', ''),
            house.get('Height', '')
        ]
        output["solution"]["rows"].append(row)

    return json.dumps(output, indent=2)

print(solve_puzzle())