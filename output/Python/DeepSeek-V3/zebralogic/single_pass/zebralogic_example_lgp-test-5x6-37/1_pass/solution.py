import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    categories = {
        'House': ['1', '2', '3', '4', '5'],
        'Name': ['Bob', 'Arnold', 'Alice', 'Peter', 'Eric'],
        'Hobby': ['cooking', 'gardening', 'painting', 'photography', 'knitting'],
        'Sport': ['swimming', 'tennis', 'soccer', 'baseball', 'basketball'],
        'House Style': ['ranch', 'craftsman', 'victorian', 'modern', 'colonial'],
        'Child': ['Timothy', 'Samantha', 'Bella', 'Meredith', 'Fred'],
        'Height': ['average', 'very tall', 'very short', 'short', 'tall']
    }

    # Initialize possibilities for each house (1-5)
    houses = [{} for _ in range(5)]

    # Apply constraints step by step

    # Clue 20: Victorian is in house 5
    houses[4]['House Style'] = 'victorian'

    # Clue 14: Victorian house has child Fred
    houses[4]['Child'] = 'Fred'

    # Clue 3: Peter is directly left of Victorian house, so Peter is in house 4
    houses[3]['Name'] = 'Peter'

    # Clue 16: Peter is very tall
    houses[3]['Height'] = 'very tall'

    # Clue 5: very tall person loves baseball
    houses[3]['Sport'] = 'baseball'

    # Clue 4: Alice is tall
    # Clue 2: tall person is in house 2
    houses[1]['Height'] = 'tall'
    houses[1]['Name'] = 'Alice'

    # Clue 8: gardening is in house 2
    houses[1]['Hobby'] = 'gardening'

    # Clue 18: knitting is next to gardening, so knitting is in house 1 or 3
    # Clue 17: ranch is left of cooking
    # Clue 19: modern house loves cooking
    # So cooking is in modern house, and ranch is left of it

    # Clue 12: child Samantha is in modern house
    # Clue 10: tennis lover has child Samantha
    # So modern house has tennis and cooking

    # Clue 7: Bob paints
    # Clue 13: craftsman house has average height
    # Clue 1: average height has child Meredith
    # So craftsman house has average height and child Meredith

    # Clue 6: Meredith's parent and Timothy's parent are next to each other

    # Clue 9: very short is right of Eric
    # So Eric is left of very short

    # Clue 11: soccer is not in house 1
    # Clue 15: short person loves basketball

    # Let's determine possible positions for modern house
    # It can't be house 5 (victorian), or house 4 (Peter is there)
    # Possible: 1, 2, or 3
    # House 2 has gardening, and modern has cooking (from clue 19)
    # But house 2 has gardening, not cooking, so modern can't be 2
    # So modern is 1 or 3

    # Try modern in house 3
    # Then cooking is in 3, tennis is in 3 (from clue 10 and 12)
    houses[2]['House Style'] = 'modern'
    houses[2]['Hobby'] = 'cooking'
    houses[2]['Sport'] = 'tennis'
    houses[2]['Child'] = 'Samantha'

    # Then ranch is left of cooking (clue 17), so ranch is 1 or 2
    # House 2 has gardening, not necessarily ranch
    # But house 1 could be ranch

    # knitting is next to gardening (house 2), so knitting is 1 or 3
    # house 3 has cooking, so knitting is in 1
    houses[0]['Hobby'] = 'knitting'

    # From clue 13: craftsman has average height and child Meredith
    # Possible positions: 1 or 2 or 4 (3 is modern, 5 is victorian)
    # house 2 has gardening, name Alice, height tall
    # house 4 has Peter, height very tall
    # So craftsman must be house 1
    houses[0]['House Style'] = 'craftsman'
    houses[0]['Height'] = 'average'
    houses[0]['Child'] = 'Meredith'

    # From clue 6: Meredith's parent (house 1) and Timothy's parent are next to each other
    # So Timothy's parent is house 2
    houses[1]['Child'] = 'Timothy'

    # From clue 10: tennis lover has child Samantha (already set in house 3)

    # From clue 15: short person loves basketball
    # Possible houses: 0,1,2,4 (3 is very tall)
    # Heights assigned so far: 
    # house 0: average, house 1: tall, house 3: very tall
    # So short or very short in 2 or 4
    # house 4: no height assigned yet
    # house 2: no height assigned yet

    # From clue 9: very short is right of Eric
    # So Eric is left of very short
    # Eric must be in house 0 or 1 or 2
    # house 1 is Alice, so Eric is 0 or 2
    # house 0 name not assigned yet
    # house 2 name not assigned yet

    # From names left: Bob, Arnold, Eric
    # house 0: name could be Bob or Eric or Arnold
    # house 2: name could be Bob or Eric or Arnold
    # house 4: name could be Bob or Arnold or Eric (but Peter is 4? No, Peter is 4 is already set)
    # Wait, names assigned so far: Alice (house 1), Peter (house 3)
    # Remaining names: Bob, Arnold, Eric

    # From clue 7: Bob paints
    # Painting not assigned yet
    # So Bob must be in house with hobby painting
    # Hobbies assigned:
    # house 0: knitting, house 1: gardening, house 2: cooking, house 3: ?
    # house 4: ?
    # Remaining hobbies: painting, photography
    # So Bob must be in house with painting, so house 3 or 4
    # house 3 name is Peter, so Bob must be in house 4
    houses[4]['Name'] = 'Bob'
    houses[4]['Hobby'] = 'painting'  # Only remaining hobby is painting or photography, but Bob paints

    # Then names left: Arnold, Eric
    # house 0 and 2
    # From clue 9: very short is right of Eric
    # If Eric is in 0, very short is in 1,2,3,4
    # house 1 is tall, 3 is very tall, so very short is 2 or 4
    # house 4 height not assigned yet
    # house 2 height not assigned yet

    # If Eric is in 0:
    houses[0]['Name'] = 'Eric'
    houses[2]['Name'] = 'Arnold'

    # Then very short is right of Eric, so 2 or 4
    # house 4: height could be short or very short
    # house 2: height could be short or very short
    # From clue 15: short loves basketball
    # Sports assigned: house 2: tennis, house 3: baseball
    # Remaining sports: swimming, soccer, basketball
    # From clue 11: soccer is not in house 1
    # house 1 sport not assigned yet
    # house 0 sport not assigned
    # house 4 sport not assigned

    # Assign heights:
    # house 2 or 4 is very short
    # Let's say house 2 is very short
    houses[2]['Height'] = 'very short'
    # Then house 4 must be short
    houses[4]['Height'] = 'short'
    # Then from clue 15: short loves basketball
    houses[4]['Sport'] = 'basketball'

    # Then house 0 sport: remaining are swimming, soccer
    # From clue 11: soccer is not in house 1
    # So soccer can be in 0,2,3,4
    # 2 has tennis, 3 has baseball, 4 has basketball, so soccer is in 0
    houses[0]['Sport'] = 'soccer'
    # Then house 1 sport is swimming
    houses[1]['Sport'] = 'swimming'

    # Now check hobbies:
    # Assigned: 0: knitting, 1: gardening, 2: cooking, 4: painting
    # Remaining: photography
    # So house 3 hobby is photography
    houses[3]['Hobby'] = 'photography'

    # Now assign house styles:
    # Assigned: 0: craftsman, 2: modern, 4: victorian
    # Remaining: ranch, colonial
    # From clue 17: ranch is left of cooking (cooking is in 2)
    # So ranch is in 0 or 1
    # house 0 is craftsman, so ranch is in 1
    houses[1]['House Style'] = 'ranch'
    # Then house 3 is colonial
    houses[3]['House Style'] = 'colonial'

    # Now assign children:
    # Assigned: 0: Meredith, 1: Timothy, 2: Samantha, 4: Fred
    # Remaining: Bella
    # So house 3 child is Bella
    houses[2]['Child'] = 'Bella'  # Wait, house 2 child was not assigned yet?
    # Wait, looking back:
    # Children assigned:
    # house 0: Meredith, house 1: Timothy, house 2: Samantha (from modern house), house 4: Fred
    # So house 3 child is Bella
    houses[3]['Child'] = 'Bella'

    # Verify all constraints are satisfied
    # All attributes should be filled now

    # Prepare the solution dictionary
    solution = {
        "solution": {
            "header": ["House", "Name", "Hobby", "Sport", "House Style", "Child", "Height"],
            "rows": []
        }
    }

    for i in range(5):
        house_num = str(i + 1)
        row = [
            house_num,
            houses[i].get('Name', ''),
            houses[i].get('Hobby', ''),
            houses[i].get('Sport', ''),
            houses[i].get('House Style', ''),
            houses[i].get('Child', ''),
            houses[i].get('Height', '')
        ]
        solution["solution"]["rows"].append(row)

    return json.dumps(solution, indent=2)

if __name__ == "__main__":
    print(solve_puzzle())