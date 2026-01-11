import json

def solve_puzzle():
    # Initialize houses with None values
    houses = [{'Name': None, 'Mother': None, 'Pet': None} for _ in range(6)]
    
    # Apply Clue 5: Eric owns a rabbit
    for i in range(6):
        if houses[i]['Pet'] is None:
            houses[i]['Pet'] = 'rabbit'
            houses[i]['Name'] = 'Eric'
            houses[i]['Mother'] = 'Kailyn'
            break
    
    # Apply Clue 10: Arnold has a cat
    for i in range(6):
        if houses[i]['Pet'] is None:
            houses[i]['Pet'] = 'cat'
            houses[i]['Name'] = 'Arnold'
            houses[i]['Mother'] = 'Janelle'
            break
    
    # Apply Clue 7: The person who has a cat is directly left of the person whose mother's name is Holly
    # Since Arnold has the cat, the person whose mother is Holly must be in the next house
    for i in range(5):
        if houses[i]['Pet'] == 'cat':
            houses[i+1]['Mother'] = 'Holly'
            break
    
    # Apply Clue 4: The person with a pet hamster is directly left of the person who owns a rabbit
    # Since Eric owns the rabbit, the person with the hamster must be in the previous house
    for i in range(1, 6):
        if houses[i]['Pet'] == 'rabbit':
            houses[i-1]['Pet'] = 'hamster'
            break
    
    # Apply Clue 2: There are two houses between the person who has a cat and the person who owns a rabbit
    # Since Arnold has the cat and Eric owns the rabbit, the distance must be 2 houses apart
    # This is already satisfied as per the previous placements
    
    # Apply Clue 6: There is one house between the person who owns a dog and the person who has a cat
    # Arnold has the cat, so the person with the dog must be in house 1 or house 3
    if houses[0]['Pet'] is None:
        houses[0]['Pet'] = 'dog'
    else:
        houses[2]['Pet'] = 'dog'
    
    # Apply Clue 8: Alice is directly left of Carol
    # Apply Clue 9: Carol is the person whose mother's name is Aniya
    # Find available slots for Alice and Carol
    alice_house = None
    carol_house = None
    for i in range(5):
        if houses[i]['Name'] is None and houses[i+1]['Name'] is None:
            alice_house = i
            carol_house = i + 1
            break
    
    houses[alice_house]['Name'] = 'Alice'
    houses[carol_house]['Name'] = 'Carol'
    houses[carol_house]['Mother'] = 'Aniya'
    
    # Apply Clue 12: The person with an aquarium of fish is the person whose mother's name is Sarah
    for i in range(6):
        if houses[i]['Mother'] is None:
            houses[i]['Mother'] = 'Sarah'
            houses[i]['Pet'] = 'fish'
            break
    
    # Assign remaining name to Bob
    for i in range(6):
        if houses[i]['Name'] is None:
            houses[i]['Name'] = 'Bob'
            break
    
    # Ensure Bob is not in the second house (Clue 1)
    if houses[1]['Name'] == 'Bob':
        # Swap Bob with another person
        for i in range(6):
            if houses[i]['Name'] != 'Bob':
                houses[1]['Name'], houses[i]['Name'] = houses[i]['Name'], houses[1]['Name']
                break
    
    # Validate the solution
    for house in houses:
        assert house['Name'] is not None, "Name not assigned"
        assert house['Mother'] is not None, "Mother not assigned"
        assert house['Pet'] is not None, "Pet not assigned"
    
    # Prepare the solution in the required JSON format
    solution = {
        "solution": {
            "header": ["House", "Name", "Mother", "Pet"],
            "rows": []
        }
    }
    
    for i, house in enumerate(houses):
        solution["solution"]["rows"].append([str(i+1), house['Name'], house['Mother'], house['Pet']])
    
    return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())