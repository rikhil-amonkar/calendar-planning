import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values
    names = ['Arnold', 'Eric', 'Bob', 'Peter', 'Alice']
    smoothies = ['desert', 'watermelon', 'lime', 'cherry', 'dragonfruit']
    nationalities = ['german', 'swede', 'norwegian', 'dane', 'brit']
    
    # Initialize houses
    houses = [1, 2, 3, 4, 5]
    
    # Apply direct clues first
    # Clue 10: Alice is in the third house
    # Clue 9: Alice is the Norwegian
    # Clue 11: Watermelon smoothie lover is in the third house
    house3_name = 'Alice'
    house3_nationality = 'norwegian'
    house3_smoothie = 'watermelon'
    
    # Clue 8: Bob is the Dane
    # Clue 2: Dragonfruit smoothie lover is in the second house
    house2_smoothie = 'dragonfruit'
    
    # Clue 1: Dragonfruit is left of Eric (so Eric is to the right of house 2)
    
    # Clue 7: Two houses between lime drinker and dane (bob)
    # So if lime is in X, dane is in X+3 or X-3
    # Possible positions for lime: 1 or 2 (since 3 is watermelon, 4+3>5)
    # But house 2 is dragonfruit, so lime must be in 1, dane in 4
    house1_smoothie = 'lime'
    house4_nationality = 'dane'
    house4_name = 'Bob'  # from clue 8
    
    # Clue 4: Dane and brit are next to each other
    # So brit is in 3 or 5 (since dane is in 4)
    # But house3 is norwegian, so brit must be in 5
    house5_nationality = 'brit'
    
    # Clue 6: Swedish person is left of dragonfruit (house 2)
    # So swede is in house 1
    house1_nationality = 'swede'
    
    # Now assign nationalities: we have assigned swede, norwegian, dane, brit
    # Remaining is german, which must be in house 2
    house2_nationality = 'german'
    
    # Names left: Arnold, Eric, Peter (since Alice is in 3, Bob in 4)
    # Clue 3: Peter is not in first house
    # So house1 name is Arnold or Eric
    # But from clue 1: dragonfruit is left of Eric, so Eric must be to the right of house 2
    # So Eric is in 3,4, or 5
    # But 3 is Alice, 4 is Bob, so Eric is in 5
    house5_name = 'Eric'
    
    # So house1 name is Arnold or Peter, but Peter is not in first (clue 3), so Arnold
    house1_name = 'Arnold'
    # Then Peter is in 2
    house2_name = 'Peter'
    
    # Smoothies left: desert, cherry (lime in 1, dragonfruit in 2, watermelon in 3)
    # Clue 5: desert is not in 5
    # So desert is in 4, cherry in 5
    house4_smoothie = 'desert'
    house5_smoothie = 'cherry'
    
    # Compile the solution
    solution = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "Nationality"],
            "rows": [
                ["1", house1_name, house1_smoothie, house1_nationality],
                ["2", house2_name, house2_smoothie, house2_nationality],
                ["3", house3_name, house3_smoothie, house3_nationality],
                ["4", house4_name, house4_smoothie, house4_nationality],
                ["5", house5_name, house5_smoothie, house5_nationality]
            ]
        }
    }
    
    return json.dumps(solution)

print(solve_puzzle())