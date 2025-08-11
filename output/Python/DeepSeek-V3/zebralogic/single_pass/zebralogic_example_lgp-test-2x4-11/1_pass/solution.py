import json
from itertools import permutations

def solve_puzzle():
    # Define the attributes and their possible values
    attributes = {
        'House': ['1', '2'],
        'Name': ['Eric', 'Arnold'],
        'Hobby': ['gardening', 'photography'],
        'Pet': ['cat', 'dog'],
        'Height': ['short', 'very short']
    }
    
    # Generate all possible permutations for each attribute
    # Since there are only 2 houses, we can pair them directly
    solutions = []
    
    # Iterate through all possible name assignments
    for names in permutations(attributes['Name']):
        # Check if Eric is very short (clue 2)
        eric_index = names.index('Eric')
        heights = [None, None]
        heights[eric_index] = 'very short'
        other_height_index = 1 - eric_index
        heights[other_height_index] = 'short'
        
        # Assign hobbies based on clue 1 (very short person is photography)
        hobbies = [None, None]
        hobbies[eric_index] = 'photography'
        hobbies[other_height_index] = 'gardening'
        
        # Assign pets based on clue 3 (cat is to the right of very short person)
        pets = [None, None]
        if eric_index == 0:  # Eric is in house 1, cat must be to the right (house 2)
            pets[0] = 'dog'
            pets[1] = 'cat'
        else:  # Eric is in house 2, cat cannot be to the right (no house 3), so this is invalid
            continue
        
        # Construct the solution
        solution = {
            'header': ['House', 'Name', 'Hobby', 'Pet', 'Height'],
            'rows': [
                ['1', names[0], hobbies[0], pets[0], heights[0]],
                ['2', names[1], hobbies[1], pets[1], heights[1]]
            ]
        }
        
        # Verify all constraints are met (though they should be by construction)
        # Clue 1: very short person is photography
        assert hobbies[eric_index] == 'photography'
        # Clue 2: Eric is very short (already enforced)
        # Clue 3: cat is to the right of very short person
        if 'cat' in pets:
            cat_house = pets.index('cat') + 1
            very_short_house = heights.index('very short') + 1
            assert cat_house > very_short_house
        
        solutions.append(solution)
    
    # Since the puzzle should have a unique solution, return the first one
    return solutions[0] if solutions else None

solution = solve_puzzle()
print(json.dumps({"solution": solution}, indent=2))