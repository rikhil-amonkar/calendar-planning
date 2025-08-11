import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    categories = {
        'House': ['1', '2', '3', '4'],
        'Name': ['Peter', 'Arnold', 'Alice', 'Eric'],
        'Flower': ['roses', 'daffodils', 'carnations', 'lilies'],
        'Hobby': ['photography', 'painting', 'cooking', 'gardening'],
        'Pet': ['dog', 'fish', 'bird', 'cat'],
        'Color': ['red', 'yellow', 'green', 'white'],
        'House Style': ['craftsman', 'colonial', 'ranch', 'victorian']
    }
    
    # Initialize all possible assignments
    from collections import defaultdict
    assignments = defaultdict(list)
    
    # Generate all possible permutations for each category
    for cat in categories:
        if cat != 'House':
            assignments[cat] = categories[cat]
    
    # Apply constraints step by step
    solution = {}
    
    # Clue 6: The person in a Craftsman-style house is in the second house.
    solution['2'] = {'House Style': 'craftsman'}
    
    # Clue 1: The person in a Craftsman-style house is Arnold.
    solution['2']['Name'] = 'Arnold'
    
    # Clue 7: Eric is the person residing in a Victorian house.
    # So Eric is in one of the houses 1,3,4 with House Style victorian
    # Clue 14: The person who has a cat is Eric.
    # So in whichever house Eric is, his pet is cat
    
    # Clue 13: The person living in a colonial-style house is the person whose favorite color is red.
    # So in some house, House Style is colonial and Color is red
    
    # Clue 5: The person who loves the rose bouquet is the person whose favorite color is red.
    # So in the same house as above, Flower is roses
    
    # Clue 2: The person who loves the rose bouquet is somewhere to the right of Peter.
    # So Peter is to the left of the house with roses
    
    # Clue 4: The person who loves a bouquet of daffodils is not in the fourth house.
    # So daffodils are in 1,2, or 3
    
    # Clue 12: The person who loves a bouquet of daffodils is the person who loves yellow.
    # So in the same house as daffodils, color is yellow
    
    # Clue 10: The person who loves white is the person who loves a carnations arrangement.
    # So in the same house, color is white and flower is carnations
    
    # Clue 8: The person with an aquarium of fish is the person who loves white.
    # So in the same house as above, pet is fish
    
    # Clue 11: The person who loves white is somewhere to the right of the person who enjoys gardening.
    # So gardening is to the left of the house with white
    
    # Clue 9: The person who loves cooking is somewhere to the right of the person whose favorite color is red.
    # So cooking is to the right of the house with red
    
    # Clue 3: The photography enthusiast is the person who owns a dog.
    # So in the same house, hobby is photography and pet is dog
    
    # Now let's try to assign step by step
    
    # House 2 has craftsman style and Arnold
    # House 2 cannot be victorian (since Eric is in victorian)
    # So Eric is in 1,3, or 4
    
    # Let's consider House 1:
    # Possible names: Peter, Alice, Eric
    # If Eric is in 1:
    if '1' not in solution:
        solution['1'] = {}
    # Let's try Eric in 1
    solution['1']['Name'] = 'Eric'
    solution['1']['House Style'] = 'victorian'  # from clue 7
    solution['1']['Pet'] = 'cat'  # from clue 14
    
    # Now, from clue 13: colonial house has color red and flower roses
    # Possible houses: 3 or 4 (since 2 is craftsman, 1 is victorian)
    
    # Let's try house 3 as colonial
    solution['3'] = {}
    solution['3']['House Style'] = 'colonial'
    solution['3']['Color'] = 'red'
    solution['3']['Flower'] = 'roses'
    
    # From clue 2: roses are right of Peter, so Peter must be left of house 3
    # So Peter is in 1 or 2
    # But 2 is Arnold, so Peter is in 1
    # But 1 is Eric, so contradiction
    # So Eric cannot be in 1
    
    # Reset house 1
    solution['1'] = {}
    
    # Try Eric in 3
    solution['3'] = {}
    solution['3']['Name'] = 'Eric'
    solution['3']['House Style'] = 'victorian'
    solution['3']['Pet'] = 'cat'
    
    # Now colonial must be in 1 or 4
    # Let's try house 1 as colonial
    solution['1']['House Style'] = 'colonial'
    solution['1']['Color'] = 'red'
    solution['1']['Flower'] = 'roses'
    
    # From clue 2: roses are right of Peter, but roses are in 1, so Peter must be left of 1, but no house left
    # Contradiction, so colonial cannot be in 1
    
    # Try colonial in 4
    solution['4'] = {}
    solution['4']['House Style'] = 'colonial'
    solution['4']['Color'] = 'red'
    solution['4']['Flower'] = 'roses'
    
    # From clue 2: roses are right of Peter, so Peter is left of 4
    # So Peter is in 1,2, or 3
    # 2 is Arnold, so Peter is in 1 or 3
    # 3 is Eric, so Peter is in 1
    solution['1']['Name'] = 'Peter'
    
    # From clue 5: roses are red, already handled
    
    # From clue 13: colonial is red, handled
    
    # From clue 12: daffodils are yellow, not in 4 (clue 4)
    # So daffodils are in 1,2, or 3
    # 1: flower not assigned yet
    # 2: flower not assigned
    # 3: flower not assigned
    
    # From clue 10: white is carnations
    # From clue 8: white is fish
    # From clue 11: white is right of gardening
    # From clue 9: cooking is right of red (red is in 4)
    # But red is in 4, so cooking must be right of 4, but no house there
    # Contradiction, so colonial cannot be in 4
    
    # So Eric cannot be in 3
    
    # Reset
    solution = {
        '2': {'House Style': 'craftsman', 'Name': 'Arnold'}
    }
    
    # Try Eric in 4
    solution['4'] = {}
    solution['4']['Name'] = 'Eric'
    solution['4']['House Style'] = 'victorian'
    solution['4']['Pet'] = 'cat'
    
    # Now colonial must be in 1 or 3
    # Try colonial in 1
    solution['1'] = {}
    solution['1']['House Style'] = 'colonial'
    solution['1']['Color'] = 'red'
    solution['1']['Flower'] = 'roses'
    
    # From clue 2: roses are right of Peter, but roses are in 1, so Peter must be left of 1 - impossible
    # Contradiction
    
    # Try colonial in 3
    solution['3'] = {}
    solution['3']['House Style'] = 'colonial'
    solution['3']['Color'] = 'red'
    solution['3']['Flower'] = 'roses'
    
    # From clue 2: roses are right of Peter, so Peter is left of 3
    # So Peter is in 1 or 2
    # 2 is Arnold, so Peter is in 1
    solution['1']['Name'] = 'Peter'
    
    # From clue 4: daffodils not in 4
    # From clue 12: daffodils are yellow
    # So daffodils are in 1,2, or 3
    # 3 has roses, so daffodils in 1 or 2
    
    # From clue 10: white is carnations
    # From clue 8: white is fish
    # From clue 11: white is right of gardening
    # So gardening is left of white
    
    # From clue 9: cooking is right of red (red is in 3)
    # So cooking is in 4
    
    solution['4']['Hobby'] = 'cooking'
    
    # From clue 3: photography is dog
    # From clue 7: Eric is in 4, pet is cat, so no dog in 4
    # So photography is in 1,2, or 3
    
    # From clue 14: Eric has cat (already in 4)
    
    # Assign hobbies: photography, painting, cooking, gardening
    # cooking is in 4
    # others in 1,2,3
    
    # From clue 11: white is right of gardening
    # So gardening is left of white
    # white must be in 2 or 3 or 4
    # 3 has color red, 4 color not assigned yet
    # So white is in 2 or 4
    # 4: color not assigned, but hobbies is cooking
    # From clue 10: white is carnations
    # From clue 8: white is fish
    # If white is in 4:
    # Then gardening is left of 4
    # 4:
    solution['4']['Color'] = 'white'
    solution['4']['Flower'] = 'carnations'
    solution['4']['Pet'] = 'fish'
    
    # From clue 11: gardening is left of white (4)
    # So gardening is in 1,2, or 3
    # 3: hobby not assigned
    # 2: hobby not assigned
    # 1: hobby not assigned
    
    # From clue 3: photography is dog
    # Possible in 1,2, or 3
    
    # From clue 12: daffodils are yellow
    # Possible in 1 or 2 (3 has roses)
    
    # Let's assign daffodils to 1
    solution['1']['Flower'] = 'daffodils'
    solution['1']['Color'] = 'yellow'
    
    # Then house 2 flower is not assigned yet: options are lilies or carnations
    # But carnations are in 4, so 2 has lilies
    solution['2']['Flower'] = 'lilies'  # Note: typo in original categories? 'lilies' vs 'lilies'
    
    # Now colors:
    # 1: yellow
    # 2: ?
    # 3: red
    # 4: white
    # So 2 must be green
    solution['2']['Color'] = 'green'
    
    # Now hobbies:
    # 4: cooking
    # From clue 11: gardening is left of white (4), so gardening is in 1,2, or 3
    # 1:
    # 2:
    # 3:
    
    # From clue 3: photography is dog
    # Assign photography to 3
    solution['3']['Hobby'] = 'photography'
    solution['3']['Pet'] = 'dog'
    
    # Then remaining hobbies: painting, gardening
    # Assign gardening to 1 (since it must be left of white)
    solution['1']['Hobby'] = 'gardening'
    
    # Then painting to 2
    solution['2']['Hobby'] = 'painting'
    
    # Now pets:
    # 1: ?
    # 2: ?
    # 3: dog
    # 4: fish
    # Remaining pets: bird, cat
    # But Eric has cat in 4, but 4 has fish, so cat must be elsewhere
    # Wait, no: clue 14 says Eric has cat, but we have pet in 4 as fish - contradiction
    
    # Oops, error: in house 4, pet is fish from clue 8, but Eric must have cat from clue 14
    # So cannot have white in 4
    
    # Reset white to 2
    solution['4']['Color'] = None
    solution['4']['Flower'] = None
    solution['4']['Pet'] = None
    
    # Assign white to 2
    solution['2']['Color'] = 'white'
    solution['2']['Flower'] = 'carnations'
    solution['2']['Pet'] = 'fish'
    
    # From clue 11: gardening is left of white (2), so gardening is in 1
    solution['1']['Hobby'] = 'gardening'
    
    # From clue 9: cooking is right of red (3), so cooking is in 4
    solution['4']['Hobby'] = 'cooking'
    
    # From clue 3: photography is dog
    # Possible in 1,3
    # 1: hobby is gardening
    # So 3:
    solution['3']['Hobby'] = 'photography'
    solution['3']['Pet'] = 'dog'
    
    # Now pets:
    # 1: ?
    # 2: fish
    # 3: dog
    # 4: ?
    # Remaining pets: bird, cat
    # Eric is in 4, must have cat
    solution['4']['Pet'] = 'cat'
    # So 1 has bird
    solution['1']['Pet'] = 'bird'
    
    # Now flowers:
    # 1: ?
    # 2: carnations
    # 3: roses
    # 4: ?
    # From clue 12: daffodils are yellow
    # Assign daffodils to 1
    solution['1']['Flower'] = 'daffodils'
    solution['1']['Color'] = 'yellow'
    
    # Then 4 has lilies
    solution['4']['Flower'] = 'lilies'
    # Color for 4: remaining is green
    solution['4']['Color'] = 'green'
    
    # Now names:
    # 1: Peter
    # 2: Arnold
    # 3: ?
    # 4: Eric
    # Remaining name: Alice
    solution['3']['Name'] = 'Alice'
    
    # Now house styles:
    # 1: ?
    # 2: craftsman
    # 3: colonial
    # 4: victorian
    # Remaining style: ranch
    solution['1']['House Style'] = 'ranch'
    
    # Verify all constraints
    # All constraints should be satisfied now
    
    # Prepare the output
    header = ['House', 'Name', 'Flower', 'Hobby', 'Pet', 'Color', 'House Style']
    rows = []
    for house in ['1', '2', '3', '4']:
        row = [house]
        for attr in header[1:]:
            row.append(solution[house].get(attr, ''))
        rows.append(row)
    
    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    
    return json.dumps(output, indent=2)

if __name__ == "__main__":
    print(solve_puzzle())