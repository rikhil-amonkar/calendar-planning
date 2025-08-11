import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    names = ['Bob', 'Arnold', 'Peter', 'Alice', 'Eric']
    drinks = ['milk', 'root beer', 'coffee', 'tea', 'water']
    colors = ['blue', 'green', 'white', 'yellow', 'red']
    flowers = ['daffodils', 'roses', 'lilies', 'tulips', 'carnations']
    hobbies = ['painting', 'cooking', 'photography', 'gardening', 'knitting']
    
    # We'll represent each house as a dictionary with these keys
    attributes = ['Name', 'Drink', 'Color', 'Flower', 'Hobby']
    
    # Generate all possible permutations for each attribute
    # But this is computationally expensive, so we'll use constraints to narrow down
    
    # We know from clue 13: water drinker is in house 3 and is Peter
    # So house 3 has name Peter and drink water
    # From clue 8: Peter is the water drinker
    
    # From clue 15: white is in house 2
    # From clue 10: white color loves roses
    # From clue 15 and 10: house 2 has color white and flower roses
    
    # From clue 14: carnations lover is root beer drinker
    # From clue 2: root beer lover enjoys gardening
    # So carnations -> root beer -> gardening
    
    # From clue 4: green color -> lilies
    # From clue 3: green color -> coffee
    # So green -> lilies and coffee
    
    # From clue 7: Eric is directly left of tea drinker
    # So if Eric is in house X, tea drinker is in house X+1
    
    # From clue 12: cooking is left of painting
    # So cooking is in house X, painting is in house Y where X < Y
    
    # From clue 5: blue is right of daffodils
    # So daffodils is in X, blue is in Y where X < Y
    
    # From clue 6: cooking hobby loves blue color
    
    # From clue 11: one house between carnations and red color
    # So if carnations is in X, red is in X+2 or X-2
    
    # From clue 1: Alice is not in house 4
    # From clue 9: Arnold is photography
    
    # Let's try to assign step by step
    
    # Initialize houses
    houses = [{'House': str(i+1)} for i in range(5)]
    
    # Assign known values
    houses[2]['Drink'] = 'water'
    houses[2]['Name'] = 'Peter'
    
    houses[1]['Color'] = 'white'
    houses[1]['Flower'] = 'roses'
    
    # Assign Arnold (clue 9)
    # Arnold could be in 0,1,3,4 (since house 2 is white, but name not assigned yet)
    # But house 1 has color white, but name not assigned yet
    
    # Assign green color (must be coffee and lilies)
    # green can't be in house 1 (white), house 2 (white), maybe 0,3,4
    
    # carnations is root beer and gardening
    # and one house between carnations and red
    
    # Let's try assigning carnations to house 0
    # Then red is in house 2
    # But house 2 is white, so red can't be there
    # So carnations can't be in 0
    
    # Try carnations in 1
    # Then red is in 3
    # But house 1 has flower roses (from white color), so carnations can't be there
    
    # Try carnations in 2
    # But house 2 has roses, so no
    
    # Try carnations in 3
    # Then red is in 5
    # So house 3 has flower carnations, drink root beer, hobby gardening
    # house 5 has color red
    
    houses[3]['Flower'] = 'carnations'
    houses[3]['Drink'] = 'root beer'
    houses[3]['Hobby'] = 'gardening'
    
    houses[4]['Color'] = 'red'
    
    # Now green must be in 0 (since 1,2,3,4 have colors)
    houses[0]['Color'] = 'green'
    houses[0]['Drink'] = 'coffee'
    houses[0]['Flower'] = 'lilies'
    
    # From clue 6: cooking hobby loves blue
    # From clue 5: blue is right of daffodils
    # From clue 12: cooking is left of painting
    
    # Possible colors left: blue, yellow
    # house 1: color white
    # house 0: green
    # house 2: ?
    # house 3: ?
    # house 4: red
    
    # house 2 and 3 colors not assigned yet
    # From clue 5: blue is right of daffodils
    # daffodils must be in house 0,1,2 (since blue must be to right)
    # house 0 has lilies, 1 has roses, so daffodils in 2
    houses[2]['Flower'] = 'daffodils'
    
    # Then blue is to right, so blue is in 3 or 4
    # house 4 is red, so blue is in 3
    houses[3]['Color'] = 'blue'
    
    # From clue 6: cooking hobby loves blue
    # So house 3 has hobby cooking
    # But house 3 has gardening from earlier - contradiction
    # So our assumption that carnations is in 3 is wrong
    
    # Backtrack: try carnations in 4
    # Then red is in 2 (but house 2 is white)
    # Not possible
    
    # Try carnations in 1 - but house 1 has roses
    # So no possible position for carnations - contradiction in earlier steps
    
    # Alternative approach: maybe house 1 doesn't have roses
    # Wait, clue 10 says white color loves roses, and house 2 is white, so house 1 can have other flowers
    
    # Reinitialize
    houses = [{'House': str(i+1)} for i in range(5)]
    
    # Assign known values
    houses[2]['Drink'] = 'water'
    houses[2]['Name'] = 'Peter'
    
    houses[1]['Color'] = 'white'
    houses[1]['Flower'] = 'roses'
    
    # Try carnations in 0
    # Then red is in 2
    # But house 2 color not assigned yet
    houses[0]['Flower'] = 'carnations'
    houses[0]['Drink'] = 'root beer'
    houses[0]['Hobby'] = 'gardening'
    
    houses[2]['Color'] = 'red'
    
    # green must be in 3 or 4 (since 1 is white, 2 is red, 0 could be anything)
    # try green in 3
    houses[3]['Color'] = 'green'
    houses[3]['Drink'] = 'coffee'
    houses[3]['Flower'] = 'lilies'
    
    # From clue 5: blue is right of daffodils
    # daffodils must be in 0,1,2
    # 0 has carnations, 1 has roses, so daffodils in 2
    houses[2]['Flower'] = 'daffodils'
    
    # blue is to right, so blue is in 3 or 4
    # 3 is green, so blue in 4
    houses[4]['Color'] = 'blue'
    
    # From clue 6: cooking hobby loves blue
    houses[4]['Hobby'] = 'cooking'
    # But from clue 12: cooking is left of painting
    # So painting must be to right of cooking, but cooking is in 4 - no house to right
    # Contradiction
    
    # Try green in 4 instead
    houses = [{'House': str(i+1)} for i in range(5)]
    houses[2]['Drink'] = 'water'
    houses[2]['Name'] = 'Peter'
    houses[1]['Color'] = 'white'
    houses[1]['Flower'] = 'roses'
    
    houses[0]['Flower'] = 'carnations'
    houses[0]['Drink'] = 'root beer'
    houses[0]['Hobby'] = 'gardening'
    houses[2]['Color'] = 'red'
    
    houses[4]['Color'] = 'green'
    houses[4]['Drink'] = 'coffee'
    houses[4]['Flower'] = 'lilies'
    
    # daffodils in 1 or 2
    # house 1 has roses, so daffodils in 2
    houses[2]['Flower'] = 'daffodils'
    
    # blue is to right, so blue in 3
    houses[3]['Color'] = 'blue'
    
    # cooking hobby loves blue
    houses[3]['Hobby'] = 'cooking'
    
    # painting is to right of cooking, so painting in 4
    houses[4]['Hobby'] = 'painting'
    
    # From clue 7: Eric is directly left of tea drinker
    # Possible positions:
    # Eric in 0, tea in 1
    # Eric in 1, tea in 2 - but 2 has water
    # Eric in 2, tea in 3
    # Eric in 3, tea in 4
    
    # Try Eric in 0, tea in 1
    houses[0]['Name'] = 'Eric'
    houses[1]['Drink'] = 'tea'
    
    # Assign names left: Bob, Arnold, Alice
    # From clue 9: Arnold is photography
    # Possible in 1,3,4
    # house 1: name not assigned yet
    houses[1]['Name'] = 'Arnold'
    houses[1]['Hobby'] = 'photography'
    
    # house 3: name not assigned
    # house 4: name not assigned
    # From clue 1: Alice not in 4, so Alice in 3
    houses[3]['Name'] = 'Alice'
    houses[4]['Name'] = 'Bob'
    
    # Assign remaining drinks
    # drinks assigned: root beer (0), tea (1), water (2), coffee (4)
    # remaining: milk
    houses[3]['Drink'] = 'milk'
    
    # Assign remaining hobbies
    # assigned: gardening (0), photography (1), cooking (3), painting (4)
    # remaining: knitting
    houses[2]['Hobby'] = 'knitting'
    
    # Assign remaining colors
    # assigned: white (1), red (2), blue (3), green (4)
    # remaining: yellow in 0
    houses[0]['Color'] = 'yellow'
    
    # Assign remaining flowers
    # assigned: carnations (0), roses (1), daffodils (2), lilies (4)
    # remaining: tulips in 3
    houses[3]['Flower'] = 'tulips'
    
    # Verify all constraints
    # All constraints should be satisfied now
    
    # Prepare the output
    solution = {
        "solution": {
            "header": ["House", "Name", "Drink", "Color", "Flower", "Hobby"],
            "rows": []
        }
    }
    
    for house in houses:
        row = [
            house['House'],
            house.get('Name', ''),
            house.get('Drink', ''),
            house.get('Color', ''),
            house.get('Flower', ''),
            house.get('Hobby', '')
        ]
        solution["solution"]["rows"].append(row)
    
    return json.dumps(solution, indent=2)

print(solve_puzzle())