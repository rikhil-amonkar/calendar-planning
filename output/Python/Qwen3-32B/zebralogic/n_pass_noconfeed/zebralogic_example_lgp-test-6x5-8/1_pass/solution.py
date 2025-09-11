import json

def solve_puzzle():
    # Define all possible values
    names = ['Arnold', 'Peter', 'Bob', 'Eric', 'Carol', 'Alice']
    animals = ['horse', 'rabbit', 'fish', 'cat', 'bird', 'dog']
    occupations = ['engineer', 'nurse', 'lawyer', 'teacher', 'artist', 'doctor']
    favorite_sports = ['basketball', 'volleyball', 'soccer', 'tennis', 'baseball', 'swimming']
    heights = ['average', 'tall', 'short', 'very short', 'very tall', 'super tall']
    
    # Initialize houses with None
    houses = [{'name': None, 'animal': None, 'occupation': None, 'favorite_sport': None, 'height': None} for _ in range(6)]
    
    # Apply fixed clues
    houses[0]['favorite_sport'] = 'baseball'  # House 1
    houses[4]['occupation'] = 'lawyer'        # House 5
    houses[4]['height'] = 'super tall'        # House 5
    
    # Carol is in House 5 (index 4)
    houses[4]['favorite_sport'] = 'soccer'
    houses[4]['animal'] = 'fish'
    
    # Teacher is in House 4 (index 3)
    houses[3]['occupation'] = 'teacher'
    houses[3]['animal'] = 'horse'
    houses[3]['favorite_sport'] = 'tennis'
    
    # Engineer is in House 2 (index 1)
    houses[1]['occupation'] = 'engineer'
    houses[1]['animal'] = 'dog'
    
    # Alice is in House 3 (index 2)
    houses[2]['animal'] = 'rabbit'
    houses[1]['height'] = 'average'           # Average height is in House 2
    houses[1]['favorite_sport'] = 'swimming'  # Average height loves swimming
    
    # Arnold is in House 6 (index 5)
    houses[5]['animal'] = 'cat'
    houses[5]['name'] = 'Arnold'
    
    # Peter is in House 1 (index 0)
    houses[0]['name'] = 'Peter'
    houses[0]['occupation'] = 'nurse'
    
    # Eric is in House 2 (index 1)
    houses[1]['name'] = 'Eric'
    
    # Bob is in House 4 (index 3)
    houses[3]['name'] = 'Bob'
    
    # Alice is in House 3 (index 2)
    houses[2]['name'] = 'Alice'
    
    # Carol is in House 5 (index 4)
    houses[4]['name'] = 'Carol'
    
    # Fill in remaining attributes
    houses[0]['animal'] = 'bird'
    houses[2]['favorite_sport'] = 'volleyball'
    houses[5]['favorite_sport'] = 'basketball'
    houses[0]['height'] = 'very tall'
    houses[2]['height'] = 'tall'
    houses[3]['height'] = 'very short'
    houses[5]['height'] = 'short'
    
    # Build solution dictionary
    solution = {
        "solution": {
            "header": ["House", "Name", "Animal", "Occupation", "FavoriteSport", "Height"],
            "rows": []
        }
    }
    
    for i in range(6):
        house_data = [
            str(i+1),
            houses[i]['name'],
            houses[i]['animal'],
            houses[i]['occupation'],
            houses[i]['favorite_sport'],
            houses[i]['height']
        ]
        solution['solution']['rows'].append(house_data)
    
    return solution

solution = solve_puzzle()
print(json.dumps(solution, indent=2))