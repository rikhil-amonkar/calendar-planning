import itertools
import json

def apply_constraints(houses):
    # Constraint 1: The person who owns a Toyota Camry is in the sixth house.
    houses[5]['CarModel'] = {'toyota camry'}
    
    # Constraint 7: The person whose mother's name is Kailyn is in the sixth house.
    houses[5]['Mother'] = {'Kailyn'}
    
    # Constraint 3: The person who owns a Chevrolet Silverado is The person whose mother's name is Aniya.
    # Constraint 4: The person who owns a Chevrolet Silverado is not in the second house.
    for i in range(6):
        if i != 1:
            if 'chevrolet silverado' in houses[i]['CarModel']:
                houses[i]['Mother'] = {'Aniya'}
            elif 'Aniya' in houses[i]['Mother']:
                houses[i]['CarModel'] = {'chevrolet silverado'}
    
    # Constraint 5: The person who owns a Ford F-150 is The person whose mother's name is Sarah.
    for i in range(6):
        if 'ford f150' in houses[i]['CarModel']:
            houses[i]['Mother'] = {'Sarah'}
        elif 'Sarah' in houses[i]['Mother']:
            houses[i]['CarModel'] = {'ford f150'}
    
    # Constraint 6: The person who owns a BMW 3 Series is Bob.
    for i in range(6):
        if 'bmw 3 series' in houses[i]['CarModel']:
            houses[i]['Name'] = {'Bob'}
        elif 'Bob' in houses[i]['Name']:
            houses[i]['CarModel'] = {'bmw 3 series'}
    
    # Constraint 8: Eric is directly left of the person who enjoys knitting.
    for i in range(5):
        if 'Eric' in houses[i]['Name']:
            houses[i+1]['Hobby'] = {'knitting'}
        elif 'knitting' in houses[i+1]['Hobby']:
            houses[i]['Name'] = {'Eric'}
    
    # Constraint 13: Eric is the person who enjoys gardening.
    for i in range(6):
        if 'Eric' in houses[i]['Name']:
            houses[i]['Hobby'] = {'gardening'}
        elif 'gardening' in houses[i]['Hobby']:
            houses[i]['Name'] = {'Eric'}
    
    # Constraint 17: The person whose mother's name is Holly is directly left of the person who enjoys knitting.
    for i in range(5):
        if 'Holly' in houses[i]['Mother']:
            houses[i+1]['Hobby'] = {'knitting'}
        elif 'knitting' in houses[i+1]['Hobby']:
            houses[i]['Mother'] = {'Holly'}
    
    # Constraint 9: There is one house between The person whose mother's name is Sarah and the person who owns a Toyota Camry.
    for i in range(5):
        if 'Sarah' in houses[i]['Mother']:
            if 'toyota camry' in houses[i+2]['CarModel']:
                houses[i+2]['CarModel'] = {'toyota camry'}
            elif 'toyota camry' in houses[i-1]['CarModel']:
                houses[i-1]['CarModel'] = {'toyota camry'}
        elif 'toyota camry' in houses[i]['CarModel']:
            if 'Sarah' in houses[i-2]['Mother']:
                houses[i-2]['Mother'] = {'Sarah'}
            elif 'Sarah' in houses[i+1]['Mother']:
                houses[i+1]['Mother'] = {'Sarah'}
    
    # Constraint 15: There is one house between The person whose mother's name is Sarah and the person who loves cooking.
    for i in range(5):
        if 'Sarah' in houses[i]['Mother']:
            if 'cooking' in houses[i+2]['Hobby']:
                houses[i+2]['Hobby'] = {'cooking'}
            elif 'cooking' in houses[i-1]['Hobby']:
                houses[i-1]['Hobby'] = {'cooking'}
        elif 'cooking' in houses[i]['Hobby']:
            if 'Sarah' in houses[i-2]['Mother']:
                houses[i-2]['Mother'] = {'Sarah'}
            elif 'Sarah' in houses[i+1]['Mother']:
                houses[i+1]['Mother'] = {'Sarah'}
    
    # Constraint 10: The person whose mother's name is Penny is somewhere to the right of the person who enjoys knitting.
    for i in range(6):
        if 'knitting' in houses[i]['Hobby']:
            for j in range(i+1, 6):
                houses[j]['Mother'].discard('Penny')
        elif 'Penny' in houses[i]['Mother']:
            for j in range(i):
                houses[j]['Hobby'].discard('knitting')
    
    # Constraint 11: The person whose mother's name is Aniya is somewhere to the right of the person who owns a Honda Civic.
    for i in range(6):
        if 'honda civic' in houses[i]['CarModel']:
            for j in range(i+1, 6):
                houses[j]['Mother'].discard('Aniya')
        elif 'Aniya' in houses[i]['Mother']:
            for j in range(i):
                houses[j]['CarModel'].discard('honda civic')
    
    # Constraint 12: Alice is somewhere to the right of the person who owns a Ford F-150.
    for i in range(6):
        if 'ford f150' in houses[i]['CarModel']:
            for j in range(i+1, 6):
                houses[j]['Name'].discard('Alice')
        elif 'Alice' in houses[i]['Name']:
            for j in range(i):
                houses[j]['CarModel'].discard('ford f150')
    
    # Constraint 14: The woodworking hobbyist is somewhere to the left of the person who enjoys knitting.
    for i in range(6):
        if 'knitting' in houses[i]['Hobby']:
            for j in range(i):
                houses[j]['Hobby'].discard('woodworking')
        elif 'woodworking' in houses[i]['Hobby']:
            for j in range(i+1, 6):
                houses[j]['Hobby'].discard('woodworking')
    
    # Constraint 16: The person who owns a Honda Civic is Arnold.
    for i in range(6):
        if 'honda civic' in houses[i]['CarModel']:
            houses[i]['Name'] = {'Arnold'}
        elif 'Arnold' in houses[i]['Name']:
            houses[i]['CarModel'] = {'honda civic'}
    
    # Constraint 2: Carol is the photography enthusiast.
    for i in range(6):
        if 'Carol' in houses[i]['Name']:
            houses[i]['Hobby'] = {'photography'}
        elif 'photography' in houses[i]['Hobby']:
            houses[i]['Name'] = {'Carol'}

def solve_puzzle():
    # Initialize houses with all possible values
    houses = [
        {
            'Name': {'Eric', 'Bob', 'Peter', 'Alice', 'Arnold', 'Carol'},
            'CarModel': {'ford f150', 'honda civic', 'toyota camry', 'tesla model 3', 'chevrolet silverado', 'bmw 3 series'},
            'Mother': {'Sarah', 'Penny', 'Holly', 'Aniya', 'Kailyn', 'Janelle'},
            'Hobby': {'photography', 'cooking', 'knitting', 'gardening', 'woodworking', 'painting'}
        } for _ in range(6)
    ]
    
    # Apply all constraints
    apply_constraints(houses)
    
    # Backtracking function to solve the puzzle
    def backtrack(house_index):
        if house_index == 6:
            return True
        
        # Try each combination of values for the current house
        for name in list(houses[house_index]['Name']):
            for car_model in list(houses[house_index]['CarModel']):
                for mother in list(houses[house_index]['Mother']):
                    for hobby in list(houses[house_index]['Hobby']):
                        # Check if this combination is valid
                        if len({name, car_model, mother, hobby}) == 4:
                            # Assign values
                            houses[house_index]['Name'] = {name}
                            houses[house_index]['CarModel'] = {car_model}
                            houses[house_index]['Mother'] = {mother}
                            houses[house_index]['Hobby'] = {hobby}
                            
                            # Propagate constraints
                            apply_constraints(houses)
                            
                            # Recur for the next house
                            if backtrack(house_index + 1):
                                return True
                            
                            # Backtrack
                            houses[house_index]['Name'] = {'Eric', 'Bob', 'Peter', 'Alice', 'Arnold', 'Carol'}
                            houses[house_index]['CarModel'] = {'ford f150', 'honda civic', 'toyota camry', 'tesla model 3', 'chevrolet silverado', 'bmw 3 series'}
                            houses[house_index]['Mother'] = {'Sarah', 'Penny', 'Holly', 'Aniya', 'Kailyn', 'Janelle'}
                            houses[house_index]['Hobby'] = {'photography', 'cooking', 'knitting', 'gardening', 'woodworking', 'painting'}
        
        return False
    
    # Start backtracking
    if backtrack(0):
        # Format the solution as JSON
        solution = {
            "solution": {
                "header": ["House", "Name", "CarModel", "Mother", "Hobby"],
                "rows": []
            }
        }
        for i in range(6):
            house_info = [
                str(i + 1),
                list(houses[i]['Name'])[0],
                list(houses[i]['CarModel'])[0],
                list(houses[i]['Mother'])[0],
                list(houses[i]['Hobby'])[0]
            ]
            solution['solution']['rows'].append(house_info)
        
        return json.dumps(solution, indent=2)
    else:
        return "No solution found"

# Solve the puzzle and print the result
print(solve_puzzle())