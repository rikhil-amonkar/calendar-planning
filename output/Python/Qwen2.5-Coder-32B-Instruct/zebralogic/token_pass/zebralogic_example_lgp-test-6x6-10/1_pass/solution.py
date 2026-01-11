import itertools
import json

# Define the possible values for each attribute
names = ['Arnold', 'Bob', 'Peter', 'Alice', 'Carol', 'Eric']
foods = ['stew', 'grilled cheese', 'stir fry', 'soup', 'pizza', 'spaghetti']
heights = ['tall', 'average', 'super tall', 'very short', 'very tall', 'short']
drinks = ['root beer', 'boba tea', 'coffee', 'water', 'tea', 'milk']
pets = ['hamster', 'fish', 'cat', 'dog', 'bird', 'rabbit']
phone_models = ['samsung galaxy s21', 'xiaomi mi 11', 'google pixel 6', 'iphone 13', 'huawei p50', 'oneplus 9']

# Initialize the houses with all possible values
houses = [{attr: set(values) for attr, values in zip(['Name', 'Food', 'Height', 'Drink', 'Pet', 'PhoneModel'],
                                                    [names, foods, heights, drinks, pets, phone_models])} for _ in range(6)]

# Function to apply constraints
def apply_constraints(houses):
    # Constraint 1
    houses[2]['PhoneModel'] = {'iphone 13'}
    
    # Constraint 2
    for house in houses:
        if 'tall' in house['Height']:
            house['Name'].intersection_update({'Bob'})
    
    # Constraint 3
    houses[1]['Food'] = {'soup'}
    
    # Constraint 4
    for i in range(5):
        if 'root beer' in houses[i]['Drink']:
            houses[i+1]['PhoneModel'].intersection_update({'xiaomi mi 11'})
    
    # Constraint 5
    for i in range(5):
        if 'huawei p50' in houses[i]['PhoneModel']:
            houses[i+1]['Food'].intersection_update({'grilled cheese'})
    
    # Constraint 6
    for house in houses:
        if 'stir fry' in house['Food']:
            house['Drink'].intersection_update({'milk'})
    
    # Constraint 7
    for house in houses:
        if 'grilled cheese' in house['Food']:
            house['Height'].intersection_update({'tall'})
    
    # Constraint 8
    for house in houses:
        if 'xiaomi mi 11' in house['PhoneModel']:
            house['Drink'].intersection_update({'coffee'})
    
    # Constraint 9
    houses[4]['Name'] = {'Arnold'}
    
    # Constraint 10 & 20
    for house in houses:
        if house['Pet'] == {'rabbit'}:
            house['Pet'] -= {'rabbit'}
    
    # Constraint 11 & 20
    for i in range(5):
        if 'google pixel 6' in houses[i]['PhoneModel']:
            houses[i+1:]['Pet'].intersection_update({'hamster'})
    
    # Constraint 12
    for house in houses:
        if 'super tall' in house['Height']:
            house['Pet'].intersection_update({'fish'})
    
    # Constraint 13
    houses[2]['Pet'] = {'fish'}
    houses[2]['Name'] = {'Alice'}
    
    # Constraint 14
    for i in range(5):
        if 'tea' in houses[i]['Drink']:
            houses[i+1]['Food'].intersection_update({'pizza'})
    
    # Constraint 15
    houses[0]['Name'] = {'Carol'}
    
    # Constraint 16
    for house in houses:
        if 'pizza' in house['Food']:
            house['Height'].intersection_update({'short'})
    
    # Constraint 17
    houses[4]['Height'] = {'very tall'}
    
    # Constraint 18
    for house in houses:
        if 'spaghetti' in house['Food']:
            house['PhoneModel'].intersection_update({'google pixel 6'})
    
    # Constraint 19
    for i in range(5):
        if 'soup' in houses[i]['Food']:
            houses[i+1:]['Drink'].intersection_update({'boba tea'})
    
    # Constraint 21
    for house in houses:
        if 'very tall' in house['Height']:
            house['Height'] -= {'very tall'}
    
    # Constraint 22
    for i in range(5):
        if 'super tall' in houses[i]['Height']:
            houses[i+1:]['Name'].intersection_update({'Peter'})
    
    # Constraint 23
    for house in houses:
        if 'spaghetti' in house['Food']:
            house['Height'].intersection_update({'very short'})
    
    # Constraint 24
    for i in range(5):
        if 'bird' in houses[i]['Pet']:
            houses[i+1:]['Food'].intersection_update({'spaghetti'})
    
    # Constraint 25
    for i in range(5):
        if 'fish' in houses[i]['Pet']:
            houses[i+1]['Name'].intersection_update({'Eric'})
    
    # Constraint 26
    for house in houses:
        if 'dog' in house['Pet']:
            house['Drink'].intersection_update({'milk'})

# Apply constraints to reduce the search space
apply_constraints(houses)

# Backtracking function
def solve(houses, index=0):
    if index == 6:
        return True
    
    # Try all permutations of remaining attributes
    for perm in itertools.permutations(names[index:], len(names) - index):
        for name in perm:
            if name not in houses[index]['Name']:
                continue
            
            # Assign the name
            houses[index]['Name'] = {name}
            
            for food in foods:
                if food not in houses[index]['Food']:
                    continue
                
                # Assign the food
                houses[index]['Food'] = {food}
                
                for height in heights:
                    if height not in houses[index]['Height']:
                        continue
                    
                    # Assign the height
                    houses[index]['Height'] = {height}
                    
                    for drink in drinks:
                        if drink not in houses[index]['Drink']:
                            continue
                        
                        # Assign the drink
                        houses[index]['Drink'] = {drink}
                        
                        for pet in pets:
                            if pet not in houses[index]['Pet']:
                                continue
                            
                            # Assign the pet
                            houses[index]['Pet'] = {pet}
                            
                            for phone_model in phone_models:
                                if phone_model not in houses[index]['PhoneModel']:
                                    continue
                                
                                # Assign the phone model
                                houses[index]['PhoneModel'] = {phone_model}
                                
                                # Check if the current assignment is valid
                                valid = True
                                for attr in ['Name', 'Food', 'Height', 'Drink', 'Pet', 'PhoneModel']:
                                    for j in range(6):
                                        if j != index and houses[j][attr] & houses[index][attr]:
                                            valid = False
                                            break
                                    if not valid:
                                        break
                                
                                if valid:
                                    # Recurse to the next house
                                    if solve(houses, index + 1):
                                        return True
                                
                                # Backtrack
                                houses[index]['PhoneModel'].add(phone_model)
                            
                            houses[index]['Pet'].add(pet)
                        
                        houses[index]['Drink'].add(drink)
                    
                    houses[index]['Height'].add(height)
                
                houses[index]['Food'].add(food)
            
            houses[index]['Name'].add(name)
    
    return False

# Solve the puzzle
solve(houses)

# Construct the solution in JSON format
solution = {
    "solution": {
        "header": ["House", "Name", "Food", "Height", "Drink", "Pet", "PhoneModel"],
        "rows": []
    }
}

for i, house in enumerate(houses, 1):
    row = [str(i)]
    for attr in ['Name', 'Food', 'Height', 'Drink', 'Pet', 'PhoneModel']:
        row.append(list(house[attr])[0])
    solution["solution"]["rows"].append(row)

# Print the solution as JSON
print(json.dumps(solution, indent=2))