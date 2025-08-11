import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values for each category
    names = ['Peter', 'Bob', 'Carol', 'Eric', 'Alice', 'Arnold']
    pets = ['bird', 'dog', 'cat', 'rabbit', 'fish', 'hamster']
    house_styles = ['victorian', 'ranch', 'modern', 'mediterranean', 'colonial', 'craftsman']
    months = ['mar', 'sept', 'may', 'feb', 'jan', 'april']
    
    # Initialize houses
    houses = [{'House': str(i+1)} for i in range(6)]
    
    # Apply clues one by one
    # Clue 3: The person whose birthday is in May is in the second house.
    for house in houses:
        if house['House'] == '2':
            house['Birthday month'] = 'may'
    
    # Clue 4: The person living in a colonial-style house is in the second house.
    for house in houses:
        if house['House'] == '2':
            house['House style'] = 'colonial'
    
    # Clue 5: Carol is in the third house.
    for house in houses:
        if house['House'] == '3':
            house['Name'] = 'Carol'
    
    # Clue 8: Eric is in the sixth house.
    for house in houses:
        if house['House'] == '6':
            house['Name'] = 'Eric'
    
    # Clue 14: Peter is the person living in a colonial-style house.
    for house in houses:
        if 'House style' in house and house['House style'] == 'colonial':
            house['Name'] = 'Peter'
    
    # Clue 17: Carol is the person whose birthday is in March.
    for house in houses:
        if 'Name' in house and house['Name'] == 'Carol':
            house['Birthday month'] = 'mar'
    
    # Clue 18: The person in a Craftsman-style house is in the fourth house.
    for house in houses:
        if house['House'] == '4':
            house['House style'] = 'craftsman'
    
    # Clue 11: The person in a Craftsman-style house is Arnold.
    for house in houses:
        if 'House style' in house and house['House style'] == 'craftsman':
            house['Name'] = 'Arnold'
    
    # Clue 19: The person who owns a dog is in the fourth house.
    for house in houses:
        if house['House'] == '4':
            house['Pet'] = 'dog'
    
    # Clue 15: The person whose birthday is in January is directly left of the person whose birthday is in April.
    # This means jan is in house X, april is in house X+1
    possible_jan_april = [(i, i+1) for i in range(1, 6) if i+1 <= 6]
    # Filter out positions already taken
    possible_jan_april = [(x, y) for x, y in possible_jan_april 
                          if 'Birthday month' not in houses[x-1] and 'Birthday month' not in houses[y-1]]
    
    # Clue 2: The person whose birthday is in January is somewhere to the left of the person whose birthday is in September.
    # So jan is left of sept (house number jan < house number sept)
    
    # Clue 7: The person with an aquarium of fish is somewhere to the right of Bob.
    # So fish is right of Bob (house number fish > house number Bob)
    
    # Clue 10: There are two houses between the person residing in a Victorian house and the person with a pet hamster.
    # If victorian is in X, hamster is in X+3
    possible_vic_ham = [(i, i+3) for i in range(1, 4) if i+3 <= 6]
    
    # Clue 9: There is one house between the person who has a cat and the person residing in a Victorian house.
    # If cat is in X, victorian is in X+2, or victorian is in X-2 and cat is in X
    possible_cat_vic = [(i, i+2) for i in range(1, 5) if i+2 <= 6] + [(i+2, i) for i in range(1, 5) if i+2 <= 6]
    
    # Clue 16: There is one house between the person who keeps a pet bird and the person in a modern-style house.
    # bird in X, modern in X+2 or modern in X, bird in X+2
    possible_bird_modern = [(i, i+2) for i in range(1, 5) if i+2 <= 6] + [(i+2, i) for i in range(1, 5) if i+2 <= 6]
    
    # Clue 12: The person in a colonial-style house is somewhere to the left of the person in a modern-style house.
    # colonial is in 2, so modern is right of 2
    
    # Clue 6: The person in a Mediterranean-style villa is not in the sixth house.
    # mediterranean is not in 6
    
    # Clue 1: The person with a pet hamster is somewhere to the right of the person whose birthday is in March.
    # hamster is right of mar (house number hamster > house number mar)
    # mar is in 3, so hamster is in 4,5,6
    
    # From clue 10 and mar in 3, victorian must be in X, hamster in X+3
    # hamster must be >=4, so X can be 1 (hamster in 4)
    # So victorian in 1, hamster in 4
    # But hamster is in 4, but 4 has dog (from clue 19), so contradiction
    # Next option: victorian in 2, hamster in 5
    # But 2 is colonial, so victorian can't be in 2
    # Next option: victorian in 3, hamster in 6
    # 3 is carol, no house style assigned yet
    for house in houses:
        if house['House'] == '3':
            house['House style'] = 'victorian'
    for house in houses:
        if house['House'] == '6':
            house['Pet'] = 'hamster'
    
    # Now from clue 9: one house between cat and victorian
    # victorian is in 3, so cat is in 1 or 5
    # From clue 10: two houses between victorian (3) and hamster (6) - already satisfied
    
    # From clue 16: one house between bird and modern
    # modern must be right of colonial (2), so modern is 3,4,5,6
    # 3 is victorian, 4 is craftsman, so modern is 5 or 6
    # bird is then 3 or 7 (invalid) or -1 (invalid), or modern is X, bird is X+2
    # if modern is 5, bird is 3
    # if modern is 6, bird is 4
    # 4 has dog, so bird is 3
    # So modern is 5, bird is 3
    for house in houses:
        if house['House'] == '5':
            house['House style'] = 'modern'
    for house in houses:
        if house['House'] == '3':
            house['Pet'] = 'bird'
    
    # From clue 9: cat is in 1 or 5
    # 5's pet is not assigned, but let's see other constraints
    # From clue 7: fish is right of Bob
    # From clue 13: fish is not in 2
    # fish could be in 3,4,5,6
    # 3 has bird, 4 has dog, 6 has hamster, so fish is in 5
    for house in houses:
        if house['House'] == '5':
            house['Pet'] = 'fish'
    # So cat must be in 1
    for house in houses:
        if house['House'] == '1':
            house['Pet'] = 'cat'
    
    # Now assign remaining pets: rabbit is left
    # Pets assigned so far: 1:cat, 3:bird, 4:dog, 5:fish, 6:hamster
    # So 2 has rabbit
    for house in houses:
        if house['House'] == '2':
            house['Pet'] = 'rabbit'
    
    # From clue 7: fish is right of Bob
    # fish is in 5, so Bob is left of 5
    # Bob could be in 1,2,3,4
    # 2 is Peter, 3 is Carol, 4 is Arnold, so Bob is in 1
    for house in houses:
        if house['House'] == '1':
            house['Name'] = 'Bob'
    
    # Remaining name is Alice, which must be in 5
    for house in houses:
        if house['House'] == '5':
            house['Name'] = 'Alice'
    
    # Now assign months
    # Months assigned: 2:may, 3:mar
    # From clue 15: jan is directly left of april
    # Possible positions: (1,2) - but 2 is may, (4,5), (5,6)
    # From clue 2: jan is left of sept
    # From clue 17: mar is in 3
    # From clue 1: hamster is right of mar (already satisfied)
    # Try (4,5): 4:jan, 5:april
    # Then sept must be right of jan, so sept is 6
    # Then feb is left in 1
    for house in houses:
        if house['House'] == '4':
            house['Birthday month'] = 'jan'
        if house['House'] == '5':
            house['Birthday month'] = 'april'
        if house['House'] == '6':
            house['Birthday month'] = 'sept'
        if house['House'] == '1':
            house['Birthday month'] = 'feb'
    
    # Now assign remaining house styles
    # Assigned: 2:colonial, 3:victorian, 4:craftsman, 5:modern
    # Remaining: ranch, mediterranean
    # From clue 6: mediterranean is not in 6, so mediterranean is in 1, ranch in 6
    for house in houses:
        if house['House'] == '1':
            house['House style'] = 'mediterranean'
        if house['House'] == '6':
            house['House style'] = 'ranch'
    
    # Verify all constraints are satisfied
    # Prepare the solution in the required format
    solution = {
        "solution": {
            "header": ["House", "Name", "Pet", "House style", "Birthday month"],
            "rows": []
        }
    }
    
    for house in houses:
        row = [
            house['House'],
            house.get('Name', ''),
            house.get('Pet', ''),
            house.get('House style', ''),
            house.get('Birthday month', '')
        ]
        solution["solution"]["rows"].append(row)
    
    return json.dumps(solution)

if __name__ == "__main__":
    print(solve_puzzle())