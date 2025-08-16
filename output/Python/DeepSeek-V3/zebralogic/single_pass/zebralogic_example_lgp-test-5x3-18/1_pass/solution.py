import json
from itertools import permutations

def solve_puzzle():
    # Define all possible options
    names = ['Alice', 'Eric', 'Arnold', 'Bob', 'Peter']
    flowers = ['tulips', 'roses', 'lilies', 'daffodils', 'carnations']
    animals = ['dog', 'horse', 'cat', 'bird', 'fish']
    houses = ['1', '2', '3', '4', '5']
    
    # Initialize possibilities for each attribute in each house
    possibilities = []
    for house in houses:
        possibilities.append({
            'name': names.copy(),
            'flower': flowers.copy(),
            'animal': animals.copy()
        })
    
    # Apply clue 1: Alice is in the second house.
    house_idx = 1  # 0-based index for house 2
    possibilities[house_idx]['name'] = ['Alice']
    for i in range(5):
        if i != house_idx:
            if 'Alice' in possibilities[i]['name']:
                possibilities[i]['name'].remove('Alice')
    
    # Apply clue 8: Alice is directly left of the person who keeps horses.
    # So horse is in house 3 (since Alice is in 2)
    house_idx = 2  # house 3
    possibilities[house_idx]['animal'] = ['horse']
    for i in range(5):
        if i != house_idx and 'horse' in possibilities[i]['animal']:
            possibilities[i]['animal'].remove('horse')
    
    # Apply clue 5: The person who keeps horses is Eric.
    # So Eric is in house 3
    possibilities[house_idx]['name'] = ['Eric']
    for i in range(5):
        if i != house_idx and 'Eric' in possibilities[i]['name']:
            possibilities[i]['name'].remove('Eric')
    
    # Apply clue 6: There are two houses between the dog owner and Bob.
    # So if dog is in 1, Bob is in 4
    # Or dog in 2, Bob in 5
    # But Alice is in 2, and names are unique, so Bob can't be in 2
    # Also, Alice is in 2, so dog can't be in 2 (since names are unique)
    # So only possible: dog in 1, Bob in 4
    possibilities[0]['animal'] = ['dog']
    for i in range(1, 5):
        if 'dog' in possibilities[i]['animal']:
            possibilities[i]['animal'].remove('dog')
    possibilities[3]['name'] = ['Bob']
    for i in range(5):
        if i != 3 and 'Bob' in possibilities[i]['name']:
            possibilities[i]['name'].remove('Bob')
    
    # Apply clue 7: The fish enthusiast is directly left of Bob.
    # Bob is in 4, so fish is in 3
    # But house 3 has horse, so this contradicts unless fish is separate from animal
    # Wait, fish is an animal, but house 3 has horse, so this can't be
    # So our assumption that dog is in 1 must be correct, and no other options
    # Therefore, clue 7 implies fish is in 3, but house 3 has horse, so contradiction
    # Wait, maybe I misapplied clue 6. Alternative: dog in 2, Bob in 5
    # But Alice is in 2, and names are unique, so dog can't be in 2 if Alice is there
    # Because names and animals are separate attributes
    # So dog is an animal, Alice is a name, so dog can be in 2
    # Let me re-examine clue 6 with dog in 2, Bob in 5
    # Reset some possibilities
    possibilities[0]['animal'] = animals.copy()
    possibilities[3]['name'] = names.copy()
    possibilities[0]['animal'].remove('horse')  # horse is in 3
    possibilities[3]['name'].remove('Alice')
    possibilities[3]['name'].remove('Eric')
    
    # Try dog in 2, Bob in 5
    possibilities[1]['animal'] = ['dog']
    for i in range(5):
        if i != 1 and 'dog' in possibilities[i]['animal']:
            possibilities[i]['animal'].remove('dog')
    possibilities[4]['name'] = ['Bob']
    for i in range(5):
        if i != 4 and 'Bob' in possibilities[i]['name']:
            possibilities[i]['name'].remove('Bob')
    
    # Now apply clue 7: fish is directly left of Bob (Bob in 5, so fish in 4)
    possibilities[3]['animal'] = ['fish']
    for i in range(5):
        if i != 3 and 'fish' in possibilities[i]['animal']:
            possibilities[i]['animal'].remove('fish')
    
    # Apply clue 4: The fish enthusiast loves daffodils.
    possibilities[3]['flower'] = ['daffodils']
    for i in range(5):
        if i != 3 and 'daffodils' in possibilities[i]['flower']:
            possibilities[i]['flower'].remove('daffodils')
    
    # Apply clue 2: The person who loves lilies keeps the bird.
    # So wherever lilies is, animal is bird, and vice versa
    # This will be applied during the permutation check
    
    # Apply clue 3: Peter is somewhere to the right of the person who loves tulips.
    # So tulips is in a house with number less than Peter's house
    # This will be applied during permutation check
    
    # Apply clue 9: The person who loves carnations is directly left of the person who loves tulips.
    # So carnations in n, tulips in n+1
    # This will be applied during permutation check
    
    # Apply clue 10: The cat lover is not in the first house.
    possibilities[0]['animal'] = [a for a in possibilities[0]['animal'] if a != 'cat']
    
    # Now we need to assign the remaining names, flowers, and animals
    # Remaining names: Arnold, Peter (Alice in 2, Eric in 3, Bob in 5)
    # So house 1 and 4 need names
    # House 4 has fish, name is not assigned yet (Bob is in 5)
    # Wait, names left: Arnold, Peter
    # House 1 and 4 names:
    # Let's try permutations
    
    # Remaining flowers: tulips, roses, lilies, carnations (daffodils in 4)
    # Remaining animals: cat, bird (dog in 2, horse in 3, fish in 4)
    # So house 1 and 5 animals: house 1 can't be cat (clue 10), so house 1 must be bird, house 5 cat
    possibilities[0]['animal'] = ['bird']
    possibilities[4]['animal'] = ['cat']
    for i in range(5):
        if i != 0 and 'bird' in possibilities[i]['animal']:
            possibilities[i]['animal'].remove('bird')
        if i != 4 and 'cat' in possibilities[i]['animal']:
            possibilities[i]['animal'].remove('cat')
    
    # Apply clue 2: lilies is with bird
    possibilities[0]['flower'] = ['lilies']
    for i in range(5):
        if i != 0 and 'lilies' in possibilities[i]['flower']:
            possibilities[i]['flower'].remove('lilies')
    
    # Now assign flowers to houses 1,2,3,5 (4 has daffodils)
    # House 1: lilies
    # Remaining flowers: tulips, roses, carnations
    # House 2,3,5 flowers
    # Apply clue 9: carnations is directly left of tulips
    # Possible positions:
    # carnations in 2, tulips in 3
    # carnations in 3, tulips in 4 - but 4 has daffodils, so no
    # carnations in 4, tulips in 5 - but 4 has daffodils, so no
    # So only carnations in 2, tulips in 3
    possibilities[1]['flower'] = ['carnations']
    possibilities[2]['flower'] = ['tulips']
    for i in range(5):
        if i != 1 and 'carnations' in possibilities[i]['flower']:
            possibilities[i]['flower'].remove('carnations')
        if i != 2 and 'tulips' in possibilities[i]['flower']:
            possibilities[i]['flower'].remove('tulips')
    
    # Now house 5 flower must be roses
    possibilities[4]['flower'] = ['roses']
    
    # Now assign names: remaining are Arnold and Peter
    # House 1 and 4 names
    # Apply clue 3: Peter is to the right of tulips (tulips in 3)
    # So Peter must be in 4 or 5
    # But Bob is in 5, so Peter in 4
    possibilities[3]['name'] = ['Peter']
    possibilities[0]['name'] = ['Arnold']
    
    # Verify all constraints
    # Clue 3: Peter is right of tulips (tulips in 3, Peter in 4) - OK
    # Clue 10: cat not in first house (cat in 5) - OK
    # All other clues are satisfied by construction
    
    # Prepare the solution
    solution = {
        "solution": {
            "header": ["House", "Name", "Flower", "Animal"],
            "rows": []
        }
    }
    
    for i in range(5):
        house = str(i + 1)
        name = possibilities[i]['name'][0]
        flower = possibilities[i]['flower'][0]
        animal = possibilities[i]['animal'][0]
        solution["solution"]["rows"].append([house, name, flower, animal])
    
    return json.dumps(solution)

print(solve_puzzle())