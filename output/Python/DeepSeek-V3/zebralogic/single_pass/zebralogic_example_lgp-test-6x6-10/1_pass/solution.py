import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Arnold', 'Bob', 'Peter', 'Alice', 'Carol', 'Eric']
    lunches = ['stew', 'grilled cheese', 'stir fry', 'soup', 'pizza', 'spaghetti']
    heights = ['tall', 'average', 'super tall', 'very short', 'very tall', 'short']
    drinks = ['root beer', 'boba tea', 'coffee', 'water', 'tea', 'milk']
    pets = ['hamster', 'fish', 'cat', 'dog', 'bird', 'rabbit']
    phones = ['samsung galaxy s21', 'xiaomi mi 11', 'google pixel 6', 'iphone 13', 'huawei p50', 'oneplus 9']

    # Initialize possibilities for each house
    possibilities = []
    for house in houses:
        possibilities.append({
            'House': house,
            'Name': names.copy(),
            'Lunch': lunches.copy(),
            'Height': heights.copy(),
            'Drink': drinks.copy(),
            'Pet': pets.copy(),
            'Phone': phones.copy()
        })

    # Apply clues one by one
    # Clue 1: The person who uses an iPhone 13 is in the third house.
    for house in houses:
        if house != 3:
            possibilities[house-1]['Phone'].remove('iphone 13')
    
    # Clue 2: Bob is the person who is tall.
    for house in houses:
        if 'Bob' in possibilities[house-1]['Name']:
            possibilities[house-1]['Height'] = ['tall']
        else:
            if 'tall' in possibilities[house-1]['Height']:
                possibilities[house-1]['Height'].remove('tall')
    
    # Clue 3: The person who loves the soup is in the second house.
    possibilities[1]['Lunch'] = ['soup']
    for house in houses:
        if house != 2 and 'soup' in possibilities[house-1]['Lunch']:
            possibilities[house-1]['Lunch'].remove('soup')
    
    # Clue 4: The root beer lover is directly left of the person who uses a Xiaomi Mi 11.
    for house in range(1, 6):
        if 'root beer' in possibilities[house-1]['Drink'] and 'xiaomi mi 11' in possibilities[house]['Phone']:
            pass  # This is a possible configuration
        else:
            if 'root beer' in possibilities[house-1]['Drink']:
                possibilities[house]['Phone'].discard('xiaomi mi 11')
            if 'xiaomi mi 11' in possibilities[house]['Phone']:
                possibilities[house-1]['Drink'].discard('root beer')
    
    # Clue 5: The person who uses a Huawei P50 is directly left of the person who loves eating grilled cheese.
    for house in range(1, 6):
        if 'huawei p50' in possibilities[house-1]['Phone'] and 'grilled cheese' in possibilities[house]['Lunch']:
            pass
        else:
            if 'huawei p50' in possibilities[house-1]['Phone']:
                possibilities[house]['Lunch'].discard('grilled cheese')
            if 'grilled cheese' in possibilities[house]['Lunch']:
                possibilities[house-1]['Phone'].discard('huawei p50')
    
    # Clue 6: The person who loves stir fry is the person who likes milk.
    for house in houses:
        if 'stir fry' in possibilities[house-1]['Lunch']:
            possibilities[house-1]['Drink'] = ['milk']
        if 'milk' in possibilities[house-1]['Drink']:
            if 'stir fry' not in possibilities[house-1]['Lunch']:
                possibilities[house-1]['Lunch'].append('stir fry')
    
    # Clue 7: The person who loves eating grilled cheese is the person who is tall.
    for house in houses:
        if 'grilled cheese' in possibilities[house-1]['Lunch']:
            possibilities[house-1]['Height'] = ['tall']
        if 'tall' in possibilities[house-1]['Height']:
            if 'grilled cheese' not in possibilities[house-1]['Lunch']:
                possibilities[house-1]['Lunch'].append('grilled cheese')
    
    # Clue 8: The person who uses a Xiaomi Mi 11 is the coffee drinker.
    for house in houses:
        if 'xiaomi mi 11' in possibilities[house-1]['Phone']:
            possibilities[house-1]['Drink'] = ['coffee']
        if 'coffee' in possibilities[house-1]['Drink']:
            if 'xiaomi mi 11' not in possibilities[house-1]['Phone']:
                possibilities[house-1]['Phone'].append('xiaomi mi 11')
    
    # Clue 9: The person who uses a OnePlus 9 is Arnold.
    for house in houses:
        if 'Arnold' in possibilities[house-1]['Name']:
            possibilities[house-1]['Phone'] = ['oneplus 9']
        if 'oneplus 9' in possibilities[house-1]['Phone']:
            possibilities[house-1]['Name'] = ['Arnold']
    
    # Clue 10: The person who owns a rabbit is not in the fifth house.
    if 'rabbit' in possibilities[4]['Pet']:
        possibilities[4]['Pet'].remove('rabbit')
    
    # Clue 11: The person with a pet hamster is somewhere to the right of the person who uses a Google Pixel 6.
    # This implies google pixel 6 is left of hamster
    # We'll handle this during the solving process
    
    # Clue 12: The person who is super tall is the person with an aquarium of fish.
    for house in houses:
        if 'super tall' in possibilities[house-1]['Height']:
            possibilities[house-1]['Pet'] = ['fish']
        if 'fish' in possibilities[house-1]['Pet']:
            possibilities[house-1]['Height'] = ['super tall']
    
    # Clue 13: The person with an aquarium of fish is Alice.
    for house in houses:
        if 'fish' in possibilities[house-1]['Pet']:
            possibilities[house-1]['Name'] = ['Alice']
        if 'Alice' in possibilities[house-1]['Name']:
            possibilities[house-1]['Pet'] = ['fish']
    
    # Clue 14: The tea drinker is directly left of the person who is a pizza lover.
    for house in range(1, 6):
        if 'tea' in possibilities[house-1]['Drink'] and 'pizza' in possibilities[house]['Lunch']:
            pass
        else:
            if 'tea' in possibilities[house-1]['Drink']:
                possibilities[house]['Lunch'].discard('pizza')
            if 'pizza' in possibilities[house]['Lunch']:
                possibilities[house-1]['Drink'].discard('tea')
    
    # Clue 15: The person who uses a Samsung Galaxy S21 is Carol.
    for house in houses:
        if 'Carol' in possibilities[house-1]['Name']:
            possibilities[house-1]['Phone'] = ['samsung galaxy s21']
        if 'samsung galaxy s21' in possibilities[house-1]['Phone']:
            possibilities[house-1]['Name'] = ['Carol']
    
    # Clue 16: The person who is a pizza lover is the person who is short.
    for house in houses:
        if 'pizza' in possibilities[house-1]['Lunch']:
            possibilities[house-1]['Height'] = ['short']
        if 'short' in possibilities[house-1]['Height']:
            if 'pizza' not in possibilities[house-1]['Lunch']:
                possibilities[house-1]['Lunch'].append('pizza')
    
    # Clue 17: Arnold is the person who is very tall.
    for house in houses:
        if 'Arnold' in possibilities[house-1]['Name']:
            possibilities[house-1]['Height'] = ['very tall']
        if 'very tall' in possibilities[house-1]['Height']:
            possibilities[house-1]['Name'] = ['Arnold']
    
    # Clue 18: The person who loves the spaghetti eater is the person who uses a Google Pixel 6.
    for house in houses:
        if 'spaghetti' in possibilities[house-1]['Lunch']:
            possibilities[house-1]['Phone'] = ['google pixel 6']
        if 'google pixel 6' in possibilities[house-1]['Phone']:
            possibilities[house-1]['Lunch'] = ['spaghetti']
    
    # Clue 19: The boba tea drinker is somewhere to the right of the person who loves the soup.
    # soup is in house 2, so boba tea is in houses 3-6
    for house in range(1, 3):
        if 'boba tea' in possibilities[house-1]['Drink']:
            possibilities[house-1]['Drink'].remove('boba tea')
    
    # Clue 20: The person with a pet hamster is not in the fifth house.
    if 'hamster' in possibilities[4]['Pet']:
        possibilities[4]['Pet'].remove('hamster')
    
    # Clue 21: The person who is very tall is not in the second house.
    if 'very tall' in possibilities[1]['Height']:
        possibilities[1]['Height'].remove('very tall')
    
    # Clue 22: The person who is super tall is somewhere to the left of Peter.
    # super tall is left of Peter, so Peter is to the right of super tall
    # We'll handle this during solving
    
    # Clue 23: The person who is very short is the person who loves the spaghetti eater.
    for house in houses:
        if 'very short' in possibilities[house-1]['Height']:
            possibilities[house-1]['Lunch'] = ['spaghetti']
        if 'spaghetti' in possibilities[house-1]['Lunch']:
            possibilities[house-1]['Height'] = ['very short']
    
    # Clue 24: The person who keeps a pet bird is somewhere to the left of the person who loves the spaghetti eater.
    # bird is left of spaghetti
    # We'll handle this during solving
    
    # Clue 25: The person with an aquarium of fish is directly left of Eric.
    for house in range(1, 6):
        if 'fish' in possibilities[house-1]['Pet']:
            possibilities[house]['Name'] = ['Eric']
        if 'Eric' in possibilities[house]['Name']:
            possibilities[house-1]['Pet'] = ['fish']
    
    # Clue 26: The person who owns a dog is the person who likes milk.
    for house in houses:
        if 'dog' in possibilities[house-1]['Pet']:
            possibilities[house-1]['Drink'] = ['milk']
        if 'milk' in possibilities[house-1]['Drink']:
            if 'dog' not in possibilities[house-1]['Pet']:
                possibilities[house-1]['Pet'].append('dog')

    # Now we'll try to solve the puzzle by iterating through possibilities
    # This is a simplified approach; a more robust solver would use constraint propagation
    # For brevity, we'll assume the constraints narrow it down sufficiently

    # Based on the constraints, let's deduce some positions:
    # From clue 13 and 25: Alice has fish and is directly left of Eric
    # So Alice is in house X, Eric in X+1
    # From clue 12: Alice is super tall
    # From clue 22: super tall is left of Peter, so Peter is right of Alice
    # From clue 17: Arnold is very tall and not in house 2 (clue 21)
    # From clue 9: Arnold uses oneplus 9
    # From clue 15: Carol uses samsung galaxy s21
    # From clue 1: house 3 uses iphone 13
    # From clue 3: house 2 has soup
    # From clue 19: boba tea is right of soup (so houses 3-6)
    # From clue 14: tea is directly left of pizza
    # From clue 16: pizza lover is short
    # From clue 23: spaghetti lover is very short
    # From clue 18: spaghetti lover uses google pixel 6
    # From clue 24: bird is left of spaghetti
    # From clue 10 and 20: rabbit and hamster not in house 5
    # From clue 5: huawei p50 is directly left of grilled cheese
    # From clue 7: grilled cheese lover is tall
    # From clue 2: Bob is tall, so Bob loves grilled cheese
    # So huawei p50 is left of Bob
    # From clue 4: root beer is directly left of xiaomi mi 11
    # From clue 8: xiaomi mi 11 user drinks coffee
    # From clue 6: stir fry lover drinks milk
    # From clue 26: dog owner drinks milk
    # So stir fry lover has dog

    # Let's try to place Alice and Eric first
    # Alice can't be in house 6 (no house to her right for Eric)
    # Let's try Alice in house 1, Eric in 2
    # But house 2 has soup, and from clue 21 Arnold is not in house 2 (very tall)
    # Eric could be in house 2
    # But from clue 17 Arnold is very tall and not in house 2, so possible
    # Let's try Alice in 1, Eric in 2
    # Then Peter must be to the right of Alice (clue 22), so Peter is in 3-6
    # House 1: Alice, fish, super tall
    # House 2: Eric
    # From clue 25: house 1 has fish, house 2 is Eric - this fits
    # From clue 13: Alice has fish - correct
    # From clue 12: Alice is super tall - correct
    # Arnold is very tall, not in house 2, so could be 3-6
    # From clue 9: Arnold uses oneplus 9
    # House 3 uses iphone 13, so Arnold not in 3
    # So Arnold is in 4,5, or 6
    # From clue 15: Carol uses samsung galaxy s21
    # From clue 7: Bob is tall and loves grilled cheese
    # From clue 5: huawei p50 is left of grilled cheese (Bob)
    # So huawei p50 is left of Bob
    # Let's see possible positions for Bob
    # Bob must be to the right of huawei p50
    # Let's try Bob in house 4, then huawei p50 in 3
    # But house 3 uses iphone 13, not huawei p50
    # So Bob can't be in 4
    # Try Bob in 5, huawei p50 in 4
    # House 3 uses iphone 13, so huawei p50 in 4 is possible
    # Then Arnold could be in 6
    # So:
    # House 1: Alice, fish, super tall
    # House 2: Eric
    # House 3: iphone 13
    # House 4: huawei p50
    # House 5: Bob, grilled cheese, tall
    # House 6: Arnold, oneplus 9, very tall
    # From clue 15: Carol uses samsung galaxy s21
    # Remaining phone: google pixel 6, xiaomi mi 11
    # House 3: iphone 13
    # House 4: huawei p50
    # House 5: ?
    # House 6: oneplus 9
    # So Carol must be in 1,2, or 3
    # House 1: Alice, so not Carol
    # House 2: Eric, not Carol
    # House 3: ?
    # So Carol is in house 3 with samsung galaxy s21
    # But house 3 uses iphone 13 - contradiction
    # So this arrangement doesn't work
    # Let's try Alice in 2, Eric in 3
    # But house 2 has soup, and Alice is in 2
    # From clue 13: Alice has fish
    # From clue 12: Alice is super tall
    # From clue 21: very tall is not in 2 (Arnold is very tall), so ok
    # Peter is to the right of Alice (house 3+)
    # But Eric is in 3, so Peter is 4-6
    # Arnold is very tall, not in 2, so 1,3-6
    # Eric is in 3, so Arnold is 1,4-6
    # From clue 9: Arnold uses oneplus 9
    # From clue 15: Carol uses samsung galaxy s21
    # From clue 7: Bob is tall, loves grilled cheese
    # From clue 5: huawei p50 is left of Bob
    # Let's try Bob in 5, huawei p50 in 4
    # Then Arnold could be in 1 or 6
    # From clue 17: Arnold is very tall
    # From clue 21: very tall not in 2 (already)
    # Let's try Arnold in 1
    # Then house 1: Arnold, oneplus 9, very tall
    # House 2: Alice, fish, super tall, soup
    # House 3: Eric
    # House 4: huawei p50
    # House 5: Bob, grilled cheese, tall
    # House 6: ?
    # Carol must be in 3 or 6
    # House 3: Eric