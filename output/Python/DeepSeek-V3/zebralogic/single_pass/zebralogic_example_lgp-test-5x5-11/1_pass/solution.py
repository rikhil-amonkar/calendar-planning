import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories
    names = ['Peter', 'Arnold', 'Eric', 'Bob', 'Alice']
    heights = ['average', 'very tall', 'very short', 'short', 'tall']
    cigars = ['prince', 'dunhill', 'blends', 'pall mall', 'blue master']
    smoothies = ['lime', 'cherry', 'dragonfruit', 'watermelon', 'desert']
    phones = ['oneplus 9', 'samsung galaxy s21', 'iphone 13', 'huawei p50', 'google pixel 6']
    
    # Generate all possible house permutations (1-5)
    houses = [1, 2, 3, 4, 5]
    
    # We'll use constraint satisfaction to find the solution
    # Let's create a list of dictionaries representing each house's attributes
    solution = []
    
    # We'll iterate through all possible permutations of attributes
    # This is brute-force but manageable for 5 houses
    
    # Let's approach this step by step using the clues
    
    # From clue 15: The person who uses an iPhone 13 is Eric.
    # From clue 6: Eric is very tall.
    # From clue 9: Eric is directly left of the person who likes Cherry smoothies.
    # So Eric is in house X, cherry lover is in house X+1
    
    # From clue 14: There are two houses between the person who is very tall (Eric) and the Dragonfruit smoothie lover (Bob, from clue 11)
    # So if Eric is in X, Bob is in X+3
    # Possible positions:
    # Eric in 1, Bob in 4
    # Eric in 2, Bob in 5
    
    # From clue 8: Bob is not in the fourth house.
    # So Bob must be in 5, Eric in 2
    
    # So:
    # House 2: Name=Eric, Height=very tall, Phone=iphone 13
    # House 3: Smoothie=cherry (from clue 9, Eric is directly left of cherry)
    # House 5: Name=Bob
    
    # From clue 11: Bob likes dragonfruit
    # So House 5: Smoothie=dragonfruit
    
    # From clue 10: Bob is the Dunhill smoker
    # So House 5: Cigar=dunhill
    
    # From clue 5: The person who has an average height is the Dunhill smoker.
    # So House 5: Height=average
    
    # From clue 4: The person who uses an iPhone 13 is directly left of the person who smokes Blue Master.
    # iPhone 13 is in house 2, so blue master is in house 3
    
    # From clue 12: The person who uses an iPhone 13 and the person who uses a OnePlus 9 are next to each other.
    # iPhone 13 is in 2, so OnePlus 9 is in 1 or 3
    
    # From clue 7: Arnold is directly left of the person who uses a Huawei P50.
    # So Arnold is in X, huawei p50 is in X+1
    
    # From clue 2: There is one house between Eric and Alice.
    # Eric is in 2, so Alice is in 4 (one house between means positions differ by 2)
    
    # From clue 3: The person who is short is the person who smokes blends.
    # From clue 13: The person who uses a Samsung Galaxy S21 is the person who is short.
    # So blends smoker is short and uses samsung galaxy s21
    
    # From clue 1: The Prince smoker is the Desert smoothie lover.
    
    # From clue 16: The Desert smoothie lover is somewhere to the left of the person who drinks Lime smoothies.
    
    # From clue 17: Arnold and the person who is very short are next to each other.
    
    # Now let's assign what we know so far:
    solution = [
        {'House': 1, 'Name': None, 'Height': None, 'Cigar': None, 'Smoothie': None, 'PhoneModel': None},
        {'House': 2, 'Name': 'Eric', 'Height': 'very tall', 'Cigar': None, 'Smoothie': None, 'PhoneModel': 'iphone 13'},
        {'House': 3, 'Name': None, 'Height': None, 'Cigar': 'blue master', 'Smoothie': 'cherry', 'PhoneModel': None},
        {'House': 4, 'Name': 'Alice', 'Height': None, 'Cigar': None, 'Smoothie': None, 'PhoneModel': None},
        {'House': 5, 'Name': 'Bob', 'Height': 'average', 'Cigar': 'dunhill', 'Smoothie': 'dragonfruit', 'PhoneModel': None}
    ]
    
    # From clue 12: OnePlus 9 is in 1 or 3
    # House 3 phone is not yet assigned, but let's see other constraints
    
    # From clue 7: Arnold is directly left of huawei p50
    # Possible positions:
    # Arnold in 1, huawei p50 in 2 - but 2 has iphone 13
    # Arnold in 3, huawei p50 in 4
    # Arnold in 4, huawei p50 in 5 - but 5 phone not assigned yet
    
    # Let's try Arnold in 3:
    # Then huawei p50 in 4
    # So:
    # House 3: Name=Arnold
    # House 4: PhoneModel=huawei p50
    
    # From clue 17: Arnold and very short are next to each other
    # So very short is in 2 or 4
    # 2 has height very tall, so very short must be in 4
    # So House 4: Height=very short
    
    # Now assign names: remaining are Peter and Alice (Alice is in 4), so Peter must be in 1 or 3
    # 3 is Arnold, so Peter is in 1
    # So House 1: Name=Peter
    
    # From clue 12: OnePlus 9 is next to iphone 13 (house 2)
    # So OnePlus 9 is in 1 or 3
    # House 3 phone not assigned yet
    # House 1 phone not assigned
    
    # From clue 13: samsung galaxy s21 is short
    # From clue 3: blends smoker is short and uses samsung galaxy s21
    # So blends smoker is short and uses samsung galaxy s21
    
    # Possible houses for blends:
    # House 1, 3, or 4
    # 4 has height very short, not short, so not 4
    # 1 or 3
    
    # If blends is in 1:
    # Then house 1: cigar=blends, height=short, phone=samsung galaxy s21
    # Then from clue 12: OnePlus 9 must be in 3
    # So house 3: phone=oneplus 9 or huawei p50?
    # Wait, house 4 is huawei p50, so house 3 phone is not assigned yet
    # But if house 1 is samsung, then oneplus must be in 3
    
    # So:
    # House 1: cigar=blends, height=short, phone=samsung galaxy s21
    # House 3: phone=oneplus 9
    
    # Then remaining phone is google pixel 6, which must be in 5
    # House 5: PhoneModel=google pixel 6
    
    # Now assign heights: we have very tall (2), average (5), very short (4), short (1)
    # Remaining height is tall, which must be in 3
    # So House 3: Height=tall
    
    # Now assign cigars: we have blue master (3), dunhill (5), blends (1)
    # Remaining cigars: prince, pall mall
    # House 2 and 4
    
    # From clue 1: prince smoker is desert lover
    # Possible in 2 or 4
    
    # From clue 16: desert is left of lime
    # So desert is in X, lime is in Y where X < Y
    
    # Current smoothies: cherry (3), dragonfruit (5)
    # Remaining: lime, watermelon, desert
    
    # House 1, 2, 4
    
    # House 2: if cigar is prince, then smoothie is desert
    # Then lime must be to the right, so could be in 4
    
    # Let's try:
    # House 2: cigar=prince, smoothie=desert
    # Then from clue 1 this satisfies
    # Then lime must be to the right, so house 4: smoothie=lime
    # Then house 1: smoothie=watermelon
    
    # Now assign remaining cigar: pall mall in 4
    
    # Verify all constraints:
    # 1. prince (2) is desert (2) - yes
    # 2. one house between Eric (2) and Alice (4) - yes (house 3 between)
    # 3. short (1) smokes blends (1) - yes
    # 4. iphone 13 (2) is left of blue master (3) - yes
    # 5. average (5) is dunhill (5) - yes
    # 6. Eric is very tall - yes (2)
    # 7. Arnold (3) is left of huawei p50 (4) - yes
    # 8. Bob not in 4 - yes, in 5
    # 9. Eric (2) is left of cherry (3) - yes
    # 10. Bob is dunhill - yes
    # 11. Bob likes dragonfruit - yes
    # 12. iphone 13 (2) and oneplus 9 (3) next to each other - yes
    # 13. samsung galaxy s21 (1) is short (1) - yes
    # 14. two houses between very tall (2) and dragonfruit (5) - yes (3,4 between)
    # 15. iphone 13 is Eric - yes
    # 16. desert (2) left of lime (4) - yes
    # 17. Arnold (3) and very short (4) next to each other - yes
    
    # Final solution:
    solution = [
        {'House': 1, 'Name': 'Peter', 'Height': 'short', 'Cigar': 'blends', 'Smoothie': 'watermelon', 'PhoneModel': 'samsung galaxy s21'},
        {'House': 2, 'Name': 'Eric', 'Height': 'very tall', 'Cigar': 'prince', 'Smoothie': 'desert', 'PhoneModel': 'iphone 13'},
        {'House': 3, 'Name': 'Arnold', 'Height': 'tall', 'Cigar': 'blue master', 'Smoothie': 'cherry', 'PhoneModel': 'oneplus 9'},
        {'House': 4, 'Name': 'Alice', 'Height': 'very short', 'Cigar': 'pall mall', 'Smoothie': 'lime', 'PhoneModel': 'huawei p50'},
        {'House': 5, 'Name': 'Bob', 'Height': 'average', 'Cigar': 'dunhill', 'Smoothie': 'dragonfruit', 'PhoneModel': 'google pixel 6'}
    ]
    
    # Convert to required JSON format
    output = {
        "solution": {
            "header": ["House", "Name", "Height", "Cigar", "Smoothie", "PhoneModel"],
            "rows": []
        }
    }
    
    for house in solution:
        row = [
            str(house['House']),
            house['Name'],
            house['Height'],
            house['Cigar'],
            house.get('Smoothie', house.get('Smoothie', '')),  # Handle both spellings
            house['PhoneModel']
        ]
        output["solution"]["rows"].append(row)
    
    return json.dumps(output)

print(solve_puzzle())