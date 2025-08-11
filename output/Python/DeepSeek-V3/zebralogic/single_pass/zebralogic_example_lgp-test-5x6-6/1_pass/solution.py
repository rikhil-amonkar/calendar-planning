import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    houses = ['1', '2', '3', '4', '5']
    names = ['Arnold', 'Eric', 'Alice', 'Bob', 'Peter']
    vacations = ['mountain', 'city', 'cruise', 'beach', 'camping']
    educations = ['doctorate', 'high school', 'bachelor', 'associate', 'master']
    colors = ['blue', 'red', 'white', 'yellow', 'green']
    phones = ['google pixel 6', 'iphone 13', 'oneplus 9', 'huawei p50', 'samsung galaxy s21']
    lunches = ['grilled cheese', 'stir fry', 'pizza', 'spaghetti', 'stew']

    # Initialize possible assignments
    from collections import defaultdict
    possibilities = []
    for house in houses:
        possibilities.append({
            'House': house,
            'Name': names.copy(),
            'Vacation': vacations.copy(),
            'Education': educations.copy(),
            'Color': colors.copy(),
            'Phone': phones.copy(),
            'Lunch': lunches.copy()
        })

    # Apply clues one by one
    # Clue 5 & 7: The person who uses a Samsung Galaxy S21 is in the third house and has a doctorate
    for i in range(5):
        if possibilities[i]['House'] == '3':
            possibilities[i]['Phone'] = ['samsung galaxy s21']
            possibilities[i]['Education'] = ['doctorate']
            possibilities[i]['Name'].remove('Eric')  # Because Eric is the one with doctorate (Clue 6)
            possibilities[i]['Name'] = ['Eric']
            possibilities[i]['Lunch'] = ['pizza']  # Clue 9
        else:
            if 'samsung galaxy s21' in possibilities[i]['Phone']:
                possibilities[i]['Phone'].remove('samsung galaxy s21')
            if 'doctorate' in possibilities[i]['Education']:
                possibilities[i]['Education'].remove('doctorate')
            if 'Eric' in possibilities[i]['Name']:
                possibilities[i]['Name'].remove('Eric')
            if 'pizza' in possibilities[i]['Lunch']:
                possibilities[i]['Lunch'].remove('pizza')

    # Clue 13: One house between high school and samsung galaxy s21 (house 3)
    # So high school is in house 1 (since 1 and 3 have two houses between, but house 3 is samsung)
    for i in range(5):
        if possibilities[i]['House'] == '1':
            possibilities[i]['Education'] = ['high school']
        else:
            if 'high school' in possibilities[i]['Education']:
                possibilities[i]['Education'].remove('high school')

    # Clue 8: stir fry is bachelor's degree
    # Clue 3: mountain retreat is bachelor's degree
    # So stir fry is mountain retreat
    # Clue 2: two houses between stir fry and associate
    # So if stir fry is in 1, associate is in 4
    # or stir fry in 2, associate in 5
    # But house 1 has high school, not bachelor, so stir fry must be in 2, associate in 5
    for i in range(5):
        if possibilities[i]['House'] == '2':
            possibilities[i]['Lunch'] = ['stir fry']
            possibilities[i]['Education'] = ['bachelor']
            possibilities[i]['Vacation'] = ['mountain']
        elif possibilities[i]['House'] == '5':
            possibilities[i]['Education'] = ['associate']
        else:
            if 'stir fry' in possibilities[i]['Lunch']:
                possibilities[i]['Lunch'].remove('stir fry')
            if 'bachelor' in possibilities[i]['Education'] and possibilities[i]['House'] != '2':
                possibilities[i]['Education'].remove('bachelor')
            if 'mountain' in possibilities[i]['Vacation'] and possibilities[i]['House'] != '2':
                possibilities[i]['Vacation'].remove('mountain')
            if 'associate' in possibilities[i]['Education'] and possibilities[i]['House'] != '5':
                possibilities[i]['Education'].remove('associate')

    # Clue 18: two houses between bachelor (house 2) and red
    # So red is in house 5
    for i in range(5):
        if possibilities[i]['House'] == '5':
            possibilities[i]['Color'] = ['red']
        else:
            if 'red' in possibilities[i]['Color']:
                possibilities[i]['Color'].remove('red')

    # Clue 4: doctorate is right of Bob, so Bob is left of house 3
    for i in range(5):
        if possibilities[i]['House'] in ['1', '2']:
            if 'Bob' not in possibilities[i]['Name']:
                possibilities[i]['Name'].remove('Bob')
        else:
            if 'Bob' in possibilities[i]['Name']:
                possibilities[i]['Name'].remove('Bob')

    # Clue 10: green is right of Peter, so Peter is left of green
    # Clue 21: blue is right of Peter, so Peter is left of blue
    # So Peter is left of both green and blue
    # Clue 20: green not in house 2
    # So green is in 3,4,5, but 5 is red, so green is 3 or 4
    # But house 3 color not yet assigned, but house 5 is red
    # Peter must be left of green, so if green is 3, Peter is 1 or 2
    # if green is 4, Peter is 1,2, or 3

    # Clue 14: Arnold uses google pixel 6
    # Clue 16: Arnold loves grilled cheese
    # Clue 17: grilled cheese not in house 4
    # So Arnold is not in house 4
    for i in range(5):
        if 'Arnold' in possibilities[i]['Name']:
            possibilities[i]['Phone'] = ['google pixel 6']
            possibilities[i]['Lunch'] = ['grilled cheese']
            if possibilities[i]['House'] == '4':
                possibilities[i]['Name'].remove('Arnold')
        else:
            if 'google pixel 6' in possibilities[i]['Phone']:
                possibilities[i]['Phone'].remove('google pixel 6')
            if 'grilled cheese' in possibilities[i]['Lunch']:
                possibilities[i]['Lunch'].remove('grilled cheese')

    # Clue 11: camping is iphone 13
    # Clue 22: one house between camping and yellow
    # So if camping is 1, yellow is 3
    # camping 2, yellow 4
    # camping 3, yellow 5
    # camping cannot be 4 or 5 because need house after
    # But house 3 phone is samsung, not iphone, so camping not 3
    # So camping is 1 or 2, yellow is 3 or 4
    # house 3 color could be yellow
    # house 4 color could be yellow

    # Clue 12: cruise is Alice
    for i in range(5):
        if 'Alice' in possibilities[i]['Name']:
            possibilities[i]['Vacation'] = ['cruise']
        else:
            if 'cruise' in possibilities[i]['Vacation']:
                possibilities[i]['Vacation'].remove('cruise')

    # Clue 19: beach is right of city
    # So city is left of beach

    # Clue 15: oneplus 9 is right of huawei p50
    # So huawei is left of oneplus

    # Clue 1: stew not in house 1
    for i in range(5):
        if possibilities[i]['House'] == '1':
            if 'stew' in possibilities[i]['Lunch']:
                possibilities[i]['Lunch'].remove('stew')

    # Now let's try to assign Arnold
    # Arnold must be in house 1, 2, 3, or 5 (not 4 because grilled cheese not in 4)
    # But house 3 is Eric, so Arnold is 1, 2, or 5
    # house 1 has high school, name could be Arnold
    # house 2 name could be Arnold
    # house 5 name could be Arnold
    # Let's assume Arnold is in house 1
    # Then house 1 name is Arnold
    for i in range(5):
        if possibilities[i]['House'] == '1':
            possibilities[i]['Name'] = ['Arnold']
            possibilities[i]['Phone'] = ['google pixel 6']
            possibilities[i]['Lunch'] = ['grilled cheese']
        else:
            if 'Arnold' in possibilities[i]['Name']:
                possibilities[i]['Name'].remove('Arnold')

    # Then house 1 name is Arnold, phone is google, lunch is grilled cheese
    # house 2 name is not Arnold, possible names: Bob, Alice, Peter
    # house 3 name is Eric
    # house 4 and 5 names: remaining from Alice, Bob, Peter

    # house 1 education is high school
    # house 2 education is bachelor
    # house 3 is doctorate
    # house 5 is associate
    # so house 4 is master
    for i in range(5):
        if possibilities[i]['House'] == '4':
            possibilities[i]['Education'] = ['master']
        elif possibilities[i]['House'] == '5':
            possibilities[i]['Education'] = ['associate']
        else:
            if 'master' in possibilities[i]['Education'] and possibilities[i]['House'] != '4':
                possibilities[i]['Education'].remove('master')
            if 'associate' in possibilities[i]['Education'] and possibilities[i]['House'] != '5':
                possibilities[i]['Education'].remove('associate')

    # house 2 name: Bob, Alice, or Peter
    # But Alice is cruise (clue 12), so if Alice is in house 2, vacation is cruise
    # But house 2 vacation is mountain (from clue 3 and 8), so Alice cannot be in house 2
    # So house 2 name is Bob or Peter
    for i in range(5):
        if possibilities[i]['House'] == '2':
            if 'Alice' in possibilities[i]['Name']:
                possibilities[i]['Name'].remove('Alice')

    # house 4 and 5 names: remaining from Alice, Bob, Peter
    # house 2 is Bob or Peter
    # house 4 and 5 must have Alice if not in house 2
    # So if house 2 is Bob, then house 4 or 5 is Alice and Peter
    # Or if house 2 is Peter, then house 4 or 5 is Alice and Bob
    # But Bob must be left of doctorate (house 3), so Bob is in house 1 or 2
    # house 1 is Arnold, so Bob is in house 2
    # So house 2 name is Bob
    for i in range(5):
        if possibilities[i]['House'] == '2':
            possibilities[i]['Name'] = ['Bob']
        else:
            if 'Bob' in possibilities[i]['Name']:
                possibilities[i]['Name'].remove('Bob')

    # Then house 4 and 5 names are Alice and Peter
    # house 3 is Eric
    # house 1 is Arnold
    # house 2 is Bob

    # Now assign Alice and Peter to houses 4 and 5
    # Alice is cruise (clue 12)
    # So Alice must be in house where vacation is cruise
    # house 4 or 5 vacation: remaining options are city, beach, camping
    # cruise is not assigned yet, but house 2 is mountain, others?
    # house 2 is mountain, others not assigned
    # So Alice must be in house where vacation is cruise, but cruise not assigned yet
    # Wait, vacation options: mountain (house 2), cruise (Alice), others: city, beach, camping
    # So Alice must be in house where vacation is cruise
    # So assign cruise to house 4 or 5 where Alice is
    for i in range(5):
        if possibilities[i]['House'] in ['4', '5']:
            if 'Alice' in possibilities[i]['Name']:
                possibilities[i]['Vacation'] = ['cruise']
            else:
                if 'cruise' in possibilities[i]['Vacation']:
                    possibilities[i]['Vacation'].remove('cruise')

    # Now assign Peter
    # Peter is in house 4 or 5, not Alice
    # So if Alice is in 4, Peter is in 5
    # Or Alice in 5, Peter in 4
    # Let's try Alice in 4, Peter in 5
    possibilities[3]['Name'] = ['Alice']
    possibilities[3]['Vacation'] = ['cruise']
    possibilities[4]['Name'] = ['Peter']
    # Remove Alice from house 5 and Peter from house 4
    possibilities[4]['Name'] = ['Peter']
    if 'Alice' in possibilities[4]['Name']:
        possibilities[4]['Name'].remove('Alice')
    if 'Peter' in possibilities[3]['Name']:
        possibilities[3]['Name'].remove('Peter')

    # Now assign colors
    # house 5 is red
    # green is right of Peter (house 5 is Peter, but green must be right of Peter, but no house right of 5)
    # Contradiction, so Alice must be in 5, Peter in 4
    # Reset names
    possibilities[3]['Name'] = ['Peter']
    possibilities[4]['Name'] = ['Alice']
    possibilities[4]['Vacation'] = ['cruise']
    possibilities[3]['Vacation'] = [v for v in possibilities[3]['Vacation'] if v != 'cruise']

    # Now green is right of Peter (house 4), so green is house 5
    # But house 5 color is red (from clue 18), contradiction
    # So green must be in house 3 or 4
    # Peter is in house 4, so green is right of Peter means green is house 5
    # But house 5 is red, so no solution this way
    # Alternative: Peter is not in house 4, but earlier logic forced Peter to be in 4 or 5
    # Maybe initial assumption that Arnold is in house 1 is wrong
    # Let's try Arnold in house 2
    # Reset possibilities
    possibilities = []
    for house in houses:
        possibilities.append({
            'House': house,
            'Name': names.copy(),
            'Vacation': vacations.copy(),
            'Education': educations.copy(),
            'Color': colors.copy(),
            'Phone': phones.copy(),
            'Lunch': lunches.copy()
        })

    # Reapply clues with Arnold in house 2
    # House 3: samsung, doctorate, Eric, pizza
    for i in range(5):
        if possibilities[i]['House'] == '3':
            possibilities[i]['Phone'] = ['samsung galaxy s21']
            possibilities[i]['Education'] = ['doctorate']
            possibilities[i]['Name'] = ['Eric']
            possibilities[i]['Lunch'] = ['pizza']
        else:
            if 'samsung galaxy s21' in possibilities[i]['Phone']:
                possibilities[i]['Phone'].remove('samsung galaxy s21')
            if 'doctorate' in possibilities[i]['Education']:
                possibilities[i]['Education'].remove('doctorate')
            if 'Eric' in possibilities[i]['Name']:
                possibilities[i]['Name'].remove('Eric')
            if 'pizza' in possibilities[i]['Lunch']:
                possibilities[i]['Lunch'].remove('pizza')

    # Clue 13: high school in house 1
    for i in range(5):
        if possibilities[i]['House'] == '1':
            possibilities[i]['Education'] = ['high school']
        else:
            if 'high school' in possibilities[i]['Education']:
                possibilities[i]['Education'].remove('high school')

    # Clue 8,3: stir fry is bachelor and mountain, in house 2 or 4 (because two houses to associate)
    # associate is in house 5 if stir fry is 2
    # or associate is not possible if stir fry is 3, but 3 is doctorate
    # So stir fry is in 2, associate in 5
    for i in range(5):
        if possibilities[i]['House'] == '2':
            possibilities[i]['Lunch'] = ['stir fry']
            possibilities[i]['Education'] = ['bachelor']
            possibilities[i]['Vacation'] = ['mountain']
        elif possibilities[i]['House'] == '5':
            possibilities[i]['Education'] = ['associate']
        else:
            if 'stir fry' in possibilities[i]['Lunch'] and possibilities[i]['House'] != '2':
                possibilities[i]['Lunch'].remove('stir fry')
            if 'bachelor' in possibilities[i]['Education'] and possibilities[i]['House'] != '2':
                possibilities[i]['Education'].remove('bachelor')
            if 'mountain' in possibilities[i]['Vacation'] and possibilities[i]['House'] != '2':
                possibilities[i]['Vacation'].remove('mountain')
            if 'associate' in possibilities[i]['Education'] and possibilities[i]['House'] != '5':
                possibilities[i]['Education'].remove('associate')

    # Clue 18: two houses between bachelor (house 2) and red, so red is house 5
    for i in range(5):
        if possibilities[i]['House'] == '5':
            possibilities[i]['Color'] = ['red']
        else:
            if 'red' in possibilities[i]['Color']:
                possibilities[i]['Color'].remove('red')

    # Clue 4: doctorate is right of Bob, so Bob is left of house 3 (house 1 or 2)
    for i in range(5):
        if possibilities[i]['House'] not in ['1', '2']:
            if 'Bob' in possibilities[i]['Name']:
                possibilities[i]['Name'].remove('Bob')

    # Clue 14: Arnold uses google pixel 6
    # Clue 16: Arnold loves grilled cheese
    # Clue 17: grilled cheese not in house 4
    # Let's place Arnold in house 2
    for i in range(5):
        if possibilities[i]['House'] == '2':