import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values for each category
    names = ['Peter', 'Alice', 'Eric', 'Bob', 'Arnold']
    months = ['april', 'feb', 'mar', 'jan', 'sept']
    cigars = ['pall mall', 'prince', 'dunhill', 'blends', 'blue master']
    drinks = ['water', 'coffee', 'tea', 'milk', 'root beer']
    
    # Initialize houses
    houses = [{'House': str(i+1), 'Name': None, 'Birthday': None, 'Cigar': None, 'Drink': None} for i in range(5)]
    
    # Apply clue 13: Eric is in the third house
    houses[2]['Name'] = 'Eric'
    # Apply clue 1: The root beer lover is Eric
    houses[2]['Drink'] = 'root beer'
    # Apply clue 2: The person partial to Pall Mall is in the third house
    houses[2]['Cigar'] = 'pall mall'
    # Apply clue 8: The person whose birthday is in February is in the second house
    houses[1]['Birthday'] = 'feb'
    # Apply clue 7: The person who smokes blends is the person whose birthday is in February
    houses[1]['Cigar'] = 'blends'
    # Apply clue 4: The Dunhill smoker is the person whose birthday is in March
    # We'll apply this after determining the March birthday
    # Apply clue 3: The person whose birthday is in April is Bob
    # Apply clue 5: Peter is somewhere to the right of the root beer lover (house 3)
    # So Peter is in house 4 or 5
    # Apply clue 6: There is one house between the person whose birthday is in January and Peter
    # So if Peter is in 4, jan is in 2. But 2 is feb, so Peter must be in 5, jan in 3
    # But 3's birthday is not yet assigned, but Eric is in 3, and Bob is april (clue 3)
    # So jan must be in 3, but Eric is in 3, and names are unique, so jan can't be in 3 if Eric is there
    # Wait, names and months are separate, so jan can be in 3 even if Eric is there
    # So Peter is in 5, jan is in 3
    houses[4]['Name'] = 'Peter'
    houses[2]['Birthday'] = 'jan'
    # Apply clue 9: Arnold is directly left of Peter (so Arnold is in 4)
    houses[3]['Name'] = 'Arnold'
    # Now assign remaining names: Alice and Bob
    # From clue 3: Bob's birthday is april
    # Possible positions: 0 or 1 (since 2 is jan, 3 is ?, 4 is Peter, 5 is Arnold)
    # But house 1's month is not assigned yet, house 0's month is not assigned
    # From clue 4: Dunhill smoker's birthday is mar
    # From clue 7: feb is in 2 with blends
    # From clue 8: feb is in 2
    # From months left: april, mar, sept (since jan is in 3, feb in 2)
    # Bob is april, so assign Bob to house 0 or 1 with april
    # house 1's month is feb, so Bob must be in house 0 with april
    houses[0]['Name'] = 'Bob'
    houses[0]['Birthday'] = 'april'
    # Remaining name is Alice in house 1
    houses[1]['Name'] = 'Alice'
    # Now assign months: house 3 and 4 left
    # Remaining months: mar, sept
    # From clue 4: Dunhill smoker's birthday is mar
    # So mar must be in house with dunhill
    # Possible positions: 3 or 4
    # From clue 10: milk is not in 5, so milk is in 0-4
    # From drinks assigned: root beer in 3, others not assigned
    # From clue 11: blue master smoker is coffee drinker
    # From clue 12: one house between tea and coffee
    # From drinks left: water, coffee, tea, milk
    # milk is not in 5, so possible in 0,1,3 (2 is root beer)
    # house 0: drink not assigned
    # house 1: drink not assigned
    # house 3: drink not assigned
    # house 4: drink not assigned
    # Let's assign months first
    # Assign mar to 3 or 4
    # If mar is in 3:
    # Then house 3 has birthday mar, cigar dunhill (from clue 4)
    houses[3]['Birthday'] = 'mar'
    houses[3]['Cigar'] = 'dunhill'
    # Then house 4's birthday is sept
    houses[4]['Birthday'] = 'sept'
    # Now assign drinks
    # milk is not in 5, so possible in 0,1,3
    # house 3: no drink assigned, but let's see other clues
    # clue 11: blue master smoker is coffee drinker
    # clue 12: one house between tea and coffee
    # possible assignments:
    # tea in 0, coffee in 2 (but 2 is root beer), no
    # tea in 1, coffee in 3
    # tea in 2 is root beer, no
    # tea in 3, coffee in 5 (but 5 is not assigned yet)
    # So only possible is tea in 1, coffee in 3
    houses[1]['Drink'] = 'tea'
    houses[3]['Drink'] = 'coffee'
    # Then from clue 11: blue master smoker is coffee drinker (house 3)
    houses[3]['Cigar'] = 'blue master'
    # But earlier we assigned dunhill to house 3, contradiction
    # So our assumption that mar is in 3 is wrong
    # So mar must be in 4
    # Reset house 3 and 4 assignments
    houses[3]['Birthday'] = None
    houses[3]['Cigar'] = None
    houses[4]['Birthday'] = None
    # Assign mar to 4
    houses[4]['Birthday'] = 'mar'
    houses[4]['Cigar'] = 'dunhill'
    # Then house 3's birthday is sept
    houses[3]['Birthday'] = 'sept'
    # Now assign drinks
    # milk is not in 5, so possible in 0,1,3
    # clue 12: one house between tea and coffee
    # possibilities:
    # tea in 0, coffee in 2 (but 2 is root beer), no
    # tea in 1, coffee in 3
    # tea in 2 is root beer, no
    # tea in 3, coffee in 5
    # So possible: tea in 1, coffee in 3
    houses[1]['Drink'] = 'tea'
    houses[3]['Drink'] = 'coffee'
    # From clue 11: blue master smoker is coffee drinker (house 3)
    houses[3]['Cigar'] = 'blue master'
    # Now assign remaining cigars
    # Assigned cigars: house 1 blends, house 2 pall mall, house 3 blue master, house 4 dunhill
    # Remaining cigar: prince
    # So house 0 has prince
    houses[0]['Cigar'] = 'prince'
    # Now assign remaining drinks
    # Assigned drinks: house 1 tea, house 2 root beer, house 3 coffee
    # Remaining drinks: water, milk
    # milk is not in 5, so milk is in 0
    houses[0]['Drink'] = 'milk'
    # Then house 4's drink is water
    houses[4]['Drink'] = 'water'
    
    # Prepare the solution in the required format
    solution = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Cigar", "Drink"],
            "rows": []
        }
    }
    
    for house in houses:
        row = [
            house['House'],
            house['Name'],
            house['Birthday'],
            house['Cigar'],
            house['Drink']
        ]
        solution["solution"]["rows"].append(row)
    
    return json.dumps(solution, indent=2)

print(solve_puzzle())