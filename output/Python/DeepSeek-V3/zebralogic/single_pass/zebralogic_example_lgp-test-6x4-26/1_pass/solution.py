import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    names = ['Peter', 'Bob', 'Carol', 'Eric', 'Alice', 'Arnold']
    pets = ['bird', 'dog', 'cat', 'rabbit', 'fish', 'hamster']
    house_styles = ['victorian', 'ranch', 'modern', 'mediterranean', 'colonial', 'craftsman']
    months = ['mar', 'sept', 'may', 'feb', 'jan', 'april']
    
    # Initialize houses
    houses = [{'House': str(i+1)} for i in range(6)]
    
    # Apply direct assignments first
    # Clue 3: May is in house 2
    houses[1]['Birthday'] = 'may'
    # Clue 4: colonial is in house 2
    houses[1]['HouseStyle'] = 'colonial'
    # Clue 5: Carol is in house 3
    houses[2]['Name'] = 'Carol'
    # Clue 8: Eric is in house 6
    houses[5]['Name'] = 'Eric'
    # Clue 14: Peter is in colonial (house 2)
    houses[1]['Name'] = 'Peter'
    # Clue 17: Carol's birthday is mar
    houses[2]['Birthday'] = 'mar'
    # Clue 18: craftsman is house 4
    houses[3]['HouseStyle'] = 'craftsman'
    # Clue 19: dog is in house 4
    houses[3]['Pet'] = 'dog'
    # Clue 11: Arnold is in craftsman (house 4)
    houses[3]['Name'] = 'Arnold'
    
    # Determine remaining names: Bob, Alice
    remaining_names = [name for name in names if name not in [house.get('Name') for house in houses]]
    
    # Determine remaining pets: bird, cat, rabbit, fish, hamster
    remaining_pets = [pet for pet in pets if pet not in [house.get('Pet') for house in houses]]
    
    # Determine remaining house styles: victorian, ranch, modern, mediterranean
    remaining_styles = [style for style in house_styles if style not in [house.get('HouseStyle') for house in houses]]
    
    # Determine remaining months: sept, feb, jan, april
    remaining_months = [month for month in months if month not in [house.get('Birthday') for house in houses]]
    
    # Clue 15: jan is directly left of april
    # Possible positions for jan and april:
    # (1,2), (2,3), (3,4), (4,5)
    # But house 2 is may, house 3 is mar, so possible:
    # (1,2) - but 2 is may
    # (4,5)
    # So jan is 4, april is 5
    houses[3]['Birthday'] = 'jan'
    houses[4]['Birthday'] = 'april'
    
    # Clue 2: jan is left of sept
    # jan is in 4, so sept must be 5 or 6
    # But april is in 5, so sept is in 6
    houses[5]['Birthday'] = 'sept'
    
    # Now only feb is left for house 0
    houses[0]['Birthday'] = 'feb'
    
    # Clue 12: colonial (house 2) is left of modern
    # So modern is in 3,4,5, or 6
    # But house 4 is craftsman, house 6 is ?
    # So modern is in 3 or 5
    # house 3 has craftsman, so modern is in 5
    houses[4]['HouseStyle'] = 'modern'
    
    # Clue 16: one house between bird and modern
    # modern is in 5, so bird is in 3 (5-2)
    # house 3 pet is dog, so bird must be in 1 or 2 or 3
    # but house 3 is dog, house 2 pet unknown
    # house 1 pet unknown
    # So bird is in 1 or 2
    # house 2 pet unknown, but house 2 is colonial, no pet info
    # Let's hold this for now
    
    # Clue 9: one house between cat and victorian
    # Possible positions:
    # cat in 1, victorian in 3
    # cat in 2, victorian in 4
    # cat in 3, victorian in 5
    # cat in 4, victorian in 6
    # But house 4 pet is dog, house 3 pet unknown
    # house 5 style is modern, so victorian can't be 5
    # house 6 style unknown
    # So possible:
    # cat in 1, victorian in 3
    # cat in 2, victorian in 4 (but 4 is craftsman)
    # cat in 3, victorian in 5 (5 is modern)
    # cat in 4 (but 4 is dog)
    # So only cat in 1, victorian in 3
    houses[0]['Pet'] = 'cat'
    houses[2]['HouseStyle'] = 'victorian'
    
    # Clue 10: two houses between victorian and hamster
    # victorian is in 3, so hamster is in 6
    houses[5]['Pet'] = 'hamster'
    
    # Clue 1: hamster is right of mar (house 3 is mar), which it is (house 6)
    
    # Clue 7: fish is right of Bob
    # So Bob is left of fish
    # fish could be in 1,2,3,4,5 (but 3 is cat, 4 is dog, 5 is hamster)
    # So fish is in 1 or 2
    # But house 1 pet is cat, so fish is in 2
    houses[1]['Pet'] = 'fish'
    # So Bob must be left of fish (house 2)
    # So Bob is in 1
    houses[0]['Name'] = 'Bob'
    
    # Remaining name is Alice in house 4
    houses[4]['Name'] = 'Alice'
    
    # Now assign remaining pets: bird, rabbit
    # house 0: cat
    # house 1: fish
    # house 2: ?
    # house 3: dog
    # house 4: ?
    # house 5: hamster
    # remaining pets: bird, rabbit
    # From clue 16: one house between bird and modern (modern is 5)
    # So bird is in 3 (5-2)
    houses[2]['Pet'] = 'bird'
    # Then rabbit is in 4
    houses[4]['Pet'] = 'rabbit'
    
    # Now assign remaining house styles: ranch, mediterranean
    # house 0: ?
    # house 1: colonial
    # house 2: victorian
    # house 3: craftsman
    # house 4: modern
    # house 5: ?
    # remaining styles: ranch, mediterranean
    # Clue 6: mediterranean is not in 6, so mediterranean is in 0
    houses[0]['HouseStyle'] = 'ranch'  # Wait, no: mediterranean is not in 6, so could be in 0 or others, but others are assigned
    # Actually, assigned styles:
    # 0: ?
    # 1: colonial
    # 2: victorian
    # 3: craftsman
    # 4: modern
    # 5: ?
    # remaining: ranch, mediterranean
    # mediterranean can't be in 6 (but house 5 is 6th?), no house 6
    # mediterranean is not in 6 (but we have only 6 houses, numbered 1-6, so 6 is index 5)
    # So mediterranean is not in house 5, so it must be in house 0
    houses[0]['HouseStyle'] = 'mediterranean'
    # Then ranch is in house 5
    houses[5]['HouseStyle'] = 'ranch'
    
    # Verify all constraints are satisfied
    # (In a real implementation, you'd want to verify each clue here)
    
    # Prepare the output
    solution = {
        "solution": {
            "header": ["House", "Name", "Pet", "HouseStyle", "Birthday"],
            "rows": []
        }
    }
    
    for house in houses:
        row = [
            house['House'],
            house.get('Name', ''),
            house.get('Pet', ''),
            house.get('HouseStyle', ''),
            house.get('Birthday', '')
        ]
        solution["solution"]["rows"].append(row)
    
    return json.dumps(solution, indent=2)

if __name__ == "__main__":
    print(solve_puzzle())