import json
from itertools import permutations

def main():
    # Define all possible values for each category
    names = ['Arnold', 'Bob', 'Alice', 'Eric', 'Peter']
    heights = ['very tall', 'average', 'tall', 'very short', 'short']
    foods = ['stew', 'grilled cheese', 'spaghetti', 'pizza', 'stir fry']
    houses = [1, 2, 3, 4, 5]
    
    # Generate all possible permutations for each category
    name_perms = list(permutations(names))
    height_perms = list(permutations(heights))
    food_perms = list(permutations(foods))
    
    # Try all combinations until we find one that satisfies all constraints
    for name_assignment in name_perms:
        for height_assignment in height_perms:
            for food_assignment in food_perms:
                # Create assignment dictionaries for each house
                assignment = {}
                for i, house in enumerate(houses):
                    assignment[house] = {
                        'name': name_assignment[i],
                        'height': height_assignment[i],
                        'food': food_assignment[i]
                    }
                
                # Check all constraints
                valid = True
                
                # Clue 1: Alice is the person who is short.
                alice_house = None
                short_house = None
                for house, attrs in assignment.items():
                    if attrs['name'] == 'Alice':
                        alice_house = house
                    if attrs['height'] == 'short':
                        short_house = house
                if alice_house != short_house:
                    valid = False
                
                # Clue 2: The person who is tall is in the third house.
                if assignment[3]['height'] != 'tall':
                    valid = False
                
                # Clue 3: The person who has an average height is not in the second house.
                for house, attrs in assignment.items():
                    if attrs['height'] == 'average' and house == 2:
                        valid = False
                        break
                
                # Clue 4: The person who has an average height is somewhere to the left of the person who loves the stew.
                avg_height_house = None
                stew_house = None
                for house, attrs in assignment.items():
                    if attrs['height'] == 'average':
                        avg_height_house = house
                    if attrs['food'] == 'stew':
                        stew_house = house
                if avg_height_house is None or stew_house is None or avg_height_house >= stew_house:
                    valid = False
                
                # Clue 5: The person who loves stir fry is Arnold.
                for house, attrs in assignment.items():
                    if attrs['food'] == 'stir fry' and attrs['name'] != 'Arnold':
                        valid = False
                        break
                    if attrs['name'] == 'Arnold' and attrs['food'] != 'stir fry':
                        valid = False
                        break
                
                # Clue 6: The person who is a pizza lover is the person who is tall.
                pizza_house = None
                tall_house = None
                for house, attrs in assignment.items():
                    if attrs['food'] == 'pizza':
                        pizza_house = house
                    if attrs['height'] == 'tall':
                        tall_house = house
                if pizza_house != tall_house:
                    valid = False
                
                # Clue 7: Eric is the person who is tall.
                eric_house = None
                for house, attrs in assignment.items():
                    if attrs['name'] == 'Eric':
                        eric_house = house
                if eric_house != tall_house:
                    valid = False
                
                # Clue 8: Bob is somewhere to the right of Arnold.
                arnold_house = None
                bob_house = None
                for house, attrs in assignment.items():
                    if attrs['name'] == 'Arnold':
                        arnold_house = house
                    if attrs['name'] == 'Bob':
                        bob_house = house
                if bob_house <= arnold_house:
                    valid = False
                
                # Clue 9: The person who loves eating grilled cheese is somewhere to the right of Eric.
                grilled_cheese_house = None
                for house, attrs in assignment.items():
                    if attrs['food'] == 'grilled cheese':
                        grilled_cheese_house = house
                if grilled_cheese_house <= eric_house:
                    valid = False
                
                # Clue 10: The person who is very short is somewhere to the left of Arnold.
                very_short_house = None
                for house, attrs in assignment.items():
                    if attrs['height'] == 'very short':
                        very_short_house = house
                if very_short_house >= arnold_house:
                    valid = False
                
                if valid:
                    # Format the solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Height", "Food"],
                            "rows": []
                        }
                    }
                    
                    for house in sorted(assignment.keys()):
                        attrs = assignment[house]
                        solution["solution"]["rows"].append([
                            str(house),
                            attrs['name'],
                            attrs['height'],
                            attrs['food']
                        ])
                    
                    print(json.dumps(solution, indent=2))
                    return
    
    print('No solution found')

if __name__ == "__main__":
    main()