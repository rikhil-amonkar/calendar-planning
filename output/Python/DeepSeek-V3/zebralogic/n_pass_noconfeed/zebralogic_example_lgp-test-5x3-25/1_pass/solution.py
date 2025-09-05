import json
from itertools import permutations

def main():
    # Define all possible values for each category
    names = ["Arnold", "Bob", "Alice", "Eric", "Peter"]
    heights = ["very tall", "average", "tall", "very short", "short"]
    foods = ["stew", "grilled cheese", "spaghetti", "pizza", "stir fry"]
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
                    continue
                
                # Clue 2: The person who is tall is in the third house.
                if assignment[3]['height'] != 'tall':
                    valid = False
                    continue
                
                # Clue 3: The person who has an average height is not in the second house.
                average_house = None
                for house, attrs in assignment.items():
                    if attrs['height'] == 'average':
                        average_house = house
                if average_house == 2:
                    valid = False
                    continue
                
                # Clue 4: The person who has an average height is somewhere to the left of the person who loves the stew.
                stew_house = None
                for house, attrs in assignment.items():
                    if attrs['food'] == 'stew':
                        stew_house = house
                if average_house is None or stew_house is None or average_house >= stew_house:
                    valid = False
                    continue
                
                # Clue 5: The person who loves stir fry is Arnold.
                stir_fry_house = None
                arnold_house = None
                for house, attrs in assignment.items():
                    if attrs['food'] == 'stir fry':
                        stir_fry_house = house
                    if attrs['name'] == 'Arnold':
                        arnold_house = house
                if stir_fry_house != arnold_house:
                    valid = False
                    continue
                
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
                    continue
                
                # Clue 7: Eric is the person who is tall.
                eric_house = None
                for house, attrs in assignment.items():
                    if attrs['name'] == 'Eric':
                        eric_house = house
                if eric_house != tall_house:
                    valid = False
                    continue
                
                # Clue 8: Bob is somewhere to the right of Arnold.
                bob_house = None
                for house, attrs in assignment.items():
                    if attrs['name'] == 'Bob':
                        bob_house = house
                if bob_house <= arnold_house:
                    valid = False
                    continue
                
                # Clue 9: The person who loves eating grilled cheese is somewhere to the right of Eric.
                grilled_cheese_house = None
                for house, attrs in assignment.items():
                    if attrs['food'] == 'grilled cheese':
                        grilled_cheese_house = house
                if grilled_cheese_house <= eric_house:
                    valid = False
                    continue
                
                # Clue 10: The person who is very short is somewhere to the left of Arnold.
                very_short_house = None
                for house, attrs in assignment.items():
                    if attrs['height'] == 'very short':
                        very_short_house = house
                if very_short_house >= arnold_house:
                    valid = False
                    continue
                
                # If we made it here, all constraints are satisfied
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
                    
                    # Output as JSON
                    print(json.dumps(solution, indent=2))
                    return
    
    # If no solution found
    print('{"solution": {"header": ["House", "Name", "Height", "Food"], "rows": []}}')

if __name__ == "__main__":
    main()