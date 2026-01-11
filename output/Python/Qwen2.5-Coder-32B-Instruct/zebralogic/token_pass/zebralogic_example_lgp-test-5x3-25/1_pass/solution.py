import json

def solve_puzzle():
    # Initialize the houses with unknown values
    houses = [{'name': None, 'height': None, 'food': None} for _ in range(5)]

    # Direct assignments from clues
    # Clue 5: Arnold loves stir fry
    for house in houses:
        if house['food'] is None:
            house['food'] = 'stir fry'
            house['name'] = 'Arnold'
            break

    # Clue 6 & 7: Eric is tall and loves pizza, and he is in the third house
    houses[2]['name'] = 'Eric'
    houses[2]['height'] = 'tall'
    houses[2]['food'] = 'pizza'

    # Clue 1: Alice is short
    for house in houses:
        if house['name'] is None and house['height'] is None:
            house['name'] = 'Alice'
            house['height'] = 'short'
            break

    # Positional clues and elimination
    # Clue 10: The very short person is somewhere to the left of Arnold
    arnold_house = next(i for i, house in enumerate(houses) if house['name'] == 'Arnold')
    for i in range(arnold_house):
        if houses[i]['height'] is None:
            houses[i]['height'] = 'very short'
            break

    # Clue 8: Bob is somewhere to the right of Arnold
    for i in range(arnold_house + 1, len(houses)):
        if houses[i]['name'] is None:
            houses[i]['name'] = 'Bob'
            break

    # Clue 9: The grilled cheese lover is somewhere to the right of Eric
    for i in range(3 + 1, len(houses)):
        if houses[i]['food'] is None:
            houses[i]['food'] = 'grilled cheese'
            break

    # Clue 3: The person who has an average height is not in the second house
    # Clue 4: The person who has an average height is somewhere to the left of the person who loves the stew
    stew_house = next(i for i, house in enumerate(houses) if house['food'] is None)
    houses[stew_house]['food'] = 'stew'
    for i in range(stew_house):
        if houses[i]['height'] is None:
            houses[i]['height'] = 'average'
            break

    # Assign remaining values
    remaining_names = {'Peter'}
    remaining_heights = {'very tall', 'average'} - {house['height'] for house in houses if house['height']}
    remaining_foods = {'stew', 'grilled cheese', 'spaghetti', 'pizza', 'stir fry'} - {house['food'] for house in houses if house['food']}
    
    for house in houses:
        if house['name'] is None:
            house['name'] = remaining_names.pop()
        if house['height'] is None:
            house['height'] = remaining_heights.pop()
        if house['food'] is None:
            house['food'] = remaining_foods.pop()

    # Construct the solution in the required format
    solution = {
        "solution": {
            "header": ["House", "Name", "Height", "Food"],
            "rows": [[str(i + 1), house['name'], house['height'], house['food']] for i, house in enumerate(houses)]
        }
    }

    return json.dumps(solution, indent=2)

# Solve the puzzle and print the result
print(solve_puzzle())