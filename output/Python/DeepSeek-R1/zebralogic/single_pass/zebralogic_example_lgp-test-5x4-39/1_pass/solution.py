import json

def main():
    state = {
        'name': {1: None, 2: None, 3: None, 4: None, 5: None},
        'hobby': {1: None, 2: None, 3: None, 4: None, 5: None},
        'height': {1: None, 2: None, 3: None, 4: None, 5: None},
        'lunch': {1: None, 2: None, 3: None, 4: None, 5: None}
    }
    
    steps = [
        ('height', 3, 'tall'),           # Clue 13
        ('height', 5, 'very short'),      # Clue 12
        ('lunch', 3, 'grilled cheese'),   # Clue 2 and 13
        ('lunch', 4, 'stir fry'),         # Clue 4
        ('hobby', 2, 'painting'),         # Clue 11
        ('lunch', 5, 'pizza'),            # Clue 6 and above assignments
        ('name', 4, 'Alice'),             # Clue 6
        ('lunch', 2, 'stew'),             # Remaining lunches and Clue 7
        ('lunch', 1, 'spaghetti'),        # Last remaining lunch
        ('name', 1, 'Peter'),             # Clue 3, 9, and above
        ('height', 1, 'short'),           # Clue 9
        ('height', 2, 'very tall'),       # Remaining heights
        ('height', 4, 'average'),         # Clue 5 and above
        ('hobby', 4, 'cooking'),          # Clue 5
        ('hobby', 3, 'photography'),      # Clue 1 and 14
        ('name', 3, 'Bob'),               # Clue 1
        ('hobby', 1, 'knitting'),         # Remaining hobbies
        ('hobby', 5, 'gardening'),        # Clue 10
        ('name', 2, 'Eric'),              # Clue 8 and remaining names
        ('name', 5, 'Arnold')             # Last remaining name
    ]
    
    for step in steps:
        attr, house, value = step
        state[attr][house] = value
    
    solution = {
        "solution": {
            "header": ["House", "Name", "Hobby", "Height", "Lunch"],
            "rows": []
        }
    }
    
    for house in range(1, 6):
        row = [
            str(house),
            state['name'][house],
            state['hobby'][house],
            state['height'][house],
            state['lunch'][house]
        ]
        solution["solution"]["rows"].append(row)
    
    print(json.dumps(solution, indent=2))

if __name__ == "__main__":
    main()