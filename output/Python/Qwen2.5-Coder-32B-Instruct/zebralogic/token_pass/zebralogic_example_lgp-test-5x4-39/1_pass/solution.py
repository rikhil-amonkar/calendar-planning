import itertools
import json

# Define the domains for each attribute
names = ['Arnold', 'Peter', 'Eric', 'Alice', 'Bob']
hobbies = ['painting', 'cooking', 'knitting', 'gardening', 'photography']
heights = ['very tall', 'tall', 'very short', 'average', 'short']
foods = ['stew', 'grilled cheese', 'stir fry', 'spaghetti', 'pizza']

# Initialize the houses with all possible assignments
houses = [{'name': names[:], 'hobby': hobbies[:], 'height': heights[:], 'food': foods[:]} for _ in range(5)]

def is_consistent(houses):
    # Check all constraints
    for i in range(5):
        house = houses[i]
        
        # Constraint 1: Bob is the photography enthusiast.
        if 'Bob' in house['name'] and 'photography' not in house['hobby']:
            return False
        if 'photography' in house['hobby'] and 'Bob' not in house['name']:
            return False
        
        # Constraint 2: The person who loves eating grilled cheese is the person who is tall.
        if 'grilled cheese' in house['food'] and 'tall' not in house['height']:
            return False
        if 'tall' in house['height'] and 'grilled cheese' not in house['food']:
            return False
        
        # Constraint 3: Peter is not in the second house.
        if i == 1 and 'Peter' in house['name']:
            return False
        
        # Constraint 4: The person who is tall is directly left of the person who loves stir fry.
        if i < 4 and 'tall' in house['height'] and 'stir fry' in houses[i + 1]['food']:
            return False
        if i > 0 and 'stir fry' in house['food'] and 'tall' in houses[i - 1]['height']:
            return False
        
        # Constraint 5: The person who loves cooking is the person who has an average height.
        if 'cooking' in house['hobby'] and 'average' not in house['height']:
            return False
        if 'average' in house['height'] and 'cooking' not in house['hobby']:
            return False
        
        # Constraint 6: Alice is directly left of the person who is a pizza lover.
        if i < 4 and 'Alice' in house['name'] and 'pizza' in houses[i + 1]['food']:
            return False
        if i > 0 and 'pizza' in house['food'] and 'Alice' in houses[i - 1]['name']:
            return False
        
        # Constraint 7: The person who loves the spaghetti eater is not in the second house.
        if i == 1 and 'spaghetti' in house['food']:
            return False
        
        # Constraint 8: Eric is not in the fifth house.
        if i == 4 and 'Eric' in house['name']:
            return False
        
        # Constraint 9: The person who is short is Peter.
        if 'short' in house['height'] and 'Peter' not in house['name']:
            return False
        if 'Peter' in house['name'] and 'short' not in house['height']:
            return False
        
        # Constraint 10: The person who has an average height and the person who enjoys gardening are next to each other.
        if i < 4 and ('average' in house['height'] or 'gardening' in house['hobby']) and ('average' in houses[i + 1]['height'] or 'gardening' in houses[i + 1]['hobby']):
            if not (('average' in house['height'] and 'gardening' in houses[i + 1]['hobby']) or ('gardening' in house['hobby'] and 'average' in houses[i + 1]['height'])):
                return False
        if i > 0 and ('average' in house['height'] or 'gardening' in house['hobby']) and ('average' in houses[i - 1]['height'] or 'gardening' in houses[i - 1]['hobby']):
            if not (('average' in house['height'] and 'gardening' in houses[i - 1]['hobby']) or ('gardening' in house['hobby'] and 'average' in houses[i - 1]['height'])):
                return False
        
        # Constraint 11: The person who paints as a hobby is directly left of the person who loves eating grilled cheese.
        if i < 4 and 'painting' in house['hobby'] and 'grilled cheese' in houses[i + 1]['food']:
            return False
        if i > 0 and 'grilled cheese' in house['food'] and 'painting' in houses[i - 1]['hobby']:
            return False
        
        # Constraint 12: The person who is very short is in the fifth house.
        if i == 4 and 'very short' not in house['height']:
            return False
        if i != 4 and 'very short' in house['height']:
            return False
        
        # Constraint 13: The person who is tall is in the third house.
        if i == 2 and 'tall' not in house['height']:
            return False
        if i != 2 and 'tall' in house['height']:
            return False
        
        # Constraint 14: Alice is somewhere to the right of the photography enthusiast.
        if 'Alice' in house['name']:
            for j in range(i):
                if 'photography' in houses[j]['hobby']:
                    return False
    
    return True

def solve(houses, index=0):
    if index == 5:
        if is_consistent(houses):
            return houses
        else:
            return None
    
    for name in houses[index]['name'][:]:
        for hobby in houses[index]['hobby'][:]:
            for height in houses[index]['height'][:]:
                for food in houses[index]['food'][:]:
                    houses[index] = {'name': [name], 'hobby': [hobby], 'height': [height], 'food': [food]}
                    if is_consistent(houses):
                        result = solve(houses, index + 1)
                        if result is not None:
                            return result
                    houses[index] = {'name': names[:], 'hobby': hobbies[:], 'height': heights[:], 'food': foods[:]}
    
    return None

solution = solve(houses)

# Format the solution as required
formatted_solution = {
    "solution": {
        "header": ["House", "Name", "Hobby", "Height", "Food"],
        "rows": [
            [str(i + 1), solution[i]['name'][0], solution[i]['hobby'][0], solution[i]['height'][0], solution[i]['food'][0]]
            for i in range(5)
        ]
    }
}

print(json.dumps(formatted_solution, indent=2))