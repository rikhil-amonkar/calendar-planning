from z3 import *
import json

def main():
    # Create solver
    s = Solver()
    
    # Define the houses
    n = 5
    houses = [1, 2, 3, 4, 5]
    
    # Define attributes with their possible values
    names = ['Arnold', 'Peter', 'Eric', 'Alice', 'Bob']
    hobbies = ['painting', 'cooking', 'knitting', 'gardening', 'photography']
    heights = ['very tall', 'tall', 'very short', 'average', 'short']
    foods = ['stew', 'grilled cheese', 'stir fry', 'spaghetti', 'pizza']
    
    # Create variables for each attribute in each house
    name_vars = [Int(f'name_{i}') for i in houses]
    hobby_vars = [Int(f'hobby_{i}') for i in houses]
    height_vars = [Int(f'height_{i}') for i in houses]
    food_vars = [Int(f'food_{i}') for i in houses]
    
    # Define domains for each variable
    for i in houses:
        s.add(And(name_vars[i-1] >= 0, name_vars[i-1] < len(names)))
        s.add(And(hobby_vars[i-1] >= 0, hobby_vars[i-1] < len(hobbies)))
        s.add(And(height_vars[i-1] >= 0, height_vars[i-1] < len(heights)))
        s.add(And(food_vars[i-1] >= 0, food_vars[i-1] < len(foods)))
    
    # All attributes are distinct within their category
    s.add(Distinct(name_vars))
    s.add(Distinct(hobby_vars))
    s.add(Distinct(height_vars))
    s.add(Distinct(food_vars))
    
    # Create mapping from index to value for easier constraint writing
    name_idx = {name: idx for idx, name in enumerate(names)}
    hobby_idx = {hobby: idx for idx, hobby in enumerate(hobbies)}
    height_idx = {height: idx for idx, height in enumerate(heights)}
    food_idx = {food: idx for idx, food in enumerate(foods)}
    
    # Clue 1: Bob is the photography enthusiast.
    for i in houses:
        s.add(Implies(name_vars[i-1] == name_idx['Bob'], hobby_vars[i-1] == hobby_idx['photography']))
    
    # Clue 2: The person who loves eating grilled cheese is the person who is tall.
    for i in houses:
        s.add(Implies(food_vars[i-1] == food_idx['grilled cheese'], height_vars[i-1] == height_idx['tall']))
    
    # Clue 3: Peter is not in the second house.
    s.add(name_vars[1] != name_idx['Peter'])
    
    # Clue 4: The person who is tall is directly left of the person who loves stir fry.
    for i in range(1, n):
        s.add(Implies(height_vars[i-1] == height_idx['tall'], food_vars[i] == food_idx['stir fry']))
    
    # Clue 5: The person who loves cooking is the person who has an average height.
    for i in houses:
        s.add(Implies(hobby_vars[i-1] == hobby_idx['cooking'], height_vars[i-1] == height_idx['average']))
    
    # Clue 6: Alice is directly left of the person who is a pizza lover.
    for i in range(1, n):
        s.add(Implies(name_vars[i-1] == name_idx['Alice'], food_vars[i] == food_idx['pizza']))
    
    # Clue 7: The person who loves the spaghetti eater is not in the second house.
    s.add(food_vars[1] != food_idx['spaghetti'])
    
    # Clue 8: Eric is not in the fifth house.
    s.add(name_vars[4] != name_idx['Eric'])
    
    # Clue 9: The person who is short is Peter.
    for i in houses:
        s.add(Implies(height_vars[i-1] == height_idx['short'], name_vars[i-1] == name_idx['Peter']))
    
    # Clue 10: The person who has an average height and the person who enjoys gardening are next to each other.
    for i in houses:
        adjacent_gardening = []
        if i > 1:  # Check left neighbor
            adjacent_gardening.append(hobby_vars[i-2] == hobby_idx['gardening'])
        if i < n:  # Check right neighbor
            adjacent_gardening.append(hobby_vars[i] == hobby_idx['gardening'])
        
        if adjacent_gardening:
            s.add(Implies(height_vars[i-1] == height_idx['average'], Or(*adjacent_gardening)))
    
    # Clue 11: The person who paints as a hobby is directly left of the person who loves eating grilled cheese.
    for i in range(1, n):
        s.add(Implies(hobby_vars[i-1] == hobby_idx['painting'], food_vars[i] == food_idx['grilled cheese']))
    
    # Clue 12: The person who is very short is in the fifth house.
    s.add(height_vars[4] == height_idx['very short'])
    
    # Clue 13: The person who is tall is in the third house.
    s.add(height_vars[2] == height_idx['tall'])
    
    # Clue 14: Alice is somewhere to the right of the photography enthusiast.
    # Create a constraint that ensures Alice's house number > photography enthusiast's house number
    alice_house = Int('alice_house')
    photography_house = Int('photography_house')
    
    s.add(alice_house >= 1, alice_house <= 5)
    s.add(photography_house >= 1, photography_house <= 5)
    
    # Link the variables to actual positions
    for i in houses:
        s.add(Implies(name_vars[i-1] == name_idx['Alice'], alice_house == i))
        s.add(Implies(hobby_vars[i-1] == hobby_idx['photography'], photography_house == i))
    
    s.add(alice_house > photography_house)
    
    # Check if satisfiable
    if s.check() == sat:
        model = s.model()
        
        # Extract the solution
        solution = {"solution": {"header": ["House", "Name", "Hobby", "Height", "Food"], "rows": []}}
        
        for i in houses:
            house_num = str(i)
            name_val = names[model.evaluate(name_vars[i-1]).as_long()]
            hobby_val = hobbies[model.evaluate(hobby_vars[i-1]).as_long()]
            height_val = heights[model.evaluate(height_vars[i-1]).as_long()]
            food_val = foods[model.evaluate(food_vars[i-1]).as_long()]
            
            solution["solution"]["rows"].append([house_num, name_val, hobby_val, height_val, food_val])
        
        print(json.dumps(solution, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()