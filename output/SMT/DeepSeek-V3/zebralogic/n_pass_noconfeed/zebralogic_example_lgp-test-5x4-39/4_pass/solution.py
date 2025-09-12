from z3 import *
import json

def main():
    # Create solver
    s = Solver()
    
    # Define the houses
    n = 5
    houses = [0, 1, 2, 3, 4]  # Use 0-indexing for easier array access
    
    # Define attributes with their possible values
    names = ['Arnold', 'Peter', 'Eric', 'Alice', 'Bob']
    hobbies = ['painting', 'cooking', 'knitting', 'gardening', 'photography']
    heights = ['very tall', 'tall', 'very short', 'average', 'short']
    foods = ['stew', 'grilled cheese', 'stir fry', 'spaghetti', 'pizza']
    
    # Create variables for each attribute in each house
    name_vars = [Int(f'name_{i}') for i in range(n)]
    hobby_vars = [Int(f'hobby_{i}') for i in range(n)]
    height_vars = [Int(f'height_{i}') for i in range(n)]
    food_vars = [Int(f'food_{i}') for i in range(n)]
    
    # Define domains for each variable
    for i in range(n):
        s.add(And(name_vars[i] >= 0, name_vars[i] < len(names)))
        s.add(And(hobby_vars[i] >= 0, hobby_vars[i] < len(hobbies)))
        s.add(And(height_vars[i] >= 0, height_vars[i] < len(heights)))
        s.add(And(food_vars[i] >= 0, food_vars[i] < len(foods)))
    
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
    for i in range(n):
        s.add(Implies(name_vars[i] == name_idx['Bob'], hobby_vars[i] == hobby_idx['photography']))
    
    # Clue 2: The person who loves eating grilled cheese is the person who is tall.
    for i in range(n):
        s.add(Implies(food_vars[i] == food_idx['grilled cheese'], height_vars[i] == height_idx['tall']))
    
    # Clue 3: Peter is not in the second house.
    s.add(name_vars[1] != name_idx['Peter'])
    
    # Clue 4: The person who is tall is directly left of the person who loves stir fry.
    for i in range(n-1):
        s.add(Implies(height_vars[i] == height_idx['tall'], food_vars[i+1] == food_idx['stir fry']))
    
    # Clue 5: The person who loves cooking is the person who has an average height.
    for i in range(n):
        s.add(Implies(hobby_vars[i] == hobby_idx['cooking'], height_vars[i] == height_idx['average']))
    
    # Clue 6: Alice is directly left of the person who is a pizza lover.
    for i in range(n-1):
        s.add(Implies(name_vars[i] == name_idx['Alice'], food_vars[i+1] == food_idx['pizza']))
    
    # Clue 7: The person who loves the spaghetti eater is not in the second house.
    # This means the spaghetti eater is not in house 2 (index 1)
    s.add(food_vars[1] != food_idx['spaghetti'])
    
    # Clue 8: Eric is not in the fifth house.
    s.add(name_vars[4] != name_idx['Eric'])
    
    # Clue 9: The person who is short is Peter.
    for i in range(n):
        s.add(Implies(height_vars[i] == height_idx['short'], name_vars[i] == name_idx['Peter']))
    
    # Clue 10: The person who has an average height and the person who enjoys gardening are next to each other.
    for i in range(n):
        adjacent_conditions = []
        if i > 0:
            adjacent_conditions.append(And(height_vars[i] == height_idx['average'], hobby_vars[i-1] == hobby_idx['gardening']))
            adjacent_conditions.append(And(hobby_vars[i] == hobby_idx['gardening'], height_vars[i-1] == height_idx['average']))
        if i < n-1:
            adjacent_conditions.append(And(height_vars[i] == height_idx['average'], hobby_vars[i+1] == hobby_idx['gardening']))
            adjacent_conditions.append(And(hobby_vars[i] == hobby_idx['gardening'], height_vars[i+1] == height_idx['average']))
        
        if adjacent_conditions:
            s.add(Or(*adjacent_conditions))
    
    # Clue 11: The person who paints as a hobby is directly left of the person who loves eating grilled cheese.
    for i in range(n-1):
        s.add(Implies(hobby_vars[i] == hobby_idx['painting'], food_vars[i+1] == food_idx['grilled cheese']))
    
    # Clue 12: The person who is very short is in the fifth house.
    s.add(height_vars[4] == height_idx['very short'])
    
    # Clue 13: The person who is tall is in the third house.
    s.add(height_vars[2] == height_idx['tall'])
    
    # Clue 14: Alice is somewhere to the right of the photography enthusiast.
    alice_pos = Int('alice_pos')
    photography_pos = Int('photography_pos')
    s.add(alice_pos >= 0, alice_pos < n)
    s.add(photography_pos >= 0, photography_pos < n)
    
    for i in range(n):
        s.add(Implies(name_vars[i] == name_idx['Alice'], alice_pos == i))
        s.add(Implies(hobby_vars[i] == hobby_idx['photography'], photography_pos == i))
    
    s.add(alice_pos > photography_pos)
    
    # Check if satisfiable
    if s.check() == sat:
        model = s.model()
        
        # Extract the solution
        solution = {"solution": {"header": ["House", "Name", "Hobby", "Height", "Food"], "rows": []}}
        
        for i in range(n):
            house_num = str(i + 1)
            name_val = names[model.evaluate(name_vars[i]).as_long()]
            hobby_val = hobbies[model.evaluate(hobby_vars[i]).as_long()]
            height_val = heights[model.evaluate(height_vars[i]).as_long()]
            food_val = foods[model.evaluate(food_vars[i]).as_long()]
            
            solution["solution"]["rows"].append([house_num, name_val, hobby_val, height_val, food_val])
        
        print(json.dumps(solution, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()