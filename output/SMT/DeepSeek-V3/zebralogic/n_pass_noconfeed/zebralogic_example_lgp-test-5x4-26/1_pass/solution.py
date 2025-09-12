import z3
import json

def main():
    solver = z3.Solver()
    
    # Define the houses
    houses = [1, 2, 3, 4, 5]
    
    # Define the attributes
    names = ['Alice', 'Peter', 'Bob', 'Eric', 'Arnold']
    heights = ['very short', 'short', 'tall', 'average', 'very tall']
    mothers = ['Janelle', 'Kailyn', 'Penny', 'Holly', 'Aniya']
    hair_colors = ['blonde', 'black', 'gray', 'red', 'brown']
    
    # Create variables for each attribute per house
    name_vars = [z3.Int(f'name_{i}') for i in houses]
    height_vars = [z3.Int(f'height_{i}') for i in houses]
    mother_vars = [z3.Int(f'mother_{i}') for i in houses]
    hair_vars = [z3.Int(f'hair_{i}') for i in houses]
    
    # Define domains for each variable
    for i in houses:
        solver.add(z3.And(name_vars[i-1] >= 0, name_vars[i-1] < len(names)))
        solver.add(z3.And(height_vars[i-1] >= 0, height_vars[i-1] < len(heights)))
        solver.add(z3.And(mother_vars[i-1] >= 0, mother_vars[i-1] < len(mothers)))
        solver.add(z3.And(hair_vars[i-1] >= 0, hair_vars[i-1] < len(hair_colors)))
    
    # All attributes are distinct within their category
    solver.add(z3.Distinct(name_vars))
    solver.add(z3.Distinct(height_vars))
    solver.add(z3.Distinct(mother_vars))
    solver.add(z3.Distinct(hair_vars))
    
    # Clue 1: The person who is tall is The person whose mother's name is Holly.
    tall_index = heights.index('tall')
    holly_index = mothers.index('Holly')
    for i in houses:
        solver.add(z3.Implies(height_vars[i-1] == tall_index, mother_vars[i-1] == holly_index))
    
    # Clue 2: There are two houses between the person who has an average height and the person who is short.
    average_index = heights.index('average')
    short_index = heights.index('short')
    for i in houses:
        for j in houses:
            if abs(i - j) == 3:  # Two houses between means difference of 3 positions
                solver.add(z3.Or(
                    z3.And(height_vars[i-1] == average_index, height_vars[j-1] == short_index),
                    z3.And(height_vars[i-1] == short_index, height_vars[j-1] == average_index)
                ))
    
    # Clue 3: The person who has gray hair is directly left of The person whose mother's name is Janelle.
    gray_index = hair_colors.index('gray')
    janelle_index = mothers.index('Janelle')
    for i in range(1, 5):  # House 1-4 can be left of another house
        solver.add(z3.Implies(
            hair_vars[i-1] == gray_index,
            z3.And(mother_vars[i] == janelle_index, hair_vars[i] != gray_index)
        ))
    
    # Clue 4: The person who has black hair is not in the fourth house.
    black_index = hair_colors.index('black')
    solver.add(hair_vars[3] != black_index)  # House 4 is index 3
    
    # Clue 5: Eric is the person who has black hair.
    eric_index = names.index('Eric')
    for i in houses:
        solver.add(z3.Implies(name_vars[i-1] == eric_index, hair_vars[i-1] == black_index))
    
    # Clue 6: The person who is very short is The person whose mother's name is Penny.
    very_short_index = heights.index('very short')
    penny_index = mothers.index('Penny')
    for i in houses:
        solver.add(z3.Implies(height_vars[i-1] == very_short_index, mother_vars[i-1] == penny_index))
    
    # Clue 7: Eric and the person who has gray hair are next to each other.
    for i in houses:
        adjacent_houses = []
        if i > 1:
            adjacent_houses.append(i-1)
        if i < 5:
            adjacent_houses.append(i+1)
        
        solver.add(z3.Implies(
            name_vars[i-1] == eric_index,
            z3.Or([hair_vars[j-1] == gray_index for j in adjacent_houses])
        ))
    
    # Clue 8: Bob is in the fifth house.
    bob_index = names.index('Bob')
    solver.add(name_vars[4] == bob_index)
    
    # Clue 9: The person who has red hair is Peter.
    red_index = hair_colors.index('red')
    peter_index = names.index('Peter')
    for i in houses:
        solver.add(z3.Implies(hair_vars[i-1] == red_index, name_vars[i-1] == peter_index))
    
    # Clue 10: The person whose mother's name is Kailyn is directly left of the person who is short.
    kailyn_index = mothers.index('Kailyn')
    for i in range(1, 5):  # House 1-4 can be left of another house
        solver.add(z3.Implies(
            mother_vars[i-1] == kailyn_index,
            z3.And(height_vars[i] == short_index, mother_vars[i] != kailyn_index)
        ))
    
    # Clue 11: Arnold is the person who has brown hair.
    arnold_index = names.index('Arnold')
    brown_index = hair_colors.index('brown')
    for i in houses:
        solver.add(z3.Implies(name_vars[i-1] == arnold_index, hair_vars[i-1] == brown_index))
    
    # Clue 12: The person who has brown hair is somewhere to the left of The person whose mother's name is Janelle.
    for i in houses:
        for j in houses:
            if i >= j:  # i is not to the left of j
                continue
            solver.add(z3.Implies(
                hair_vars[i-1] == brown_index,
                z3.Implies(mother_vars[j-1] == janelle_index, i < j)
            ))
    
    # Clue 13: The person whose mother's name is Aniya and the person who is very short are next to each other.
    aniya_index = mothers.index('Aniya')
    for i in houses:
        adjacent_houses = []
        if i > 1:
            adjacent_houses.append(i-1)
        if i < 5:
            adjacent_houses.append(i+1)
        
        solver.add(z3.Implies(
            mother_vars[i-1] == aniya_index,
            z3.Or([height_vars[j-1] == very_short_index for j in adjacent_houses])
        ))
    
    # Clue 14: The person whose mother's name is Kailyn is in the third house.
    solver.add(mother_vars[2] == kailyn_index)  # House 3 is index 2
    
    # Check if the problem is satisfiable
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Create result structure
        result = {
            "solution": {
                "header": ["House", "Name", "Height", "Mother", "HairColor"],
                "rows": []
            }
        }
        
        # Extract values for each house
        for house in houses:
            name_val = model.eval(name_vars[house-1]).as_long()
            height_val = model.eval(height_vars[house-1]).as_long()
            mother_val = model.eval(mother_vars[house-1]).as_long()
            hair_val = model.eval(hair_vars[house-1]).as_long()
            
            row = [
                str(house),
                names[name_val],
                heights[height_val],
                mothers[mother_val],
                hair_colors[hair_val]
            ]
            result["solution"]["rows"].append(row)
        
        print(json.dumps(result, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()