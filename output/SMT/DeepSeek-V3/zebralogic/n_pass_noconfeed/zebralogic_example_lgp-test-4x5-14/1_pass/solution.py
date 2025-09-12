import z3
import json

def main():
    solver = z3.Solver()
    
    # Define the houses
    houses = [1, 2, 3, 4]
    
    # Define the attributes and their possible values
    names = ['Peter', 'Alice', 'Eric', 'Arnold']
    mothers = ['Janelle', 'Holly', 'Aniya', 'Kailyn']
    smoothies = ['watermelon', 'dragonfruit', 'desert', 'cherry']
    heights = ['tall', 'average', 'short', 'very short']
    educations = ['high school', 'associate', 'master', 'bachelor']
    
    # Create Z3 variables for each attribute in each house
    name_vars = [z3.Int(f'name_{i}') for i in houses]
    mother_vars = [z3.Int(f'mother_{i}') for i in houses]
    smoothie_vars = [z3.Int(f'smoothie_{i}') for i in houses]
    height_vars = [z3.Int(f'height_{i}') for i in houses]
    education_vars = [z3.Int(f'education_{i}') for i in houses]
    
    # Define the domain for each variable
    for i in houses:
        solver.add(z3.And(name_vars[i-1] >= 0, name_vars[i-1] < len(names)))
        solver.add(z3.And(mother_vars[i-1] >= 0, mother_vars[i-1] < len(mothers)))
        solver.add(z3.And(smoothie_vars[i-1] >= 0, smoothie_vars[i-1] < len(smoothies)))
        solver.add(z3.And(height_vars[i-1] >= 0, height_vars[i-1] < len(heights)))
        solver.add(z3.And(education_vars[i-1] >= 0, education_vars[i-1] < len(educations)))
    
    # All attributes must be unique within their category
    solver.add(z3.Distinct(name_vars))
    solver.add(z3.Distinct(mother_vars))
    solver.add(z3.Distinct(smoothie_vars))
    solver.add(z3.Distinct(height_vars))
    solver.add(z3.Distinct(education_vars))
    
    # Clue 1: The person whose mother's name is Janelle is in the third house.
    solver.add(mother_vars[2] == mothers.index('Janelle'))
    
    # Clue 2: The Desert smoothie lover is the person with a master's degree.
    desert_smoothie = smoothies.index('desert')
    master_degree = educations.index('master')
    for i in houses:
        solver.add(z3.Implies(smoothie_vars[i-1] == desert_smoothie, education_vars[i-1] == master_degree))
    
    # Clue 3: The Desert smoothie lover is not in the first house.
    solver.add(smoothie_vars[0] != desert_smoothie)
    
    # Clue 4: The person who is very short is somewhere to the left of the person with a high school diploma.
    very_short = heights.index('very short')
    high_school = educations.index('high school')
    # At least one house where very short is left of high school
    left_constraints = []
    for i in houses:
        for j in houses:
            if i < j:  # i is left of j
                left_constraints.append(z3.And(height_vars[i-1] == very_short, education_vars[j-1] == high_school))
    solver.add(z3.Or(left_constraints))
    
    # Clue 5: Eric and the person who likes Cherry smoothies are next to each other.
    eric = names.index('Eric')
    cherry = smoothies.index('cherry')
    adjacent_constraints = []
    for i in houses:
        for j in houses:
            if abs(i - j) == 1:  # adjacent houses
                adjacent_constraints.append(z3.And(name_vars[i-1] == eric, smoothie_vars[j-1] == cherry))
                adjacent_constraints.append(z3.And(name_vars[j-1] == eric, smoothie_vars[i-1] == cherry))
    solver.add(z3.Or(adjacent_constraints))
    
    # Clue 6: The person with a high school diploma is not in the third house.
    solver.add(education_vars[2] != high_school)
    
    # Clue 7: The person whose mother's name is Kailyn is the person with an associate's degree.
    kailyn = mothers.index('Kailyn')
    associate = educations.index('associate')
    for i in houses:
        solver.add(z3.Implies(mother_vars[i-1] == kailyn, education_vars[i-1] == associate))
    
    # Clue 8: The person who likes Cherry smoothies is The person whose mother's name is Aniya.
    aniya = mothers.index('Aniya')
    for i in houses:
        solver.add(z3.Implies(smoothie_vars[i-1] == cherry, mother_vars[i-1] == aniya))
    
    # Clue 9: The person who is tall is The person whose mother's name is Janelle.
    tall = heights.index('tall')
    janelle = mothers.index('Janelle')
    for i in houses:
        solver.add(z3.Implies(height_vars[i-1] == tall, mother_vars[i-1] == janelle))
    
    # Clue 10: Arnold is somewhere to the right of the person who has an average height.
    arnold = names.index('Arnold')
    average = heights.index('average')
    right_constraints = []
    for i in houses:
        for j in houses:
            if i > j:  # i is right of j
                right_constraints.append(z3.And(name_vars[i-1] == arnold, height_vars[j-1] == average))
    solver.add(z3.Or(right_constraints))
    
    # Clue 11: The Dragonfruit smoothie lover is directly left of the person who is short.
    dragonfruit = smoothies.index('dragonfruit')
    short = heights.index('short')
    direct_left_constraints = []
    for i in range(1, 4):  # houses 1, 2, 3 can be directly left of next house
        direct_left_constraints.append(z3.And(smoothie_vars[i-1] == dragonfruit, height_vars[i] == short))
    solver.add(z3.Or(direct_left_constraints))
    
    # Clue 12: The person who is tall is Alice.
    alice = names.index('Alice')
    for i in houses:
        solver.add(z3.Implies(height_vars[i-1] == tall, name_vars[i-1] == alice))
    
    # Check if the constraints are satisfiable
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Create result dictionary
        result = {
            "solution": {
                "header": ["House", "Name", "Mother", "Smoothie", "Height", "Education"],
                "rows": []
            }
        }
        
        # Extract values for each house
        for i in houses:
            name_idx = model.evaluate(name_vars[i-1]).as_long()
            mother_idx = model.evaluate(mother_vars[i-1]).as_long()
            smoothie_idx = model.evaluate(smoothie_vars[i-1]).as_long()
            height_idx = model.evaluate(height_vars[i-1]).as_long()
            education_idx = model.evaluate(education_vars[i-1]).as_long()
            
            row = [
                str(i),
                names[name_idx],
                mothers[mother_idx],
                smoothies[smoothie_idx],
                heights[height_idx],
                educations[education_idx]
            ]
            result["solution"]["rows"].append(row)
        
        # Output as JSON
        print(json.dumps(result, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()