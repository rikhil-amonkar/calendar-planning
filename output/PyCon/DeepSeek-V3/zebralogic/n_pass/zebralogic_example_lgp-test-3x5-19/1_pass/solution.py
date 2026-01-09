import json
from constraint import Problem

def solve_puzzle():
    problem = Problem()
    
    # Define variables for each house (1, 2, 3)
    houses = [1, 2, 3]
    
    # Define domains for each attribute
    names = ['Arnold', 'Peter', 'Eric']
    occupations = ['doctor', 'teacher', 'engineer']
    educations = ['associate', 'high school', 'bachelor']
    smoothies = ['desert', 'cherry', 'watermelon']
    hobbies = ['gardening', 'cooking', 'photography']
    
    # Add variables for each house
    for house in houses:
        problem.addVariable(f'name_{house}', names)
        problem.addVariable(f'occupation_{house}', occupations)
        problem.addVariable(f'education_{house}', educations)
        problem.addVariable(f'smoothie_{house}', smoothies)
        problem.addVariable(f'hobby_{house}', hobbies)
    
    # All attributes must be unique across houses
    problem.addConstraint(lambda n1, n2, n3: len({n1, n2, n3}) == 3, 
                         ['name_1', 'name_2', 'name_3'])
    problem.addConstraint(lambda o1, o2, o3: len({o1, o2, o3}) == 3, 
                         ['occupation_1', 'occupation_2', 'occupation_3'])
    problem.addConstraint(lambda e1, e2, e3: len({e1, e2, e3}) == 3, 
                         ['education_1', 'education_2', 'education_3'])
    problem.addConstraint(lambda s1, s2, s3: len({s1, s2, s3}) == 3, 
                         ['smoothie_1', 'smoothie_2', 'smoothie_3'])
    problem.addConstraint(lambda h1, h2, h3: len({h1, h2, h3}) == 3, 
                         ['hobby_1', 'hobby_2', 'hobby_3'])
    
    # Clue 1: The Desert smoothie lover is the person who is a doctor.
    problem.addConstraint(lambda smoothie, occupation: smoothie == 'desert' and occupation == 'doctor' 
                         or smoothie != 'desert' and occupation != 'doctor',
                         ['smoothie_1', 'occupation_1'])
    problem.addConstraint(lambda smoothie, occupation: smoothie == 'desert' and occupation == 'doctor' 
                         or smoothie != 'desert' and occupation != 'doctor',
                         ['smoothie_2', 'occupation_2'])
    problem.addConstraint(lambda smoothie, occupation: smoothie == 'desert' and occupation == 'doctor' 
                         or smoothie != 'desert' and occupation != 'doctor',
                         ['smoothie_3', 'occupation_3'])
    
    # Clue 2: Arnold is not in the third house.
    problem.addConstraint(lambda name: name != 'Arnold', ['name_3'])
    
    # Clue 3: The person who likes Cherry smoothies is somewhere to the right of Peter.
    def cherry_right_of_peter(p1, p2, p3, s1, s2, s3):
        peter_house = None
        cherry_house = None
        
        if p1 == 'Peter': peter_house = 1
        if p2 == 'Peter': peter_house = 2
        if p3 == 'Peter': peter_house = 3
        
        if s1 == 'cherry': cherry_house = 1
        if s2 == 'cherry': cherry_house = 2
        if s3 == 'cherry': cherry_house = 3
        
        return cherry_house is not None and peter_house is not None and cherry_house > peter_house
    
    problem.addConstraint(cherry_right_of_peter, 
                         ['name_1', 'name_2', 'name_3', 'smoothie_1', 'smoothie_2', 'smoothie_3'])
    
    # Clue 4: The person who loves cooking is in the second house.
    problem.addConstraint(lambda hobby: hobby == 'cooking', ['hobby_2'])
    
    # Clue 5: The person who loves cooking is Peter.
    problem.addConstraint(lambda hobby, name: hobby == 'cooking' and name == 'Peter' 
                         or hobby != 'cooking' and name != 'Peter',
                         ['hobby_1', 'name_1'])
    problem.addConstraint(lambda hobby, name: hobby == 'cooking' and name == 'Peter' 
                         or hobby != 'cooking' and name != 'Peter',
                         ['hobby_2', 'name_2'])
    problem.addConstraint(lambda hobby, name: hobby == 'cooking' and name == 'Peter' 
                         or hobby != 'cooking' and name != 'Peter',
                         ['hobby_3', 'name_3'])
    
    # Clue 6: The person with an associate's degree is somewhere to the right of the person who enjoys gardening.
    def associate_right_of_gardening(e1, e2, e3, h1, h2, h3):
        gardening_house = None
        associate_house = None
        
        if h1 == 'gardening': gardening_house = 1
        if h2 == 'gardening': gardening_house = 2
        if h3 == 'gardening': gardening_house = 3
        
        if e1 == 'associate': associate_house = 1
        if e2 == 'associate': associate_house = 2
        if e3 == 'associate': associate_house = 3
        
        return associate_house is not None and gardening_house is not None and associate_house > gardening_house
    
    problem.addConstraint(associate_right_of_gardening, 
                         ['education_1', 'education_2', 'education_3', 'hobby_1', 'hobby_2', 'hobby_3'])
    
    # Clue 7: The person with a bachelor's degree is somewhere to the right of the Desert smoothie lover.
    def bachelor_right_of_desert(e1, e2, e3, s1, s2, s3):
        desert_house = None
        bachelor_house = None
        
        if s1 == 'desert': desert_house = 1
        if s2 == 'desert': desert_house = 2
        if s3 == 'desert': desert_house = 3
        
        if e1 == 'bachelor': bachelor_house = 1
        if e2 == 'bachelor': bachelor_house = 2
        if e3 == 'bachelor': bachelor_house = 3
        
        return bachelor_house is not None and desert_house is not None and bachelor_house > desert_house
    
    problem.addConstraint(bachelor_right_of_desert, 
                         ['education_1', 'education_2', 'education_3', 'smoothie_1', 'smoothie_2', 'smoothie_3'])
    
    # Clue 8: The person who loves cooking is the person who is a doctor.
    problem.addConstraint(lambda hobby, occupation: hobby == 'cooking' and occupation == 'doctor' 
                         or hobby != 'cooking' and occupation != 'doctor',
                         ['hobby_1', 'occupation_1'])
    problem.addConstraint(lambda hobby, occupation: hobby == 'cooking' and occupation == 'doctor' 
                         or hobby != 'cooking' and occupation != 'doctor',
                         ['hobby_2', 'occupation_2'])
    problem.addConstraint(lambda hobby, occupation: hobby == 'cooking' and occupation == 'doctor' 
                         or hobby != 'cooking' and occupation != 'doctor',
                         ['hobby_3', 'occupation_3'])
    
    # Clue 9: The photography enthusiast is the person who is a teacher.
    problem.addConstraint(lambda hobby, occupation: hobby == 'photography' and occupation == 'teacher' 
                         or hobby != 'photography' and occupation != 'teacher',
                         ['hobby_1', 'occupation_1'])
    problem.addConstraint(lambda hobby, occupation: hobby == 'photography' and occupation == 'teacher' 
                         or hobby != 'photography' and occupation != 'teacher',
                         ['hobby_2', 'occupation_2'])
    problem.addConstraint(lambda hobby, occupation: hobby == 'photography' and occupation == 'teacher' 
                         or hobby != 'photography' and occupation != 'teacher',
                         ['hobby_3', 'occupation_3'])
    
    # Solve the puzzle
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    # Take the first solution
    solution = solutions[0]
    
    # Build the result structure
    header = ["House", "Name", "Occupation", "Education", "Smoothie", "Hobby"]
    rows = []
    
    for house in houses:
        row = [
            str(house),
            solution[f'name_{house}'],
            solution[f'occupation_{house}'],
            solution[f'education_{house}'],
            solution[f'smoothie_{house}'],
            solution[f'hobby_{house}']
        ]
        rows.append(row)
    
    return {
        "solution": {
            "header": header,
            "rows": rows
        }
    }

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))