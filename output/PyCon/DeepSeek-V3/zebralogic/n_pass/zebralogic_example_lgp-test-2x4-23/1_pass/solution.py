from constraint import Problem
import json

def solve_puzzle():
    problem = Problem()
    
    houses = [1, 2]
    
    # Define variables for each attribute
    names = ['Eric', 'Arnold']
    mothers = ['Aniya', 'Holly']
    car_models = ['ford f150', 'tesla model 3']
    heights = ['short', 'very short']
    
    # Add variables for each house
    for house in houses:
        problem.addVariable(f'name_{house}', names)
        problem.addVariable(f'mother_{house}', mothers)
        problem.addVariable(f'car_{house}', car_models)
        problem.addVariable(f'height_{house}', heights)
    
    # All attributes must be different within their category
    problem.addConstraint(lambda n1, n2: n1 != n2, ['name_1', 'name_2'])
    problem.addConstraint(lambda m1, m2: m1 != m2, ['mother_1', 'mother_2'])
    problem.addConstraint(lambda c1, c2: c1 != c2, ['car_1', 'car_2'])
    problem.addConstraint(lambda h1, h2: h1 != h2, ['height_1', 'height_2'])
    
    # Clue 1: The person who owns a Tesla Model 3 is somewhere to the right of Arnold
    def tesla_right_of_arnold(car1, car2, name1, name2):
        arnold_house = None
        tesla_house = None
        
        if name1 == 'Arnold':
            arnold_house = 1
        if name2 == 'Arnold':
            arnold_house = 2
            
        if car1 == 'tesla model 3':
            tesla_house = 1
        if car2 == 'tesla model 3':
            tesla_house = 2
            
        return tesla_house is not None and arnold_house is not None and tesla_house > arnold_house
    
    problem.addConstraint(tesla_right_of_arnold, ['car_1', 'car_2', 'name_1', 'name_2'])
    
    # Clue 2: Arnold is the person who is short
    def arnold_is_short(name1, name2, height1, height2):
        if name1 == 'Arnold':
            return height1 == 'short'
        if name2 == 'Arnold':
            return height2 == 'short'
        return False
    
    problem.addConstraint(arnold_is_short, ['name_1', 'name_2', 'height_1', 'height_2'])
    
    # Clue 3: The person whose mother's name is Holly is in the second house
    problem.addConstraint(lambda mother: mother == 'Holly', ['mother_2'])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    solution = solutions[0]
    
    # Build the result
    header = ["House", "Name", "Mother", "CarModel", "Height"]
    rows = []
    
    for house in sorted(houses):
        row = [
            str(house),
            solution[f'name_{house}'],
            solution[f'mother_{house}'],
            solution[f'car_{house}'],
            solution[f'height_{house}']
        ]
        rows.append(row)
    
    return {"solution": {"header": header, "rows": rows}}

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))