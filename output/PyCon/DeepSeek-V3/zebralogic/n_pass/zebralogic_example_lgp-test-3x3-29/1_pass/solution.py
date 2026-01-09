import constraint
import json

def solve_puzzle():
    problem = constraint.Problem()
    
    houses = [1, 2, 3]
    names = ['Eric', 'Peter', 'Arnold']
    mothers = ['Holly', 'Aniya', 'Janelle']
    foods = ['pizza', 'grilled cheese', 'spaghetti']
    
    # Add variables for each house
    for house in houses:
        problem.addVariable(f'name_{house}', names)
        problem.addVariable(f'mother_{house}', mothers)
        problem.addVariable(f'food_{house}', foods)
    
    # All attributes must be unique per category
    problem.addConstraint(constraint.AllDifferentConstraint(), [f'name_{house}' for house in houses])
    problem.addConstraint(constraint.AllDifferentConstraint(), [f'mother_{house}' for house in houses])
    problem.addConstraint(constraint.AllDifferentConstraint(), [f'food_{house}' for house in houses])
    
    # Clue 1: The person who loves the spaghetti eater and Peter are next to each other.
    def clue1_constraint(name_1, name_2, name_3, food_1, food_2, food_3):
        peter_house = None
        spaghetti_house = None
        
        if name_1 == 'Peter': peter_house = 1
        if name_2 == 'Peter': peter_house = 2
        if name_3 == 'Peter': peter_house = 3
        
        if food_1 == 'spaghetti': spaghetti_house = 1
        if food_2 == 'spaghetti': spaghetti_house = 2
        if food_3 == 'spaghetti': spaghetti_house = 3
        
        if peter_house is None or spaghetti_house is None:
            return False
            
        return abs(peter_house - spaghetti_house) == 1
    
    problem.addConstraint(clue1_constraint, 
                         ['name_1', 'name_2', 'name_3', 'food_1', 'food_2', 'food_3'])
    
    # Clue 2: The person who loves eating grilled cheese is directly left of The person whose mother's name is Aniya.
    def clue2_constraint(food_1, food_2, food_3, mother_1, mother_2, mother_3):
        grilled_cheese_house = None
        aniya_house = None
        
        if food_1 == 'grilled cheese': grilled_cheese_house = 1
        if food_2 == 'grilled cheese': grilled_cheese_house = 2
        if food_3 == 'grilled cheese': grilled_cheese_house = 3
        
        if mother_1 == 'Aniya': aniya_house = 1
        if mother_2 == 'Aniya': aniya_house = 2
        if mother_3 == 'Aniya': aniya_house = 3
        
        if grilled_cheese_house is None or aniya_house is None:
            return False
            
        return grilled_cheese_house + 1 == aniya_house
    
    problem.addConstraint(clue2_constraint, 
                         ['food_1', 'food_2', 'food_3', 'mother_1', 'mother_2', 'mother_3'])
    
    # Clue 3: The person who loves eating grilled cheese is Eric.
    def clue3_constraint(name_1, name_2, name_3, food_1, food_2, food_3):
        for house in [1, 2, 3]:
            name = eval(f'name_{house}')
            food = eval(f'food_{house}')
            if food == 'grilled cheese' and name != 'Eric':
                return False
            if name == 'Eric' and food != 'grilled cheese':
                return False
        return True
    
    problem.addConstraint(clue3_constraint, 
                         ['name_1', 'name_2', 'name_3', 'food_1', 'food_2', 'food_3'])
    
    # Clue 4: Peter is The person whose mother's name is Holly.
    def clue4_constraint(name_1, name_2, name_3, mother_1, mother_2, mother_3):
        for house in [1, 2, 3]:
            name = eval(f'name_{house}')
            mother = eval(f'mother_{house}')
            if name == 'Peter' and mother != 'Holly':
                return False
            if mother == 'Holly' and name != 'Peter':
                return False
        return True
    
    problem.addConstraint(clue4_constraint, 
                         ['name_1', 'name_2', 'name_3', 'mother_1', 'mother_2', 'mother_3'])
    
    # Solve the puzzle
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": ["House", "Name", "Mother", "Food"], "rows": []}}
    
    solution = solutions[0]
    
    # Format the solution
    rows = []
    for house in houses:
        name = solution[f'name_{house}']
        mother = solution[f'mother_{house}']
        food = solution[f'food_{house}']
        rows.append([str(house), name, mother, food])
    
    result = {
        "solution": {
            "header": ["House", "Name", "Mother", "Food"],
            "rows": rows
        }
    }
    
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))