import json
from constraint import Problem

def solve_puzzle():
    problem = Problem()
    
    # Define variables for each house
    houses = [1, 2]
    
    # Add variables for each attribute
    for house in houses:
        problem.addVariable(f"name_{house}", ["Arnold", "Eric"])
        problem.addVariable(f"education_{house}", ["associate", "high school"])
        problem.addVariable(f"height_{house}", ["short", "very short"])
        problem.addVariable(f"food_{house}", ["grilled cheese", "pizza"])
        problem.addVariable(f"drink_{house}", ["tea", "water"])
    
    # All attributes must be unique across houses
    for attr in ["name", "education", "height", "food", "drink"]:
        problem.addConstraint(lambda *x: len(set(x)) == len(x), 
                            [f"{attr}_{house}" for house in houses])
    
    # Clue 1: The person who is very short is the person who is a pizza lover.
    for house in houses:
        problem.addConstraint(
            lambda height, food: not (height == "very short" and food != "pizza"),
            [f"height_{house}", f"food_{house}"]
        )
        problem.addConstraint(
            lambda height, food: not (food == "pizza" and height != "very short"),
            [f"height_{house}", f"food_{house}"]
        )
    
    # Clue 2: The person who loves eating grilled cheese is in the second house.
    problem.addConstraint(lambda food: food == "grilled cheese", ["food_2"])
    
    # Clue 3: The person with a high school diploma is the person who is a pizza lover.
    for house in houses:
        problem.addConstraint(
            lambda education, food: not (education == "high school" and food != "pizza"),
            [f"education_{house}", f"food_{house}"]
        )
        problem.addConstraint(
            lambda education, food: not (food == "pizza" and education != "high school"),
            [f"education_{house}", f"food_{house}"]
        )
    
    # Clue 4: The tea drinker is the person who loves eating grilled cheese.
    for house in houses:
        problem.addConstraint(
            lambda drink, food: not (drink == "tea" and food != "grilled cheese"),
            [f"drink_{house}", f"food_{house}"]
        )
        problem.addConstraint(
            lambda drink, food: not (food == "grilled cheese" and drink != "tea"),
            [f"drink_{house}", f"food_{house}"]
        )
    
    # Clue 5: Arnold is the person who is a pizza lover.
    for house in houses:
        problem.addConstraint(
            lambda name, food: not (name == "Arnold" and food != "pizza"),
            [f"name_{house}", f"food_{house}"]
        )
        problem.addConstraint(
            lambda name, food: not (food == "pizza" and name != "Arnold"),
            [f"name_{house}", f"food_{house}"]
        )
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    solution = solutions[0]
    
    # Build the result
    header = ["House", "Name", "Education", "Height", "Food", "Drink"]
    rows = []
    
    for house in sorted(houses):
        row = [
            str(house),
            solution[f"name_{house}"],
            solution[f"education_{house}"],
            solution[f"height_{house}"],
            solution[f"food_{house}"],
            solution[f"drink_{house}"]
        ]
        rows.append(row)
    
    return {"solution": {"header": header, "rows": rows}}

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))