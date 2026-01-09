import json
from constraint import Problem

def solve_puzzle():
    problem = Problem()
    
    houses = [1, 2]
    
    # Define variables for each house
    for house in houses:
        problem.addVariable(f"name_{house}", ["Eric", "Arnold"])
        problem.addVariable(f"book_{house}", ["science fiction", "mystery"])
        problem.addVariable(f"birthday_{house}", ["april", "sept"])
        problem.addVariable(f"animal_{house}", ["horse", "cat"])
    
    # All attributes must be unique across houses
    problem.addConstraint(lambda n1, n2: n1 != n2, ["name_1", "name_2"])
    problem.addConstraint(lambda b1, b2: b1 != b2, ["book_1", "book_2"])
    problem.addConstraint(lambda bd1, bd2: bd1 != bd2, ["birthday_1", "birthday_2"])
    problem.addConstraint(lambda a1, a2: a1 != a2, ["animal_1", "animal_2"])
    
    # Clue 1: Eric is in the first house
    problem.addConstraint(lambda name: name == "Eric", ["name_1"])
    
    # Clue 2: Eric is the person whose birthday is in September
    problem.addConstraint(lambda name, bd: (name == "Eric") == (bd == "sept"), 
                         ["name_1", "birthday_1"])
    problem.addConstraint(lambda name, bd: (name == "Eric") == (bd == "sept"), 
                         ["name_2", "birthday_2"])
    
    # Clue 3: The person who loves science fiction books is in the second house
    problem.addConstraint(lambda book: book == "science fiction", ["book_2"])
    
    # Clue 4: The person who keeps horses is the person whose birthday is in September
    problem.addConstraint(lambda animal, bd: (animal == "horse") == (bd == "sept"), 
                         ["animal_1", "birthday_1"])
    problem.addConstraint(lambda animal, bd: (animal == "horse") == (bd == "sept"), 
                         ["animal_2", "birthday_2"])
    
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    solution = solutions[0]
    
    result = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Birthday", "Animal"],
            "rows": []
        }
    }
    
    for house in sorted(houses):
        row = [
            str(house),
            solution[f"name_{house}"],
            solution[f"book_{house}"],
            solution[f"birthday_{house}"],
            solution[f"animal_{house}"]
        ]
        result["solution"]["rows"].append(row)
    
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))