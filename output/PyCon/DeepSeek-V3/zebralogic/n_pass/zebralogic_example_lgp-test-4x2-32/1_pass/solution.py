import json
from constraint import Problem

def solve_puzzle():
    problem = Problem()
    
    houses = [1, 2, 3, 4]
    names = ["Peter", "Arnold", "Eric", "Alice"]
    pets = ["bird", "fish", "dog", "cat"]
    
    problem.addVariables(["name"], [names])
    problem.addVariables(["pet"], [pets])
    
    # Add constraints for unique assignments
    problem.addConstraint(lambda name, pet: len(name) == len(set(name)) and len(pet) == len(set(pet)), ["name", "pet"])
    
    # Clue 2: Eric is not in the first house
    problem.addConstraint(lambda name: name[0] != "Eric", ["name"])
    
    # Clue 3: Eric is the person who keeps a pet bird
    problem.addConstraint(lambda name, pet: pet[name.index("Eric")] == "bird", ["name", "pet"])
    
    # Clue 5: Alice is not in the first house
    problem.addConstraint(lambda name: name[0] != "Alice", ["name"])
    
    # Clue 6: Arnold is the person with an aquarium of fish
    problem.addConstraint(lambda name, pet: pet[name.index("Arnold")] == "fish", ["name", "pet"])
    
    # Clue 1: The person who owns a dog is somewhere to the right of Alice
    problem.addConstraint(lambda name, pet: name.index("Alice") < pet.index("dog"), ["name", "pet"])
    
    # Clue 4: There is one house between the person with an aquarium of fish and Peter
    problem.addConstraint(lambda name, pet: abs(name.index("Peter") - pet.index("fish")) == 2, ["name", "pet"])
    
    solutions = problem.getSolutions()
    
    if solutions:
        solution = solutions[0]
        names = solution["name"]
        pets = solution["pet"]
        
        result = {
            "solution": {
                "header": ["House", "Name", "Pet"],
                "rows": []
            }
        }
        
        for i in range(4):
            result["solution"]["rows"].append([str(i+1), names[i], pets[i]])
        
        return json.dumps(result)
    else:
        return json.dumps({"error": "No solution found"})

if __name__ == "__main__":
    print(solve_puzzle())