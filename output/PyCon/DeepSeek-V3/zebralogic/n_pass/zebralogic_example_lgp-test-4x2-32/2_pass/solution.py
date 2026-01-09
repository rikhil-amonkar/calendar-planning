import json
from constraint import Problem

def solve_puzzle():
    problem = Problem()
    
    houses = [1, 2, 3, 4]
    names = ["Peter", "Arnold", "Eric", "Alice"]
    pets = ["bird", "fish", "dog", "cat"]
    
    # Add variables for each house position
    problem.addVariables(["name1", "name2", "name3", "name4"], names)
    problem.addVariables(["pet1", "pet2", "pet3", "pet4"], pets)
    
    # Add constraints for unique assignments
    problem.addConstraint(lambda n1, n2, n3, n4: len(set([n1, n2, n3, n4])) == 4, 
                         ["name1", "name2", "name3", "name4"])
    problem.addConstraint(lambda p1, p2, p3, p4: len(set([p1, p2, p3, p4])) == 4, 
                         ["pet1", "pet2", "pet3", "pet4"])
    
    # Clue 2: Eric is not in the first house
    problem.addConstraint(lambda n1: n1 != "Eric", ["name1"])
    
    # Clue 3: Eric is the person who keeps a pet bird
    problem.addConstraint(lambda n1, n2, n3, n4, p1, p2, p3, p4: 
                         ((n1 == "Eric" and p1 == "bird") or
                          (n2 == "Eric" and p2 == "bird") or
                          (n3 == "Eric" and p3 == "bird") or
                          (n4 == "Eric" and p4 == "bird")), 
                         ["name1", "name2", "name3", "name4", "pet1", "pet2", "pet3", "pet4"])
    
    # Clue 5: Alice is not in the first house
    problem.addConstraint(lambda n1: n1 != "Alice", ["name1"])
    
    # Clue 6: Arnold is the person with an aquarium of fish
    problem.addConstraint(lambda n1, n2, n3, n4, p1, p2, p3, p4: 
                         ((n1 == "Arnold" and p1 == "fish") or
                          (n2 == "Arnold" and p2 == "fish") or
                          (n3 == "Arnold" and p3 == "fish") or
                          (n4 == "Arnold" and p4 == "fish")), 
                         ["name1", "name2", "name3", "name4", "pet1", "pet2", "pet3", "pet4"])
    
    # Clue 1: The person who owns a dog is somewhere to the right of Alice
    problem.addConstraint(lambda n1, n2, n3, n4, p1, p2, p3, p4: 
                         ((n1 == "Alice" and (p2 == "dog" or p3 == "dog" or p4 == "dog")) or
                          (n2 == "Alice" and (p3 == "dog" or p4 == "dog")) or
                          (n3 == "Alice" and p4 == "dog") or
                          (n4 == "Alice" and False)),  # Alice can't be in last house if dog is to the right
                         ["name1", "name2", "name3", "name4", "pet1", "pet2", "pet3", "pet4"])
    
    # Clue 4: There is one house between the person with an aquarium of fish and Peter
    problem.addConstraint(lambda n1, n2, n3, n4, p1, p2, p3, p4: 
                         ((n1 == "Peter" and p3 == "fish") or  # Peter in house 1, fish in house 3
                          (n2 == "Peter" and p4 == "fish") or  # Peter in house 2, fish in house 4
                          (n3 == "Peter" and p1 == "fish") or  # Peter in house 3, fish in house 1
                          (n4 == "Peter" and p2 == "fish")),   # Peter in house 4, fish in house 2
                         ["name1", "name2", "name3", "name4", "pet1", "pet2", "pet3", "pet4"])
    
    solutions = problem.getSolutions()
    
    if solutions:
        solution = solutions[0]
        result = {
            "solution": {
                "header": ["House", "Name", "Pet"],
                "rows": [
                    ["1", solution["name1"], solution["pet1"]],
                    ["2", solution["name2"], solution["pet2"]],
                    ["3", solution["name3"], solution["pet3"]],
                    ["4", solution["name4"], solution["pet4"]]
                ]
            }
        }
        return json.dumps(result)
    else:
        return json.dumps({"error": "No solution found"})

if __name__ == "__main__":
    print(solve_puzzle())