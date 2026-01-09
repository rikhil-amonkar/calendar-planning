from constraint import Problem
import json

def solve_puzzle():
    problem = Problem()
    
    houses = [1, 2, 3, 4]
    names = ["Alice", "Peter", "Arnold", "Eric"]
    mothers = ["Holly", "Kailyn", "Janelle", "Aniya"]
    flowers = ["carnations", "roses", "lilies", "daffodils"]
    
    problem.addVariables(["name"], names)
    problem.addVariables(["mother"], mothers)
    problem.addVariables(["flower"], flowers)
    
    problem.addConstraint(lambda name, mother: not (name == "Alice" and mother != "Kailyn"), ["name", "mother"])
    problem.addConstraint(lambda name, mother: not (name == "Arnold" and mother != "Holly"), ["name", "mother"])
    problem.addConstraint(lambda name, flower: not (name == "Eric" and flower != "daffodils"), ["name", "flower"])
    
    all_solutions = []
    for house1 in houses:
        for name1 in names:
            for mother1 in mothers:
                for flower1 in flowers:
                    for house2 in houses:
                        if house2 == house1:
                            continue
                        for name2 in names:
                            if name2 == name1:
                                continue
                            for mother2 in mothers:
                                if mother2 == mother1:
                                    continue
                                for flower2 in flowers:
                                    if flower2 == flower1:
                                        continue
                                    for house3 in houses:
                                        if house3 in [house1, house2]:
                                            continue
                                        for name3 in names:
                                            if name3 in [name1, name2]:
                                                continue
                                            for mother3 in mothers:
                                                if mother3 in [mother1, mother2]:
                                                    continue
                                                for flower3 in flowers:
                                                    if flower3 in [flower1, flower2]:
                                                        continue
                                                    house4 = 10 - (house1 + house2 + house3)
                                                    name4 = [n for n in names if n not in [name1, name2, name3]][0]
                                                    mother4 = [m for m in mothers if m not in [mother1, mother2, mother3]][0]
                                                    flower4 = [f for f in flowers if f not in [flower1, flower2, flower3]][0]
                                                    
                                                    assignment = {
                                                        1: {"name": name1, "mother": mother1, "flower": flower1},
                                                        2: {"name": name2, "mother": mother2, "flower": flower2},
                                                        3: {"name": name3, "mother": mother3, "flower": flower3},
                                                        4: {"name": name4, "mother": mother4, "flower": flower4}
                                                    }
                                                    
                                                    if check_constraints(assignment):
                                                        all_solutions.append(assignment)
    
    if all_solutions:
        solution = all_solutions[0]
        result = {
            "solution": {
                "header": ["House", "Name", "Mother", "Flower"],
                "rows": []
            }
        }
        
        for house in sorted(solution.keys()):
            row = [str(house), solution[house]["name"], solution[house]["mother"], solution[house]["flower"]]
            result["solution"]["rows"].append(row)
        
        return json.dumps(result, indent=2)
    else:
        return json.dumps({"error": "No solution found"}, indent=2)

def check_constraints(assignment):
    houses_by_name = {data["name"]: house for house, data in assignment.items()}
    houses_by_mother = {data["mother"]: house for house, data in assignment.items()}
    houses_by_flower = {data["flower"]: house for house, data in assignment.items()}
    
    # Clue 1: Alice is The person whose mother's name is Kailyn.
    if houses_by_name["Alice"] != houses_by_mother["Kailyn"]:
        return False
    
    # Clue 2: The person whose mother's name is Janelle is somewhere to the right of Arnold.
    if houses_by_mother["Janelle"] <= houses_by_name["Arnold"]:
        return False
    
    # Clue 3: Peter is somewhere to the right of the person who loves a carnations arrangement.
    if houses_by_name["Peter"] <= houses_by_flower["carnations"]:
        return False
    
    # Clue 4: Eric is the person who loves a bouquet of daffodils.
    if houses_by_name["Eric"] != houses_by_flower["daffodils"]:
        return False
    
    # Clue 5: Arnold is The person whose mother's name is Holly.
    if houses_by_name["Arnold"] != houses_by_mother["Holly"]:
        return False
    
    # Clue 6: The person who loves a carnations arrangement is somewhere to the right of The person whose mother's name is Holly.
    if houses_by_flower["carnations"] <= houses_by_mother["Holly"]:
        return False
    
    # Clue 7: The person who loves the boquet of lilies is directly left of Alice.
    if houses_by_flower["lilies"] + 1 != houses_by_name["Alice"]:
        return False
    
    # Clue 8: Alice is in the third house.
    if houses_by_name["Alice"] != 3:
        return False
    
    return True

if __name__ == "__main__":
    print(solve_puzzle())