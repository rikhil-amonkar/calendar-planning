import json
from z3 import *

def solve_puzzle():
    s = Solver()
    
    # Define variables for each attribute (the value represents the house number, 1 or 2)
    posArnold = Int("posArnold")
    posEric = Int("posEric")
    posGrilledCheese = Int("posGrilledCheese")
    posPizza = Int("posPizza")
    posHolly = Int("posHolly")
    posAniya = Int("posAniya")
    
    # Domain constraints: each variable must be 1 or 2
    s.add(And(posArnold >= 1, posArnold <= 2))
    s.add(And(posEric >= 1, posEric <= 2))
    s.add(And(posGrilledCheese >= 1, posGrilledCheese <= 2))
    s.add(And(posPizza >= 1, posPizza <= 2))
    s.add(And(posHolly >= 1, posHolly <= 2))
    s.add(And(posAniya >= 1, posAniya <= 2))
    
    # Uniqueness constraints within each category
    s.add(Distinct(posArnold, posEric))
    s.add(Distinct(posGrilledCheese, posPizza))
    s.add(Distinct(posHolly, posAniya))
    
    # Clue 1: The person who loves eating grilled cheese is directly left of the person who is a pizza lover.
    # This means: posGrilledCheese + 1 == posPizza.
    s.add(posGrilledCheese + 1 == posPizza)
    
    # Clue 2: Arnold is not in the second house.
    s.add(posArnold != 2)
    
    # Clue 3: Arnold is the person whose mother's name is Holly.
    s.add(posArnold == posHolly)
    
    # Solve the puzzle
    if s.check() == sat:
        model = s.model()
        # Build house information dictionary for houses 1 and 2
        houses_info = {}
        for house in [1, 2]:
            # Determine Name
            if model.evaluate(posArnold).as_long() == house:
                name = "Arnold"
            elif model.evaluate(posEric).as_long() == house:
                name = "Eric"
            else:
                name = ""
            
            # Determine Food
            if model.evaluate(posGrilledCheese).as_long() == house:
                food = "grilled cheese"
            elif model.evaluate(posPizza).as_long() == house:
                food = "pizza"
            else:
                food = ""
            
            # Determine Mother
            if model.evaluate(posHolly).as_long() == house:
                mother = "Holly"
            elif model.evaluate(posAniya).as_long() == house:
                mother = "Aniya"
            else:
                mother = ""
            
            houses_info[house] = [str(house), name, food, mother]
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Food", "Mother"],
                "rows": [
                    houses_info[1],
                    houses_info[2]
                ]
            }
        }
        return solution
    else:
        return {"solution": {}}

if __name__ == "__main__":
    sol = solve_puzzle()
    print(json.dumps(sol, indent=2))