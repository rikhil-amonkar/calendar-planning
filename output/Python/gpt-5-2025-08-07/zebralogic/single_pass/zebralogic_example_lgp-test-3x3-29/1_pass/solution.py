import json
from itertools import permutations

def solve_puzzle():
    houses = [0, 1, 2]  # 0-based indices for houses 1..3
    
    names = ["Eric", "Peter", "Arnold"]
    mothers = ["Holly", "Aniya", "Janelle"]
    foods = ["pizza", "grilled cheese", "spaghetti"]
    
    solutions = []
    
    for name_perm in permutations(names):
        # Precompute name indices
        idx_name = {name_perm[i]: i for i in houses}
        
        # Clue 3: The person who loves eating grilled cheese is Eric.
        # We'll enforce this later when iterating foods.
        
        for mother_perm in permutations(mothers):
            idx_mother = {mother_perm[i]: i for i in houses}
            
            # Clue 4: Peter is the person whose mother's name is Holly.
            if idx_name["Peter"] != idx_mother["Holly"]:
                continue
            
            for food_perm in permutations(foods):
                idx_food = {food_perm[i]: i for i in houses}
                
                # Clue 3: Eric's food is grilled cheese
                if food_perm[idx_name["Eric"]] != "grilled cheese":
                    continue
                
                # Clue 2: The grilled cheese eater is directly left of Aniya's child
                if not (idx_food["grilled cheese"] + 1 == idx_mother["Aniya"]):
                    continue
                
                # Clue 1 (interpreted): The spaghetti eater and Peter are next to each other
                if abs(idx_food["spaghetti"] - idx_name["Peter"]) != 1:
                    continue
                
                # If all constraints satisfied, record solution
                solutions.append({
                    "names": name_perm,
                    "mothers": mother_perm,
                    "foods": food_perm
                })
    
    # Assuming a unique solution as typical in Zebra puzzles
    if not solutions:
        raise ValueError("No solution found.")
    
    sol = solutions[0]
    rows = []
    for i in houses:
        rows.append([
            str(i + 1),
            sol["names"][i],
            sol["mothers"][i],
            sol["foods"][i]
        ])
    
    output = {
        "solution": {
            "header": ["House", "Name", "Mother", "Food"],
            "rows": rows
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))