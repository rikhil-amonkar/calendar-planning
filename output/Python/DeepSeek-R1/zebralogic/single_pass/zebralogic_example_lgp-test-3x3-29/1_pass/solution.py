import itertools
import json

def main():
    names = ["Eric", "Peter", "Arnold"]
    mothers = ["Holly", "Aniya", "Janelle"]
    foods = ["pizza", "grilled cheese", "spaghetti"]
    
    solution_found = None
    
    for name_perm in itertools.permutations(names):
        for mother_perm in itertools.permutations(mothers):
            for food_perm in itertools.permutations(foods):
                houses = []
                for i in range(3):
                    houses.append((name_perm[i], mother_perm[i], food_perm[i]))
                
                valid = True
                
                # Constraint 3: Grilled cheese eater is Eric
                for i in range(3):
                    if houses[i][2] == 'grilled cheese':
                        if houses[i][0] != 'Eric':
                            valid = False
                        break
                if not valid:
                    continue
                    
                # Constraint 4: Peter's mother is Holly
                for i in range(3):
                    if houses[i][0] == 'Peter':
                        if houses[i][1] != 'Holly':
                            valid = False
                        break
                if not valid:
                    continue
                    
                # Constraint 2: Grilled cheese left of Aniya mother
                gc_index = None
                for i in range(3):
                    if houses[i][2] == 'grilled cheese':
                        gc_index = i
                        break
                if gc_index is None or gc_index == 2:
                    valid = False
                else:
                    if houses[gc_index+1][1] != 'Aniya':
                        valid = False
                if not valid:
                    continue
                    
                # Constraint 1: Spaghetti eater adjacent to Peter
                peter_index = None
                spaghetti_index = None
                for i in range(3):
                    if houses[i][0] == 'Peter':
                        peter_index = i
                    if houses[i][2] == 'spaghetti':
                        spaghetti_index = i
                if peter_index is None or spaghetti_index is None:
                    valid = False
                else:
                    if abs(peter_index - spaghetti_index) != 1:
                        valid = False
                if not valid:
                    continue
                    
                solution_found = houses
                break
            if solution_found is not None:
                break
        if solution_found is not None:
            break
            
    rows = []
    if solution_found is not None:
        for i, house in enumerate(solution_found):
            rows.append([str(i+1), house[0], house[1], house[2]])
    
    output = {
        "solution": {
            "header": ["House", "Name", "Mother", "Food"],
            "rows": rows
        }
    }
    print(json.dumps(output))

if __name__ == "__main__":
    main()