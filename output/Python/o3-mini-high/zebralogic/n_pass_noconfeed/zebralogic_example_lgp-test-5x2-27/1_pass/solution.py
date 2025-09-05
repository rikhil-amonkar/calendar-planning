import itertools
import json

def main():
    names = ["Peter", "Alice", "Bob", "Eric", "Arnold"]
    heights = ["very tall", "average", "tall", "very short", "short"]
    
    valid_solution = None
    
    # Iterate over all permutations of names and heights
    for name_perm in itertools.permutations(names):
        # Constraint: Alice must be directly left of the average height person.
        # Since clue 7 fixes the average height to house 5, Alice must be in house 4.
        if name_perm[3] != "Alice":
            continue
        
        for height_perm in itertools.permutations(heights):
            # Constraint: The person who is short is in the second house.
            # Constraint: The person who has an average height is in the fifth house.
            if height_perm[1] != "short" or height_perm[4] != "average":
                continue
            
            # Constraint: Peter is directly left of Bob.
            peter_left_bob = any(name_perm[i] == "Peter" and name_perm[i+1] == "Bob" for i in range(4))
            if not peter_left_bob:
                continue
            
            # Constraint: Eric is somewhere to the left of Peter.
            if name_perm.index("Eric") >= name_perm.index("Peter"):
                continue
            
            # Constraint: The person who is very tall is directly left of Peter.
            vt_left_peter = any(height_perm[i] == "very tall" and name_perm[i+1] == "Peter" for i in range(4))
            if not vt_left_peter:
                continue
            
            # Constraint: The person who is short and the person who is very short are next to each other.
            # Since 'short' is in house 2 (index 1), the 'very short' must be in house 1 (index 0) or house 3 (index 2).
            if abs(height_perm.index("very short") - 1) != 1:
                continue
            
            valid_solution = (name_perm, height_perm)
            break
        if valid_solution is not None:
            break

    if valid_solution is None:
        solution_dict = {}
    else:
        name_perm, height_perm = valid_solution
        rows = []
        for i in range(5):
            # House numbers are 1-indexed
            rows.append([str(i + 1), name_perm[i], height_perm[i]])
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "Height"],
                "rows": rows
            }
        }
    
    print(json.dumps(solution_dict))

if __name__ == "__main__":
    main()