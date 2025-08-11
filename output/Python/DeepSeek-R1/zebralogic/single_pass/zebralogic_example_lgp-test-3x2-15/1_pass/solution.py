import itertools
import json

def main():
    names = ['Arnold', 'Peter', 'Eric']
    heights = ['short', 'average', 'very short']
    houses = [1, 2, 3]
    solutions = []

    for name_perm in itertools.permutations(names):
        for height_perm in itertools.permutations(heights):
            # Constraint 2: The person who is short is in the first house.
            if height_perm[0] != 'short':
                continue
                
            # Constraint 1: Peter is somewhere to the right of Eric.
            eric_index = name_perm.index('Eric')
            peter_index = name_perm.index('Peter')
            if eric_index >= peter_index:
                continue
                
            # Constraint 3: One house between short and very short.
            short_index = height_perm.index('short')
            very_short_index = height_perm.index('very short')
            if abs(short_index - very_short_index) != 2:
                continue
                
            # Constraint 4: Arnold and the person who is very short are next to each other.
            arnold_index = name_perm.index('Arnold')
            very_short_index = height_perm.index('very short')
            if abs(arnold_index - very_short_index) != 1:
                continue
                
            # If all constraints are satisfied, add the solution
            solution = []
            for i in range(len(houses)):
                solution.append({
                    'House': str(i+1),
                    'Name': name_perm[i],
                    'Height': height_perm[i]
                })
            solutions.append(solution)
    
    # We expect exactly one solution
    if solutions:
        sol = solutions[0]
        # Prepare the output in the required JSON format
        header = ["House", "Name", "Height"]
        rows = []
        for house in sol:
            row = [house['House'], house['Name'], house['Height']]
            rows.append(row)
        
        output = {
            "solution": {
                "header": header,
                "rows": rows
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print(json.dumps({"solution": {}}))

if __name__ == "__main__":
    main()