import json
from itertools import permutations

def solve_puzzle():
    # Define all possible attributes
    names = ['Eric', 'Arnold']
    house_styles = ['victorian', 'colonial']
    heights = ['very short', 'short']
    educations = ['associate', 'high school']
    
    # Generate all possible permutations for each attribute
    for name_perm in permutations(names):
        for house_perm in permutations(house_styles):
            for height_perm in permutations(heights):
                for edu_perm in permutations(educations):
                    # Check all constraints
                    # Constraint 2: Victorian is first house
                    if house_perm[0] != 'victorian':
                        continue
                    
                    # Constraint 1: short is directly left of Eric
                    # Find index of short and Eric
                    try:
                        short_index = height_perm.index('short')
                        eric_index = name_perm.index('Eric')
                    except ValueError:
                        continue
                    
                    if short_index + 1 != eric_index:
                        continue
                    
                    # Constraint 3: short person has associate's degree
                    if edu_perm[short_index] != 'associate':
                        continue
                    
                    # All constraints satisfied, build solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "house style", "height", "education"],
                            "rows": [
                                ["1", name_perm[0], house_perm[0], height_perm[0], edu_perm[0]],
                                ["2", name_perm[1], house_perm[1], height_perm[1], edu_perm[1]]
                            ]
                        }
                    }
                    return solution
    
    return {"solution": {"header": [], "rows": []}}

# Solve and print the solution as JSON
solution = solve_puzzle()
print(json.dumps(solution, indent=2))