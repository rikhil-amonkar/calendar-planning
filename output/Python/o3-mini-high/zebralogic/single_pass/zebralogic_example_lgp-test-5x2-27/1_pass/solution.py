#!/usr/bin/env python3
import itertools
import json

def solve_puzzle():
    # Define the attributes.
    houses_count = 5
    names = ["Peter", "Alice", "Bob", "Eric", "Arnold"]
    heights = ["very tall", "average", "tall", "very short", "short"]
    
    # We'll use positions 0 to 4 representing houses 1 to 5 (left to right)
    for names_perm in itertools.permutations(names):
        for heights_perm in itertools.permutations(heights):
            # Constraint 1: The person who is short is in the second house (index 1)
            if heights_perm[1] != "short":
                continue

            # Constraint 7: The person who has an average height is in the fifth house (index 4)
            if heights_perm[4] != "average":
                continue

            # Constraint 2: Peter is directly left of Bob.
            found_peter_bob = False
            for i in range(houses_count - 1):
                if names_perm[i] == "Peter" and names_perm[i + 1] == "Bob":
                    found_peter_bob = True
                    break
            if not found_peter_bob:
                continue

            # Constraint 3: Eric is somewhere to the left of Peter.
            pos_peter = names_perm.index("Peter")
            pos_eric = names_perm.index("Eric")
            if pos_eric >= pos_peter:
                continue

            # Constraint 4: The person who is very tall is directly left of Peter.
            if pos_peter == 0 or heights_perm[pos_peter - 1] != "very tall":
                continue

            # Constraint 5: Alice is directly left of the person who has an average height.
            # Since the average height is in the fifth house (index 4) per Constraint 7,
            # then Alice must be in the fourth house (index 3).
            if names_perm[3] != "Alice":
                continue

            # Constraint 6: The person who is short and the person who is very short are next to each other.
            pos_short = heights_perm.index("short")
            pos_very_short = heights_perm.index("very short")
            if abs(pos_short - pos_very_short) != 1:
                continue
            
            # If all constraints are satisfied, return the solution.
            solution = []
            # Houses numbered 1 to 5 (convert index+1 to str)
            for i in range(houses_count):
                house_number = str(i + 1)
                name = names_perm[i]
                height = heights_perm[i]
                solution.append([house_number, name, height])
            return solution

def main():
    solution_rows = solve_puzzle()
    if solution_rows is None:
        result = {"solution": {"header": ["House", "Name", "Height"], "rows": []}}
    else:
        result = {"solution": {"header": ["House", "Name", "Height"], "rows": solution_rows}}
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()