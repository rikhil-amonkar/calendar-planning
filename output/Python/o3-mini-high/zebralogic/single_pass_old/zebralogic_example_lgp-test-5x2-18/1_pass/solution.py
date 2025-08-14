#!/usr/bin/env python3
import itertools
import json

def main():
    # Define the attributes
    houses = [1, 2, 3, 4, 5]
    names = ["Eric", "Alice", "Peter", "Bob", "Arnold"]
    children = ["Timothy", "Meredith", "Samantha", "Fred", "Bella"]

    solutions = []
    
    # Since house 2 must have child "Fred" and by clue 7 the house immediately to its right (house 3) must have "Bella",
    # we fix these positions in the child assignment.
    # The remaining child names to assign to houses 1, 4, and 5 are the ones not "Fred" or "Bella".
    remaining_children = [child for child in children if child not in ["Fred", "Bella"]]
    
    # Iterate over all permutations for the persons over the 5 houses.
    for perm_names in itertools.permutations(names):
        # Iterate over all permutations for the remaining children for houses 1, fourth and fifth houses.
        for perm_remaining in itertools.permutations(remaining_children):
            # Build the child assignment tuple with fixed positions:
            # House 1: perm_remaining[0]
            # House 2: "Fred" (clue 3)
            # House 3: "Bella" (clue 7, Fred is directly left of Bella)
            # House 4: perm_remaining[1]
            # House 5: perm_remaining[2]
            child_assignment = (perm_remaining[0], "Fred", "Bella", perm_remaining[1], perm_remaining[2])
            
            # Get indices for special children and persons using 0-indexed positions (House 1 index 0, House 2 index 1, etc.)
            try:
                index_samantha = child_assignment.index("Samantha")
                index_timothy = child_assignment.index("Timothy")
            except ValueError:
                continue  # If Samantha or Timothy are not in this assignment, skip
            
            index_bob = perm_names.index("Bob")
            index_alice = perm_names.index("Alice")
            index_peter = perm_names.index("Peter")
            index_eric = perm_names.index("Eric")
            
            # Apply the constraints
            
            # Clue 1: Bob is somewhere to the left of the house whose child is named Samantha.
            if index_bob >= index_samantha:
                continue

            # Clue 2: The house with child Timothy is somewhere to the left of the house whose child is named Samantha.
            if index_timothy >= index_samantha:
                continue

            # Clue 4: There is one house between Alice and the house whose child is named Samantha.
            if abs(index_alice - index_samantha) != 2:
                continue

            # Clue 5: Eric is not in the third house (House 3 is index 2).
            if index_eric == 2:
                continue

            # Clue 6: Bob is not in the third house.
            if index_bob == 2:
                continue

            # Clue 8: The house whose child is named Samantha is somewhere to the left of the house with Peter.
            if index_samantha >= index_peter:
                continue

            # All conditions met; record the solution.
            solution = []
            for i in range(5):
                # House number as string, then corresponding Name and Child.
                solution.append([str(houses[i]), perm_names[i], child_assignment[i]])
            solutions.append(solution)
    
    # Assume a unique solution; take the first found solution.
    final_solution = solutions[0] if solutions else []
    output = {
        "solution": {
            "header": ["House", "Name", "Child"],
            "rows": final_solution
        }
    }
    
    print(json.dumps(output))

if __name__ == "__main__":
    main()