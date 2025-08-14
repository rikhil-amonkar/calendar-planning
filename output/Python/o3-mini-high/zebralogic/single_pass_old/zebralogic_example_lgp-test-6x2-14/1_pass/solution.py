#!/usr/bin/env python3
import itertools
import json

def main():
    # Define the houses numbers (1-indexed)
    houses = [1, 2, 3, 4, 5, 6]
    
    # Fixed assignments based on clues:
    # Names: House1 = Peter, House3 = Bob, House6 = Eric.
    fixed_names = {1: "Peter", 3: "Bob", 6: "Eric"}
    # Cigars: House3 = pall mall, House5 = blue master.
    fixed_cigars = {3: "pall mall", 5: "blue master"}
    
    # All names and cigars in the puzzle.
    all_names = ["Carol", "Peter", "Eric", "Arnold", "Alice", "Bob"]
    all_cigars = ["blends", "yellow monster", "pall mall", "blue master", "dunhill", "prince"]
    
    # Determine remaining names and houses for names (houses not fixed).
    remaining_name_houses = [house for house in houses if house not in fixed_names]
    remaining_names = [name for name in all_names if name not in fixed_names.values()]
    # Similarly for cigars:
    remaining_cigar_houses = [house for house in houses if house not in fixed_cigars]
    remaining_cigars = [cigar for cigar in all_cigars if cigar not in fixed_cigars.values()]
    
    # We'll store valid solutions here.
    solutions = []
    
    # Try all permutations of the remaining names and cigars in their available houses.
    for name_perm in itertools.permutations(remaining_names):
        # Build the names assignment dictionary: key = house number.
        names_assignment = fixed_names.copy()
        for idx, house in enumerate(remaining_name_houses):
            names_assignment[house] = name_perm[idx]
        
        # Check constraint: Carol and Eric are next to each other.
        # Get the house numbers for Carol and Eric.
        pos_carol = None
        pos_eric = None
        for house, name in names_assignment.items():
            if name == "Carol":
                pos_carol = house
            if name == "Eric":
                pos_eric = house
        if pos_carol is None or pos_eric is None:
            continue
        if abs(pos_carol - pos_eric) != 1:
            continue

        for cigar_perm in itertools.permutations(remaining_cigars):
            cigars_assignment = fixed_cigars.copy()
            for idx, house in enumerate(remaining_cigar_houses):
                cigars_assignment[house] = cigar_perm[idx]
            
            # Check fixed constraint: Blue Master in house5 and Pall Mall in house3, Peter in house1, Bob in house3, Eric in house6 are already set.
            # Now enforce the other clues.
            
            # Constraint 1: Arnold is somewhere to the left of the person who smokes blends.
            pos_arnold = None
            pos_blends = None
            for house in houses:
                if names_assignment[house] == "Arnold":
                    pos_arnold = house
                if cigars_assignment[house] == "blends":
                    pos_blends = house
            if pos_arnold is None or pos_blends is None or pos_arnold >= pos_blends:
                continue

            # Constraint 3: Arnold is somewhere to the left of the Prince smoker.
            pos_prince = None
            for house in houses:
                if cigars_assignment[house] == "prince":
                    pos_prince = house
                    break
            if pos_prince is None or pos_arnold >= pos_prince:
                continue

            # Constraint 4: There is one house between the person who smokes Yellow Monster and the person who smokes blends.
            pos_yellow = None
            for house in houses:
                if cigars_assignment[house] == "yellow monster":
                    pos_yellow = house
                    break
            if pos_yellow is None or abs(pos_yellow - pos_blends) != 2:
                continue
            
            # All constraints satisfied; save solution.
            solution = []
            for house in houses:
                # Build row with House number (as string), Name, and favorite cigar.
                row = [str(house), names_assignment[house], cigars_assignment[house]]
                solution.append(row)
            solutions.append(solution)
    
    # Assuming a unique solution, we take the first solution.
    if solutions:
        final_solution = solutions[0]
    else:
        final_solution = []
    
    output = {
        "solution": {
            "header": ["House", "Name", "favorite cigar"],
            "rows": final_solution
        }
    }
    print(json.dumps(output, indent=2))
    
if __name__ == "__main__":
    main()