import itertools
import json

def solve_puzzle():
    # Houses are numbered 1 to 6 (left to right)
    # Fixed assignments from clues:
    # Clue 3: Eric is in the second house.
    # Clue 7 and Clue 4: The person who goes on cultural tours (Peter) is in the third house.
    # Clue 9: The person who prefers city breaks is in the fourth house.
    # Clue 2: Eric is somewhere to the right of Alice => Since Eric is house2, Alice must be house1.
    #
    # Therefore, the names for houses 1,2,3 are fixed:
    fixed_names = {1: "Alice", 2: "Eric", 3: "Peter"}
    # The remaining names for houses 4, 5, and 6 (in some order):
    remaining_names = ["Bob", "Carol", "Arnold"]
    
    # Vacation types available:
    vacations = ["mountain", "camping", "cruise", "city", "cultural", "beach"]
    # Fixed vacation assignments:
    fixed_vacations = {3: "cultural", 4: "city"}
    # The remaining vacation types for houses 1,2,5,6:
    remaining_vacations = [v for v in vacations if v not in fixed_vacations.values()]
    
    solution = None
    
    # Iterate over possible assignments for remaining houses for names
    for perm_names in itertools.permutations(remaining_names):
        # Build full name assignment
        names_assignment = {
            1: fixed_names[1],
            2: fixed_names[2],
            3: fixed_names[3],
            4: perm_names[0],
            5: perm_names[1],
            6: perm_names[2]
        }
        # Clue 5: Bob is directly left of Arnold.
        # Find positions (houses) of Bob and Arnold.
        bob_house = None
        arnold_house = None
        for house, name in names_assignment.items():
            if name == "Bob":
                bob_house = house
            if name == "Arnold":
                arnold_house = house
        if bob_house is None or arnold_house is None or arnold_house != bob_house + 1:
            continue
        
        # Iterate over assignments for the remaining vacations for houses 1,2,5,6.
        # The order of houses to assign from the permutation will be: house1, house2, house5, house6.
        for perm_vac in itertools.permutations(remaining_vacations):
            vac_assignment = {}
            vac_assignment[1] = perm_vac[0]
            vac_assignment[2] = perm_vac[1]
            vac_assignment[3] = fixed_vacations[3]  # "cultural"
            vac_assignment[4] = fixed_vacations[4]  # "city"
            vac_assignment[5] = perm_vac[2]
            vac_assignment[6] = perm_vac[3]
            
            # Clue 6: The person who enjoys camping trips is not in the first house.
            if vac_assignment[1] == "camping":
                continue
            
            # Clue 1: The person who goes on cultural tours is somewhere to the left of the person who loves beach vacations.
            # Cultural tours is fixed in house 3, so "beach" must be in a house with a number > 3.
            beach_house = None
            for h in range(1, 7):
                if vac_assignment[h] == "beach":
                    beach_house = h
                    break
            if beach_house is None or beach_house <= 3:
                continue
            
            # Clue 8: The person who likes going on cruises is Bob.
            # Find Bob's house and check his vacation.
            if vac_assignment[bob_house] != "cruise":
                continue
            
            # Clue 2 (Eric is to the right of Alice) is already satisfied by fixed assignment: house1 = Alice, house2 = Eric.
            
            # All constraints satisfied, record the solution.
            solution = []
            for house in range(1, 7):
                solution.append([str(house), names_assignment[house], vac_assignment[house]])
            break  # Found a valid vacation assignment, break out of vacation loop.
        
        if solution is not None:
            break  # Break out of name permutation loop if solution found
    
    result = {
        "solution": {
            "header": ["House", "Name", "Vacation"],
            "rows": solution if solution is not None else []
        }
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    solve_puzzle()