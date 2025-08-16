#!/usr/bin/env python3
import itertools
import json

def solve_puzzle():
    # Fixed names based on clues:
    # Clue 8: Peter is in house 1.
    # Clue 9: Bob is in house 3.
    # Clue 6: Eric is in house 6.
    # Clue 7: Carol and Eric are next to each other, so Carol must be in house 5.
    # Remaining names {Arnold, Alice} go to houses 2 and 4.
    # Clues 1 and 3 force Arnold to be to the left of certain cigar smokers.
    # The only viable assignment is:
    # House 1: Peter, House 2: Arnold, House 3: Bob, House 4: Alice, House 5: Carol, House 6: Eric
    names = {
        1: "Peter",
        2: "Arnold",
        3: "Bob",
        4: "Alice",
        5: "Carol",
        6: "Eric"
    }
    
    # Cigars: available list is
    # "blends", "yellow monster", "pall mall", "blue master", "dunhill", "prince"
    # Clue 5: Pall Mall is in the third house.
    # Clue 2: Blue Master is in the fifth house.
    # Thus, houses 3 and 5 are fixed.
    # The remaining houses (1,2,4,6) must be assigned the remaining cigars
    # from {"blends", "yellow monster", "dunhill", "prince"}.
    remaining_cigars = ["blends", "yellow monster", "dunhill", "prince"]
    
    solution = None
    # Iterate over all assignments of the remaining cigars to houses 1,2,4,6.
    for perm in itertools.permutations(remaining_cigars):
        cigars = {}
        cigars[1] = perm[0]
        cigars[2] = perm[1]
        cigars[3] = "pall mall"      # Clue 5
        cigars[4] = perm[2]
        cigars[5] = "blue master"    # Clue 2
        cigars[6] = perm[3]
        
        # Now enforce the remaining clues:
        # Clue 1: "Arnold is somewhere to the left of the person who smokes blends."
        # Arnold is in house 2 so the house with "blends" must have a number > 2.
        house_blends = None
        # Clue 3: "Arnold is somewhere to the left of the Prince smoker."
        house_prince = None
        # Clue 4: "There is one house between the person who smokes Yellow Monster and the person who smokes many unique blends."
        house_yellow = None
        
        for house in range(1, 7):
            if cigars[house] == "blends":
                house_blends = house
            if cigars[house] == "prince":
                house_prince = house
            if cigars[house] == "yellow monster":
                house_yellow = house
        
        if house_blends is None or house_prince is None or house_yellow is None:
            continue
        
        if not (2 < house_blends):
            continue
        if not (2 < house_prince):
            continue
        if abs(house_blends - house_yellow) != 2:
            continue
        
        # All constraints satisfied; we found the solution.
        solution = {}
        for h in range(1, 7):
            solution[h] = {"Name": names[h], "Cigar": cigars[h]}
        break

    return solution

def main():
    sol = solve_puzzle()
    output = {
        "solution": {
            "header": ["House", "Name", "Cigar"],
            "rows": [
                [str(h), sol[h]["Name"], sol[h]["Cigar"]]
                for h in sorted(sol.keys())
            ]
        }
    }
    print(json.dumps(output))

if __name__ == '__main__':
    main()