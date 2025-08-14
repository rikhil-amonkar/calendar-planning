#!/usr/bin/env python3
import itertools
import json

def main():
    # Define houses and attributes based on the puzzle
    houses = [1, 2]  # House positions: 1 is left, 2 is right
    names = ["Eric", "Arnold"]
    genres = ["science fiction", "mystery"]

    # Generate all possible assignments of names and book genres to houses
    solutions = []
    for name_perm in itertools.permutations(names):
        for genre_perm in itertools.permutations(genres):
            # Build an assignment dictionary keyed by house number
            assignment = {house: {"Name": name, "favorite book genres": genre} 
                          for house, name, genre in zip(houses, name_perm, genre_perm)}
            
            # Check the clue: "Eric is directly left of the person who loves mystery books."
            valid = False
            for i in range(len(houses) - 1):
                current_house = houses[i]
                next_house = houses[i + 1]
                if assignment[current_house]["Name"] == "Eric" and assignment[next_house]["favorite book genres"] == "mystery":
                    valid = True
                    break

            if valid:
                solutions.append(assignment)
    
    # Assume there is exactly one solution
    if solutions:
        solution = solutions[0]
        header = ["House", "Name", "favorite book genres"]
        rows = []
        for house in sorted(solution.keys()):
            row = [str(house), solution[house]["Name"], solution[house]["favorite book genres"]]
            rows.append(row)
        
        output = {"solution": {"header": header, "rows": rows}}
        print(json.dumps(output, indent=2))
    else:
        print(json.dumps({"solution": None}))

if __name__ == "__main__":
    main()