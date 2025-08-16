#!/usr/bin/env python3
import json
import itertools

def main():
    # Define houses, persons, and vacations
    houses = [1, 2]
    persons = ["Arnold", "Eric"]
    vacations = ["beach", "mountain"]
    
    solution_found = None
    
    # Iterate over possible assignments
    for person_perm in itertools.permutations(persons):
        for vacation_perm in itertools.permutations(vacations):
            # The houses are ordered from left to right (index 0 is House 1, index 1 is House 2)
            # Find the positions of "Arnold" and the person who loves "beach"
            house_index_arnold = person_perm.index("Arnold")
            house_index_beach = vacation_perm.index("beach")
            # Constraint: "Arnold is somewhere to the right of the person who loves beach vacations"
            if house_index_arnold > house_index_beach:
                solution_found = []
                for i, (name, vacation) in enumerate(zip(person_perm, vacation_perm)):
                    solution_found.append([str(i + 1), name, vacation])
                break
        if solution_found is not None:
            break

    result = {
        "solution": {
            "header": ["House", "Name", "Vacation"],
            "rows": solution_found
        }
    }
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()