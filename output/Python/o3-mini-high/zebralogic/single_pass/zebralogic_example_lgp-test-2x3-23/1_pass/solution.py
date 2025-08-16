#!/usr/bin/env python3
import json
import itertools

def main():
    # Define the attributes for the puzzle
    names = ["Eric", "Arnold"]
    children = ["Bella", "Fred"]
    foods = ["grilled cheese", "pizza"]
    
    # Houses are numbered 1 and 2 (left to right)
    houses = [1, 2]
    
    solutions = []
    
    # Enumerate all possible assignments for houses:
    # For each house we assign a Name, a Child, and a Food.
    for perm_names in itertools.permutations(names):
        for perm_children in itertools.permutations(children):
            for perm_foods in itertools.permutations(foods):
                # Create an assignment dictionary for houses 1 and 2
                assignment = {
                    1: {"House": "1", "Name": perm_names[0], "Children": perm_children[0], "Food": perm_foods[0]},
                    2: {"House": "2", "Name": perm_names[1], "Children": perm_children[1], "Food": perm_foods[1]}
                }
                
                # Constraint 1: The person who is a pizza lover is Arnold.
                # Find the house with pizza and check the name.
                pizza_house = None
                for i in houses:
                    if assignment[i]["Food"] == "pizza":
                        pizza_house = i
                if pizza_house is None or assignment[pizza_house]["Name"] != "Arnold":
                    continue
                
                # Constraint 2: The person who loves eating grilled cheese is directly left of the person whose child is named Fred.
                # With houses 1 and 2, the only possibility is that house 1 has grilled cheese and house 2's child is Fred.
                if assignment[1]["Food"] == "grilled cheese" and assignment[2]["Children"] == "Fred":
                    solutions.append(assignment)
    
    # We expect one unique solution. If a solution is found, output it.
    if solutions:
        sol = solutions[0]
        result = {
            "solution": {
                "header": ["House", "Name", "Children", "Food"],
                "rows": [
                    [sol[1]["House"], sol[1]["Name"], sol[1]["Children"], sol[1]["Food"]],
                    [sol[2]["House"], sol[2]["Name"], sol[2]["Children"], sol[2]["Food"]]
                ]
            }
        }
        print(json.dumps(result))
    else:
        print(json.dumps({"solution": "No solution found"}))

if __name__ == "__main__":
    main()