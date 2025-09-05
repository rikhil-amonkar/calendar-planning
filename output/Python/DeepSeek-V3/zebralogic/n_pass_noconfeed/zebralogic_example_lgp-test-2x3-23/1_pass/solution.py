import json

def main():
    # Define the attributes
    houses = [1, 2]
    names = ["Eric", "Arnold"]
    children = ["Bella", "Fred"]
    foods = ["grilled cheese", "pizza"]
    
    # Generate all possible assignments
    for name_assignments in generate_permutations(names, houses):
        for child_assignments in generate_permutations(children, houses):
            for food_assignments in generate_permutations(foods, houses):
                # Check all constraints
                if satisfies_constraints(name_assignments, child_assignments, food_assignments):
                    # Format the solution
                    solution = format_solution(name_assignments, child_assignments, food_assignments)
                    print(json.dumps(solution, indent=2))
                    return
    
    # If no solution found
    print(json.dumps({"solution": {"header": [], "rows": []}}, indent=2))

def generate_permutations(items, positions):
    """Generate all possible permutations of items to positions"""
    from itertools import permutations
    for perm in permutations(items):
        yield dict(zip(positions, perm))

def satisfies_constraints(names, children, foods):
    """Check if the current assignment satisfies all constraints"""
    # Constraint 1: The person who is a pizza lover is Arnold.
    for house, food in foods.items():
        if food == "pizza" and names[house] != "Arnold":
            return False
    
    # Constraint 2: The person who loves eating grilled cheese is directly left of the person's child is named Fred.
    for house in [1]:  # Only house 1 can be left of house 2
        if foods[house] == "grilled cheese":
            # Check if the child in the right house (house + 1) is Fred
            if children[house + 1] == "Fred":
                return True
        elif house == 1 and foods[2] == "grilled cheese":
            # Grilled cheese is in house 2, so it can't be left of anyone
            return False
    
    return False

def format_solution(names, children, foods):
    """Format the solution in the required JSON structure"""
    rows = []
    for house in sorted(names.keys()):
        rows.append([
            str(house),
            names[house],
            children[house],
            foods[house]
        ])
    
    return {
        "solution": {
            "header": ["House", "Name", "Children", "Food"],
            "rows": rows
        }
    }

if __name__ == "__main__":
    main()