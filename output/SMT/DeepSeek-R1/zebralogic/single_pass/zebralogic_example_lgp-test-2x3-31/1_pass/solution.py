from z3 import *

def main():
    # Define the variables for attributes of two houses
    n1, n2 = Ints('n1 n2')  # names for house 1 and house 2
    s1, s2 = Ints('s1 s2')  # sports for house 1 and house 2
    h1, h2 = Ints('h1 h2')  # hobbies for house 1 and house 2

    solver = Solver()

    # Each attribute must be 0 or 1
    solver.add(n1 >= 0, n1 <= 1)
    solver.add(n2 >= 0, n2 <= 1)
    solver.add(s1 >= 0, s1 <= 1)
    solver.add(s2 >= 0, s2 <= 1)
    solver.add(h1 >= 0, h1 <= 1)
    solver.add(h2 >= 0, h2 <= 1)

    # All attributes are unique per category
    solver.add(n1 != n2)
    solver.add(s1 != s2)
    solver.add(h1 != h2)

    # Clue 1: Gardening hobby implies Arnold (hobby=1 => name=1)
    solver.add(Implies(h1 == 1, n1 == 1))
    solver.add(Implies(h2 == 1, n2 == 1))

    # Clue 2: Photography enthusiast (hobby=0) not in house 1
    solver.add(h1 != 0)

    # Clue 3: Soccer enthusiast (sport=1) not in house 1
    solver.add(s1 != 1)

    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        
        # Convert model values to integers
        n1_val = model[n1].as_long()
        n2_val = model[n2].as_long()
        s1_val = model[s1].as_long()
        s2_val = model[s2].as_long()
        h1_val = model[h1].as_long()
        h2_val = model[h2].as_long()
        
        # Map integers to attribute strings
        name_map = {0: "Eric", 1: "Arnold"}
        sport_map = {0: "basketball", 1: "soccer"}
        hobby_map = {0: "photography", 1: "gardening"}
        
        # Create rows for the solution
        row1 = ["1", name_map[n1_val], sport_map[s1_val], hobby_map[h1_val]]
        row2 = ["2", name_map[n2_val], sport_map[s2_val], hobby_map[h2_val]]
        
        # Build the solution dictionary
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "FavoriteSport", "Hobby"],
                "rows": [row1, row2]
            }
        }
        
        # Output as JSON string
        import json
        print(json.dumps(solution_dict, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()