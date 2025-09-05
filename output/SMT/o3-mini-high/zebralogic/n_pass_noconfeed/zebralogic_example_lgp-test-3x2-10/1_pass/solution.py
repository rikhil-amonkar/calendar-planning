from z3 import *
import json

def main():
    solver = Solver()
    houses = 3
    # Create Z3 integer variables for the names and heights of each house.
    # We encode names as: 0 = Eric, 1 = Arnold, 2 = Peter.
    # We encode heights as: 0 = short, 1 = very short, 2 = average.
    names = [Int(f"name_{i}") for i in range(houses)]
    heights = [Int(f"height_{i}") for i in range(houses)]
    
    # Each variable must take a value in {0, 1, 2}.
    for i in range(houses):
        solver.add(Or(names[i] == 0, names[i] == 1, names[i] == 2))
        solver.add(Or(heights[i] == 0, heights[i] == 1, heights[i] == 2))
    
    # All houses have a distinct name and a distinct height.
    solver.add(Distinct(names))
    solver.add(Distinct(heights))
    
    # Clue 1: Eric is not in the first house.
    # (Eric is encoded as 0; house 1 corresponds to index 0.)
    solver.add(names[0] != 0)
    
    # Clue 4: Arnold is not in the first house.
    # (Arnold is encoded as 1.)
    solver.add(names[0] != 1)
    
    # Clue 3: The person who is very short is Eric.
    # This means: if a house’s occupant is Eric (0), then that house’s height must be very short (1),
    # and conversely if a house’s height is very short (1), then its occupant must be Eric.
    for i in range(houses):
        solver.add(Implies(names[i] == 0, heights[i] == 1))
        solver.add(Implies(heights[i] == 1, names[i] == 0))
    
    # Clue 2: The person who is very short is somewhere to the left of the person who is short.
    # "very short" is encoded as 1 and "short" as 0.
    # Since houses are ordered from left to right (indices 0, 1, 2),
    # we enforce that the house with height 1 must come before the house with height 0.
    # Given exactly one house has height 1 and one has height 0 (from distinctness),
    # the valid possibilities (by position) are:
    #   - House 1 (index 0) is very short and House 2 (index 1) is short,
    #   - House 1 (index 0) is very short and House 3 (index 2) is short, or
    #   - House 2 (index 1) is very short and House 3 (index 2) is short.
    # However, note that house 1 (index 0) already cannot be very short (since its occupant is not Eric).
    # Thus, the only possibility is: house 2 (index 1) is very short and house 3 (index 2) is short.
    valid_order = Or(
        And(heights[0] == 1, heights[1] == 0),
        And(heights[0] == 1, heights[2] == 0),
        And(heights[1] == 1, heights[2] == 0)
    )
    solver.add(valid_order)
    
    if solver.check() == sat:
        model = solver.model()
        # Define mappings from our numerical encoding to the actual names and heights.
        name_mapping = {0: "Eric", 1: "Arnold", 2: "Peter"}
        height_mapping = {0: "short", 1: "very short", 2: "average"}
        
        # Build the solution rows in the required order.
        rows = []
        for i in range(houses):
            house_num = str(i + 1)  # House numbers as 1-indexed strings.
            name_val = model.evaluate(names[i]).as_long()
            height_val = model.evaluate(heights[i]).as_long()
            rows.append([house_num, name_mapping[name_val], height_mapping[height_val]])
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Height"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        # In the unlikely event there is no solution.
        print(json.dumps({"solution": {"header": ["House", "Name", "Height"], "rows": []}}))
        
if __name__ == "__main__":
    main()