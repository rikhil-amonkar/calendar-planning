import z3
from z3 import *

def main():
    # Define the cities and their durations
    all_cities = ["Geneva", "Istanbul", "Vienna", "Riga", "Brussels", "Madrid", "Vilnius", "Venice", "Munich", "Reykjavik"]
    duration = {
        "Geneva": 4,
        "Istanbul": 4,
        "Vienna": 4,
        "Riga": 2,
        "Brussels": 2,
        "Madrid": 4,
        "Vilnius": 4,
        "Venice": 5,
        "Munich": 5,
        "Reykjavik": 2
    }
    
    # Fixed positions
    pos0 = "Geneva"
    pos9 = "Brussels"
    
    # Remaining cities for positions 1 to 8
    remaining_cities = ["Istanbul", "Vienna", "Riga", "Madrid", "Vilnius", "Venice", "Munich", "Reykjavik"]
    
    # Build the directed flight set
    flight_list = [
        "Munich and Vienna", 
        "Istanbul and Brussels", 
        "Vienna and Vilnius", 
        "Madrid and Munich", 
        "Venice and Brussels", 
        "Riga and Brussels", 
        "Geneva and Istanbul", 
        "Munich and Reykjavik", 
        "Vienna and Istanbul", 
        "Riga and Istanbul", 
        "Reykjavik and Vienna", 
        "Venice and Munich", 
        "Madrid and Venice", 
        "Vilnius and Istanbul", 
        "Venice and Vienna", 
        "Venice and Istanbul", 
        "from Reykjavik to Madrid", 
        "from Riga to Munich", 
        "Munich and Istanbul", 
        "Reykjavik and Brussels", 
        "Vilnius and Brussels", 
        "from Vilnius to Munich", 
        "Madrid and Vienna", 
        "Vienna and Riga", 
        "Geneva and Vienna", 
        "Madrid and Brussels", 
        "Vienna and Brussels", 
        "Geneva and Brussels", 
        "Geneva and Madrid", 
        "Munich and Brussels", 
        "Madrid and Istanbul", 
        "Geneva and Munich", 
        "from Riga to Vilnius"
    ]
    
    directed_edges = set()
    for s in flight_list:
        if s.startswith("from"):
            parts = s.split()
            if len(parts) == 4:
                A = parts[1]
                B = parts[3]
                directed_edges.add((A, B))
        else:
            if " and " in s:
                parts = s.split(" and ")
                A = parts[0].strip()
                B = parts[1].strip()
                directed_edges.add((A, B))
                directed_edges.add((B, A))
    
    # Create Z3 solver and variables
    s = Solver()
    # Positions 1 to 8: each is an integer index in [0,7] representing the city in remaining_cities
    pos_vars = [Int(f'pos_{i}') for i in range(1, 9)]
    
    # Each pos_var must be between 0 and 7
    for i in range(8):
        s.add(pos_vars[i] >= 0, pos_vars[i] <= 7)
    
    # All pos_vars are distinct
    s.add(Distinct(pos_vars))
    
    # Build city_at: an array of 10, index 0 and 9 are fixed
    city_at = [None] * 10
    city_at[0] = "Geneva"
    city_at[9] = "Brussels"
    # For positions 1 to 8, city_at[i] = remaining_cities[ pos_vars[i-1] ]
    for i in range(1, 9):
        idx = i - 1  # index in pos_vars
        # We use a function to map the Z3 variable to the city name
        city_at[i] = remaining_cities[ pos_vars[idx] ]
    
    # Build the start days: start[0]=1, then start[i] = start[i-1] + (duration[city_at[i-1]] - 1)
    start_days = [Int(f'start_{i}') for i in range(10)]
    s.add(start_days[0] == 1)
    for i in range(1, 10):
        # We need to express: duration[city_at[i-1]]
        # But city_at[i-1] is a string that depends on the Z3 variable
        # We use a dictionary of conditions for each possible city
        expr = None
        for city in remaining_cities + ["Geneva", "Brussels"]:
            # Skip cities that are not possible? Actually, for i-1 in [0,8]: 
            #   if i-1==0: city_at[0] is fixed to "Geneva"
            #   if i-1==9: not possible because i-1 from 0 to 8
            if i-1 == 0:
                # city_at[0] is "Geneva", duration 4
                cond = (start_days[i] == start_days[i-1] + (4 - 1))
                s.add(cond)
                break
            elif i-1 == 9:
                # not possible
                pass
            else:
                # For positions 1 to 8, city_at[i-1] is one of the remaining_cities
                # We are at index i-1 (which is from 1 to 8)
                # Create a condition: if city_at[i-1] == city, then start_days[i] = start_days[i-1] + (duration[city]-1)
                if expr is None:
                    expr = If(city_at[i-1] == city, start_days[i] == start_days[i-1] + (duration[city]-1), False)
                else:
                    expr = Or(expr, If(city_at[i-1] == city, start_days[i] == start_days[i-1] + (duration[city]-1), False))
        if i-1 != 0:
            s.add(expr)
    
    # Constraints for Venice: must be at a position i in [1,8] and start_days[i] == 7
    venice_constraint = Or([And(city_at[i] == "Venice", start_days[i] == 7) for i in range(1,9)])
    s.add(venice_constraint)
    
    # Constraints for Vilnius: must be at a position i in [1,8] and start_days[i] == 20
    vilnius_constraint = Or([And(city_at[i] == "Vilnius", start_days[i] == 20) for i in range(1,9)])
    s.add(vilnius_constraint)
    
    # Flight constraints: for each i from 0 to 8, (city_at[i], city_at[i+1]) must be in directed_edges
    for i in range(0,9):
        # We'll create an OR over all edges that are in directed_edges
        # But we have to use the actual city names
        expr = Or([And(city_at[i] == A, city_at[i+1] == B) for (A,B) in directed_edges])
        s.add(expr)
    
    # Check and get the model
    if s.check() == sat:
        model = s.model()
        # Get the actual assignment for the positions
        city_at_assign = [None] * 10
        city_at_assign[0] = "Geneva"
        city_at_assign[9] = "Brussels"
        # For positions 1 to 8
        actual_remaining = [None] * 8
        for i in range(1,9):
            idx_var = pos_vars[i-1]
            idx_val = model[idx_var].as_long()
            city_name = remaining_cities[idx_val]
            city_at_assign[i] = city_name
            actual_remaining[i-1] = city_name
        
        # Now compute the start_days_assign and end_days
        start_assign = [0] * 10
        end_assign = [0] * 10
        start_assign[0] = 1
        end_assign[0] = start_assign[0] + duration[city_at_assign[0]] - 1
        for i in range(1,10):
            start_assign[i] = end_assign[i-1]  # because end_assign[i-1] = start_assign[i-1] + dur - 1, and next starts on that day
            end_assign[i] = start_assign[i] + duration[city_at_assign[i]] - 1
        
        # Build the itinerary
        itinerary = []
        for i in range(10):
            s_day = start_assign[i]
            e_day = end_assign[i]
            if s_day == e_day:
                day_str = f"Day {s_day}"
            else:
                day_str = f"Day {s_day}-{e_day}"
            itinerary.append( {"day_range": day_str, "place": city_at_assign[i]} )
            if i < 9:
                # Flight out on e_day
                itinerary.append( {"day_range": f"Day {e_day}", "place": city_at_assign[i]} )
                itinerary.append( {"day_range": f"Day {e_day}", "place": city_at_assign[i+1]} )
        
        # Output as JSON
        import json
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()