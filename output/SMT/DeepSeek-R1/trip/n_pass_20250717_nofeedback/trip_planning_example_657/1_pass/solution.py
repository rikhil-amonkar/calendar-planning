from z3 import *
import json

def main():
    # Define city mappings
    cities = ["Frankfurt", "Manchester", "Valencia", "Naples", "Oslo", "Vilnius"]
    F = 0; M = 1; V = 2; N = 3; O = 4; W = 5

    # Direct flights (as tuples of city indices, including both directions)
    direct_flights = [
        (V, F), (F, V), 
        (M, F), (F, M),
        (N, M), (M, N),
        (N, F), (F, N),
        (N, O), (O, N),
        (O, F), (F, O),
        (W, F), (F, W),
        (O, W), (W, O),
        (M, O), (O, M),
        (V, N), (N, V)
    ]
    # Allow staying in the same city: add (c, c) for each city
    allowed_pairs_with_self = direct_flights + [(c, c) for c in [F, M, V, N, O, W]]
    
    # Create solver and variables
    s = Solver()
    end_city = [Int(f'end_city_{i}') for i in range(16)]
    for i in range(16):
        s.add(And(end_city[i] >= 0, end_city[i] <= 5))
    
    # Constraint: Last four days in Frankfurt (days 13 to 16: indices 12 to 15)
    s.add(end_city[12] == F)
    s.add(end_city[13] == F)
    s.add(end_city[14] == F)
    s.add(end_city[15] == F)
    
    # Constraint: Vilnius wedding on day 12 or 13 (indices 11 or 12)
    s.add(Or(end_city[10] == W, end_city[11] == W))
    
    # Flight constraints: for consecutive days, either stay or fly directly
    for i in range(1, 16):
        constraints = []
        for (a, b) in allowed_pairs_with_self:
            constraints.append(And(end_city[i-1] == a, end_city[i] == b))
        s.add(Or(constraints))
    
    # Total days constraints
    def total_days(c):
        # Day 1 (index0): only end_city[0] counts
        day1 = If(end_city[0] == c, 1, 0)
        # Days 2 to 16: if either the previous end city or current end city is c, count 1
        other_days = [If(Or(end_city[i-1] == c, end_city[i] == c), 1, 0) for i in range(1, 16)]
        return day1 + sum(other_days)
    
    s.add(total_days(F) == 4)
    s.add(total_days(M) == 4)
    s.add(total_days(V) == 4)
    s.add(total_days(N) == 4)
    s.add(total_days(O) == 3)
    s.add(total_days(W) == 2)
    
    # Solve
    if s.check() == sat:
        model = s.model()
        # Build the itinerary
        itinerary = []
        # Day 1
        city_index0 = model.evaluate(end_city[0]).as_long()
        itinerary.append({"day": 1, "city": cities[city_index0]})
        # Days 2 to 16
        for day in range(2, 17):
            idx_prev = day - 2  # index for end_city of previous day (day-1)
            idx_curr = day - 1  # index for end_city of current day (day)
            start_city_val = model.evaluate(end_city[idx_prev]).as_long()
            end_city_val = model.evaluate(end_city[idx_curr]).as_long()
            if start_city_val != end_city_val:
                itinerary.append({"day": day, "city": cities[start_city_val]})
                itinerary.append({"day": day, "city": cities[end_city_val]})
            else:
                itinerary.append({"day": day, "city": cities[start_city_val]})
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()