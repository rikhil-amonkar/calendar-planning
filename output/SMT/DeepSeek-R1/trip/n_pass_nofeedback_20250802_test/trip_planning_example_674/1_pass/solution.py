from z3 import *
import json

def main():
    # Create solver and variables
    c0, c1, c2, c3, c4, c5 = Ints('c0 c1 c2 c3 c4 c5')
    s = Solver()
    
    # Each city variable must be between 0 and 5
    s.add(c0 >= 0, c0 <= 5)
    s.add(c1 >= 0, c1 <= 5)
    s.add(c2 >= 0, c2 <= 5)
    s.add(c3 >= 0, c3 <= 5)
    s.add(c4 >= 0, c4 <= 5)
    s.add(c5 >= 0, c5 <= 5)
    
    # All cities must be distinct
    s.add(Distinct(c0, c1, c2, c3, c4, c5))
    
    # Function to get days for a city
    def day_val(city):
        return If(city == 0, 2,
                If(city == 1, 3,
                 If(city == 2, 4,
                  If(city == 3, 4,
                   If(city == 4, 2,
                    4)))))  # city 5 (Budapest) has 4 days
    
    d0 = day_val(c0)
    d1 = day_val(c1)
    d2 = day_val(c2)
    d3 = day_val(c3)
    d4 = day_val(c4)
    d5 = day_val(c5)
    
    # Start days for each position in the itinerary
    s0 = 1
    s1 = s0 + d0 - 1
    s2 = s1 + d1 - 1
    s3 = s2 + d2 - 1
    s4 = s3 + d3 - 1
    s5 = s4 + d4 - 1
    
    # Final day constraint: last city ends on day 14
    s.add(s5 + d5 == 15)
    
    # Event constraints for each city based on position
    cities = [c0, c1, c2, c3, c4, c5]
    s_days = [s0, s1, s2, s3, s4, s5]
    for i in range(6):
        city = cities[i]
        s_day = s_days[i]
        # Helsinki must start on or before day 2
        s.add(If(city == 0, s_day <= 2, True))
        # Warsaw must start between days 7 and 11
        s.add(If(city == 1, And(s_day >= 7, s_day <= 11), True))
        # Reykjavik must start between days 7 and 9
        s.add(If(city == 4, And(s_day >= 7, s_day <= 9), True))
    
    # Flight constraints: allowed direct flights
    allowed_pairs = []
    undirected_edges = [
        (0,4), (5,1), (2,3), (0,3), (0,2), (0,5), (0,1),
        (4,1), (4,5), (5,2), (1,2), (1,3)
    ]
    for a, b in undirected_edges:
        allowed_pairs.append((a, b))
        allowed_pairs.append((b, a))
    allowed_pairs.append((4, 2))  # Directed flight: Reykjavik to Madrid
    
    # Apply flight constraints for consecutive cities
    consecutive_pairs = [(c0, c1), (c1, c2), (c2, c3), (c3, c4), (c4, c5)]
    for pair in consecutive_pairs:
        a, b = pair
        constraints = []
        for (x, y) in allowed_pairs:
            constraints.append(And(a == x, b == y))
        s.add(Or(constraints))
    
    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        c0_val = m.eval(c0).as_long()
        c1_val = m.eval(c1).as_long()
        c2_val = m.eval(c2).as_long()
        c3_val = m.eval(c3).as_long()
        c4_val = m.eval(c4).as_long()
        c5_val = m.eval(c5).as_long()
        
        # Map city indices to names
        city_names = {
            0: "Helsinki",
            1: "Warsaw",
            2: "Madrid",
            3: "Split",
            4: "Reykjavik",
            5: "Budapest"
        }
        perm = [c0_val, c1_val, c2_val, c3_val, c4_val, c5_val]
        days_arr = [2, 3, 4, 4, 2, 4]
        d_vals = [days_arr[city] for city in perm]
        
        # Compute start days for each city
        s_vals = [1]
        for i in range(5):
            next_s = s_vals[-1] + d_vals[i] - 1
            s_vals.append(next_s)
        
        # Build itinerary
        itinerary = []
        for d in range(1, 15):
            # Check each segment for occupancy
            if d <= s_vals[1]:
                itinerary.append({"day": d, "place": city_names[perm[0]]})
            if s_vals[1] <= d <= s_vals[2]:
                itinerary.append({"day": d, "place": city_names[perm[1]]})
            if s_vals[2] <= d <= s_vals[3]:
                itinerary.append({"day": d, "place": city_names[perm[2]]})
            if s_vals[3] <= d <= s_vals[4]:
                itinerary.append({"day": d, "place": city_names[perm[3]]})
            if s_vals[4] <= d <= s_vals[5]:
                itinerary.append({"day": d, "place": city_names[perm[4]]})
            if d >= s_vals[5]:
                itinerary.append({"day": d, "place": city_names[perm[5]]})
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()