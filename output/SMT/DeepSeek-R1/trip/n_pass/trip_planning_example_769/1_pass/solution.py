from z3 import *

def main():
    # Define the positions for the first four cities
    pos0, pos1, pos2, pos3 = Ints('pos0 pos1 pos2 pos3')
    pos = [pos0, pos1, pos2, pos3]
    
    s = Solver()
    
    # Each position must be between 0 and 3 (inclusive)
    for p in pos:
        s.add(p >= 0, p <= 3)
    
    s.add(Distinct(pos0, pos1, pos2, pos3))
    
    # Days for each city: Porto(0)=5, Prague(1)=4, Reykjavik(2)=4, Munich(3)=4
    days_arr = [5, 4, 4, 4]
    
    # Calculate prefix sums for the first three cities
    T0 = days_arr[pos0]
    T1 = T0 + days_arr[pos1]
    T2 = T1 + days_arr[pos2]
    
    # Start days for each position in the sequence
    S0 = 1
    S1 = T0  # 1 + T0 - 1
    S2 = 1 + T1 - 2
    S3 = 1 + T2 - 3
    
    # Reykjavik is city 2, Munich is city 3
    R_start = If(pos0 == 2, S0,
                If(pos1 == 2, S1,
                If(pos2 == 2, S2,
                S3)))
    
    M_start = If(pos0 == 3, S0,
                If(pos1 == 3, S1,
                If(pos2 == 3, S2,
                S3)))
    
    # Constraints for Reykjavik and Munich
    s.add(R_start <= 7)         # Reykjavik must start by day 7
    s.add(M_start >= 4)          # Munich must start on or after day 4
    s.add(M_start <= 10)         # Munich must start by day 10
    
    # Allowed direct flight pairs (undirected)
    allowed_pairs = [
        (0, 3), (3, 0),  # Porto and Munich
        (1, 2), (2, 1),  # Prague and Reykjavik
        (1, 3), (3, 1),  # Prague and Munich
        (2, 3), (3, 2)   # Reykjavik and Munich
    ]
    
    # Constraints for consecutive cities to have direct flights
    for i in range(3):
        cons = []
        for a, b in allowed_pairs:
            cons.append(And(pos[i] == a, pos[i+1] == b))
        s.add(Or(cons))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        order = [m.evaluate(p).as_long() for p in pos]
        city_names = ["Porto", "Prague", "Reykjavik", "Munich"]
        first_four = [city_names[idx] for idx in order]
        cities = first_four + ["Amsterdam", "Santorini"]
        
        # Calculate end days for the first four cities
        days_vals = [days_arr[idx] for idx in order]
        E0 = 1 + days_vals[0] - 1
        E1 = E0 + days_vals[1] - 1
        E2 = E1 + days_vals[2] - 1
        E3 = E2 + days_vals[3] - 1  # should be 14
        
        starts = [1, E0, E1, E2, 14, 15]
        ends = [E0, E1, E2, 14, 15, 16]
        
        itinerary = []
        for i in range(6):
            s_day = starts[i]
            e_day = ends[i]
            if s_day == e_day:
                day_str = f"Day {s_day}"
            else:
                day_str = f"Day {s_day}-{e_day}"
            itinerary.append({"day_range": day_str, "place": cities[i]})
            
            if i < 5:
                itinerary.append({"day_range": f"Day {e_day}", "place": cities[i]})
                itinerary.append({"day_range": f"Day {e_day}", "place": cities[i+1]})
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()