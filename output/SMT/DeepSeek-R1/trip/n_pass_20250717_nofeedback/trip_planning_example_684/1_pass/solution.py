from z3 import *

def main():
    # Define the city indices
    AMS, EDI, BRU, VIE, BER, REK = 0, 1, 2, 3, 4, 5
    city_names = {
        AMS: "Amsterdam",
        EDI: "Edinburgh",
        BRU: "Brussels",
        VIE: "Vienna",
        BER: "Berlin",
        REK: "Reykjavik"
    }
    
    # Base array: duration - 1 for each city
    base_arr = [3, 4, 4, 4, 3, 4]  # [AMS, EDI, BRU, VIE, BER, REK]
    
    # Allowed direct flights as tuples (from, to)
    allowed_edges = set([
        (EDI, BER), (BER, EDI),
        (AMS, BER), (BER, AMS),
        (EDI, AMS), (AMS, EDI),
        (VIE, BER), (BER, VIE),
        (BER, BRU), (BRU, BER),
        (VIE, REK), (REK, VIE),
        (EDI, BRU), (BRU, EDI),
        (VIE, BRU), (BRU, VIE),
        (AMS, REK), (REK, AMS),
        (REK, BRU), (BRU, REK),
        (AMS, VIE), (VIE, AMS),
        (REK, BER), (BER, REK)
    ])
    
    # Z3 variables for the sequence of cities
    s0, s1, s2, s3, s4, s5 = Ints('s0 s1 s2 s3 s4 s5')
    s = [s0, s1, s2, s3, s4, s5]
    
    # Constraints list
    constraints = []
    
    # Each s_i is between 0 and 5 and all are distinct
    for si in s:
        constraints.append(And(si >= 0, si <= 5))
    constraints.append(Distinct(s))
    
    # Define base values for each position in the sequence
    base0 = If(s0 == AMS, base_arr[AMS],
            If(s0 == EDI, base_arr[EDI],
            If(s0 == BRU, base_arr[BRU],
            If(s0 == VIE, base_arr[VIE],
            If(s0 == BER, base_arr[BER], base_arr[REK]))))
    base1 = If(s1 == AMS, base_arr[AMS],
            If(s1 == EDI, base_arr[EDI],
            If(s1 == BRU, base_arr[BRU],
            If(s1 == VIE, base_arr[VIE],
            If(s1 == BER, base_arr[BER], base_arr[REK]))))
    base2 = If(s2 == AMS, base_arr[AMS],
            If(s2 == EDI, base_arr[EDI],
            If(s2 == BRU, base_arr[BRU],
            If(s2 == VIE, base_arr[VIE],
            If(s2 == BER, base_arr[BER], base_arr[REK]))))
    base3 = If(s3 == AMS, base_arr[AMS],
            If(s3 == EDI, base_arr[EDI],
            If(s3 == BRU, base_arr[BRU],
            If(s3 == VIE, base_arr[VIE],
            If(s3 == BER, base_arr[BER], base_arr[REK]))))
    base4 = If(s4 == AMS, base_arr[AMS],
            If(s4 == EDI, base_arr[EDI],
            If(s4 == BRU, base_arr[BRU],
            If(s4 == VIE, base_arr[VIE],
            If(s4 == BER, base_arr[BER], base_arr[REK]))))
    base5 = If(s5 == AMS, base_arr[AMS],
            If(s5 == EDI, base_arr[EDI],
            If(s5 == BRU, base_arr[BRU],
            If(s5 == VIE, base_arr[VIE],
            If(s5 == BER, base_arr[BER], base_arr[REK]))))
    bases = [base0, base1, base2, base3, base4, base5]
    
    # Prefix sums: prefix[i] = sum of bases[0..i-1]
    prefix0 = 0
    prefix1 = prefix0 + base0
    prefix2 = prefix1 + base1
    prefix3 = prefix2 + base2
    prefix4 = prefix3 + base3
    prefix5 = prefix4 + base4
    prefix6 = prefix5 + base5
    prefixes = [prefix0, prefix1, prefix2, prefix3, prefix4, prefix5, prefix6]
    
    # Total days must be 23: prefix6 should be 22 because 1 + 22 = 23
    constraints.append(prefix6 == 22)
    
    # Fixed start constraints:
    # AMS (index0) must have start day = 5 -> prefix_i = 4 for the position i where AMS is
    for i, prefix_val in enumerate(prefixes[:6]):
        constraints.append(If(s[i] == AMS, prefix_val == 4, True))
    
    # BER (index4) must have start day = 16 -> prefix_i = 15
    for i, prefix_val in enumerate(prefixes[:6]):
        constraints.append(If(s[i] == BER, prefix_val == 15, True))
    
    # REK (index5) must have start day in [8,16] -> prefix_i in [7,15]
    for i, prefix_val in enumerate(prefixes[:6]):
        constraints.append(If(s[i] == REK, And(prefix_val >= 7, prefix_val <= 15), True))
    
    # Flight constraints: consecutive cities must be connected by a direct flight
    for i in range(5):
        edge_constraint = Or([And(s[i] == a, s[i+1] == b) for (a, b) in allowed_edges])
        constraints.append(edge_constraint)
    
    # Solve the constraints
    solver = Solver()
    solver.add(constraints)
    if solver.check() == sat:
        model = solver.model()
        seq = [model.evaluate(si).as_long() for si in s]
        
        # Compute prefix values from the model
        base_vals = [base_arr[city] for city in seq]
        prefix_val = [0]
        for i in range(6):
            next_val = prefix_val[-1] + base_vals[i]
            prefix_val.append(next_val)
        
        # Build the itinerary: for each day, list the cities we are in
        days = [[] for _ in range(24)]  # 1..23
        
        for i in range(6):
            city_idx = seq[i]
            city_name = city_names[city_idx]
            start_day = 1 + prefix_val[i]
            end_day = 1 + prefix_val[i] + base_vals[i]  # last day of stay
            for d in range(start_day, end_day + 1):
                if d < 24:
                    days[d].append(city_name)
        
        # Prepare the itinerary as a list of dictionaries
        itinerary = []
        for d in range(1, 24):
            itinerary.append({"day": d, "place": days[d]})
        
        result = {'itinerary': itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()