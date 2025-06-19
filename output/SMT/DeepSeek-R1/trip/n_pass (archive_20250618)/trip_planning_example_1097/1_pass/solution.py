from z3 import Solver, Int, Distinct, And, Or, sat
import json

def main():
    # City names and their indices
    city_names = ["Reykjavik", "Riga", "Oslo", "Lyon", "Dubrovnik", "Madrid", "Warsaw", "London"]
    n = len(city_names)
    city_index = {name: idx for idx, name in enumerate(city_names)}
    durations = [4, 2, 3, 5, 2, 2, 4, 3]  # Corresponding to city_names order

    # Flight connections: list of direct flight pairs (undirected)
    flight_strings = [
        "Warsaw and Reykjavik",
        "Oslo and Madrid",
        "Warsaw and Riga",
        "Lyon and London",
        "Madrid and London",
        "Warsaw and London",
        "from Reykjavik to Madrid",
        "Warsaw and Oslo",
        "Oslo and Dubrovnik",
        "Oslo and Reykjavik",
        "Riga and Oslo",
        "Oslo and Lyon",
        "Oslo and London",
        "London and Reykjavik",
        "Warsaw and Madrid",
        "Madrid and Lyon",
        "Dubrovnik and Madrid"
    ]
    
    # Build set of directed flight pairs (both directions for undirected flights)
    allowed_directed = set()
    for s_str in flight_strings:
        words = s_str.split()
        found = [word for word in words if word in city_names]
        if len(found) == 2:
            a, b = found
            idx_a = city_index[a]
            idx_b = city_index[b]
            allowed_directed.add((idx_a, idx_b))
            allowed_directed.add((idx_b, idx_a))
    
    # Initialize Z3 solver and variables
    s = Solver()
    Seq = [Int(f'Seq_{i}') for i in range(n)]
    S = [Int(f'S_{i}') for i in range(n)]
    
    # Constraints: Seq is a permutation of 0..7
    s.add([And(Seq[i] >= 0, Seq[i] < n) for i in range(n)])
    s.add(Distinct(Seq))
    
    # Start day constraints: S[0]=1, and S[i] = S[i-1] + duration of previous city - 1
    s.add(S[0] == 1)
    for i in range(1, n):
        prev_city_dur = durations[Seq[i-1]]
        s.add(S[i] == S[i-1] + prev_city_dur - 1)
    
    # Constraints for Riga (index 1) and Dubrovnik (index 4)
    riga_constraint = Or([And(Seq[i] == 1, S[i] >= 3, S[i] <= 5) for i in range(n)])
    dubrovnik_constraint = Or([And(Seq[i] == 4, S[i] >= 6, S[i] <= 8) for i in range(n)])
    s.add(riga_constraint, dubrovnik_constraint)
    
    # Flight constraints between consecutive cities
    for i in range(n - 1):
        conds = []
        for (a, b) in allowed_directed:
            conds.append(And(Seq[i] == a, Seq[i+1] == b))
        s.add(Or(conds))
    
    # Check for solution and output
    if s.check() == sat:
        m = s.model()
        seq_val = [m.evaluate(Seq[i]).as_long() for i in range(n)]
        start_days = [1]
        for i in range(1, n):
            prev_city_idx = seq_val[i-1]
            dur_prev = durations[prev_city_idx]
            start_days.append(start_days[i-1] + dur_prev - 1)
        
        itinerary = []
        for i in range(n):
            city_idx = seq_val[i]
            city_name = city_names[city_idx]
            start = start_days[i]
            dur = durations[city_idx]
            end = start + dur - 1
            
            # Add the continuous stay record
            itinerary.append({"day_range": f"Day {start}-{end}", "place": city_name})
            if i != 0:
                itinerary.append({"day_range": f"Day {start}", "place": city_name})
            if i != n - 1:
                itinerary.append({"day_range": f"Day {end}", "place": city_name})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()