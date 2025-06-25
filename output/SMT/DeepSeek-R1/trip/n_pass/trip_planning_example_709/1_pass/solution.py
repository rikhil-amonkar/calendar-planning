from z3 import *
import json

def main():
    # City mapping
    cities = ["Helsinki", "Valencia", "Dubrovnik", "Porto", "Prague", "Reykjavik"]
    # City numbers: 0,1,2,3,4,5

    # Days required for each city
    days_req = [4, 5, 4, 3, 3, 4]  # index 0 to 5

    # Allowed direct flights (both directions)
    allowed_pairs = [
        (0,4), (4,0), # H-Prague
        (4,1), (1,4), # Prague-Valencia
        (1,3), (3,1), # Valencia-Porto
        (0,5), (5,0), # H-Reykjavik
        (2,0), (0,2), # Dubrovnik-H
        (5,4), (4,5)  # Reykjavik-Prague
    ]

    # Create the sequence: 6 positions
    seq = [Int(f"seq_{i}") for i in range(6)]
    s = [Int(f"s_{i}") for i in range(6)]   # start days for each position

    solver = Solver()

    # Each element in seq must be between 0 and 5
    for i in range(6):
        solver.add(And(seq[i] >= 0, seq[i] < 6))

    # Distinct constraint for seq
    solver.add(Distinct(seq))

    # Consecutive constraint: for each i from 0 to 4, (seq[i], seq[i+1]) must be in allowed_pairs.
    for i in range(5):
        conds = []
        for pair in allowed_pairs:
            conds.append(And(seq[i] == pair[0], seq[i+1] == pair[1]))
        solver.add(Or(conds))

    # Define a function to get the required days for a city (symbolic)
    def day(city):
        return If(city == 0, days_req[0],
               If(city == 1, days_req[1],
               If(city == 2, days_req[2],
               If(city == 3, days_req[3],
               If(city == 4, days_req[4], days_req[5]))))

    # Start day for the first city
    solver.add(s[0] == 1)

    # For the next cities
    for i in range(1, 6):
        solver.add(s[i] == s[i-1] + (day(seq[i-1]) - 1))

    # Porto constraint: find the position where seq[i] == 3 (Porto) and then require s[i] >= 14, s[i] <= 16
    porto_constraint = []
    for i in range(6):
        porto_constraint.append(And(seq[i] == 3, s[i] >= 14, s[i] <= 16))
    solver.add(Or(porto_constraint))

    # Check and get model
    if solver.check() == sat:
        model = solver.model()
        # Get the sequence and start days
        seq_val = [model.evaluate(seq[i]).as_long() for i in range(6)]
        s_val = [model.evaluate(s[i]).as_long() for i in range(6)]
        
        # Compute end days: e[i] = s_val[i] + (days_req[seq_val[i]] - 1)
        e_val = []
        for i in range(6):
            city_index = seq_val[i]
            end = s_val[i] + days_req[city_index] - 1
            e_val.append(end)
        
        # Build the itinerary list
        itinerary_list = []
        for i in range(6):
            city_index = seq_val[i]
            city_name = cities[city_index]
            if s_val[i] == e_val[i]:
                day_range_str = f"Day {s_val[i]}"
            else:
                day_range_str = f"Day {s_val[i]}-{e_val[i]}"
            itinerary_list.append({"day_range": day_range_str, "place": city_name})
            
            if i < 5:
                # Departure from current city on the last day of stay
                itinerary_list.append({"day_range": f"Day {e_val[i]}", "place": city_name})
                # Arrival to next city on the same day
                next_city_index = seq_val[i+1]
                next_city_name = cities[next_city_index]
                itinerary_list.append({"day_range": f"Day {e_val[i]}", "place": next_city_name})
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()