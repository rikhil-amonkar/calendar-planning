from z3 import *

def main():
    # Define cities and their stay durations
    cities = ["Copenhagen", "Geneva", "Mykonos", "Naples", "Prague", "Dubrovnik", "Athens", "Santorini", "Brussels", "Munich"]
    days_list = [5, 3, 2, 4, 2, 3, 4, 5, 4, 5]
    
    # Flight connections as undirected edges
    flight_pairs = [
        "Copenhagen and Dubrovnik", "Brussels and Copenhagen", "Prague and Geneva", "Athens and Geneva",
        "Naples and Dubrovnik", "Athens and Dubrovnik", "Geneva and Mykonos", "Naples and Mykonos",
        "Naples and Copenhagen", "Munich and Mykonos", "Naples and Athens", "Prague and Athens",
        "Santorini and Geneva", "Athens and Santorini", "Naples and Munich", "Prague and Copenhagen",
        "Brussels and Naples", "Athens and Mykonos", "Athens and Copenhagen", "Naples and Geneva",
        "Dubrovnik and Munich", "Brussels and Munich", "Prague and Brussels", "Brussels and Athens",
        "Athens and Munich", "Geneva and Munich", "Copenhagen and Munich", "Brussels and Geneva",
        "Copenhagen and Geneva", "Prague and Munich", "Copenhagen and Santorini", "Naples and Santorini",
        "Geneva and Dubrovnik"
    ]
    edges_set = set()
    for pair in flight_pairs:
        a, b = pair.split(" and ")
        idx_a = cities.index(a)
        idx_b = cities.index(b)
        edges_set.add((min(idx_a, idx_b), max(idx_a, idx_b)))
    
    # Allowed flight pairs (both directions)
    allowed_flights = []
    for a in range(10):
        for b in range(10):
            if a == b:
                continue
            if (min(a, b), max(a, b)) in edges_set:
                allowed_flights.append((a, b))
    
    # Fix Mykonos as the last city
    mykonos_index = 2
    other_indices = [i for i in range(10) if i != mykonos_index]
    
    # Initialize Z3 solver
    s = Solver()
    
    # Order variables for the first 9 positions
    order_vars = [Int('o%d' % i) for i in range(9)]
    order_full = order_vars + [mykonos_index]
    
    # Constraints: first 9 positions are distinct and from other_indices
    for i in range(9):
        s.add(Or([order_vars[i] == idx for idx in other_indices]))
    s.add(Distinct(order_vars))
    
    # Compute start and end days for each position
    start_i = [None] * 10
    end_i = [None] * 10
    for i in range(10):
        # Days for the city at position i
        days_i = Sum([days_list[d] * If(order_full[i] == d, 1, 0) for d in range(10)])
        if i == 0:
            start_i[i] = 1
            end_i[i] = start_i[i] + days_i - 1
        else:
            # Sum of days for cities in positions 0 to i-1
            partial_sum_i = Sum([days_list[d] * If(order_full[j] == d, 1, 0) for j in range(i) for d in range(10)])
            start_i[i] = 1 + partial_sum_i - i
            end_i[i] = start_i[i] + days_i - 1
        # Ensure days are within bounds
        s.add(start_i[i] >= 1)
        s.add(end_i[i] <= 28)
    
    # City-specific constraints
    # Copenhagen (index 0) must have a day between 11 and 15
    start_cph = Sum([If(order_full[i] == 0, start_i[i], 0) for i in range(10)])
    end_cph = Sum([If(order_full[i] == 0, end_i[i], 0) for i in range(10)])
    s.add(start_cph <= 15)
    s.add(end_cph >= 11)
    
    # Naples (index 3) must have a day between 5 and 8
    start_nap = Sum([If(order_full[i] == 3, start_i[i], 0) for i in range(10)])
    end_nap = Sum([If(order_full[i] == 3, end_i[i], 0) for i in range(10)])
    s.add(start_nap <= 8)
    s.add(end_nap >= 5)
    
    # Athens (index 6) must have a day between 8 and 11
    start_ath = Sum([If(order_full[i] == 6, start_i[i], 0) for i in range(10)])
    end_ath = Sum([If(order_full[i] == 6, end_i[i], 0) for i in range(10)])
    s.add(start_ath <= 11)
    s.add(end_ath >= 8)
    
    # Flight constraints between consecutive cities
    for i in range(9):
        a = order_full[i]
        b = order_full[i+1]
        s.add(Or([And(a == a0, b == b0) for (a0, b0) in allowed_flights]))
    
    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        order_solution = [m.evaluate(order_full[i]).as_long() for i in range(10)]
        
        # Compute start and end days for the itinerary
        starts = [0] * 10
        ends = [0] * 10
        current_start = 1
        for i in range(10):
            c = order_solution[i]
            length = days_list[c]
            starts[i] = current_start
            ends[i] = current_start + length - 1
            current_start = ends[i]
        
        # Build itinerary
        itinerary = []
        for i in range(10):
            c = order_solution[i]
            s_day = starts[i]
            e_day = ends[i]
            itinerary.append({
                "day_range": "Day {}-{}".format(s_day, e_day),
                "place": cities[c]
            })
            if i < 9:
                itinerary.append({
                    "day_range": "Day {}".format(e_day),
                    "place": cities[c]
                })
                next_city = cities[order_solution[i+1]]
                itinerary.append({
                    "day_range": "Day {}".format(e_day),
                    "place": next_city
                })
        
        # Output the itinerary
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()