from z3 import *

def main():
    # City indices
    dublin = 0
    madrid = 1
    oslo = 2
    london = 3
    vilnius = 4
    berlin = 5

    cities = ["Dublin", "Madrid", "Oslo", "London", "Vilnius", "Berlin"]
    dur = [3, 2, 3, 2, 3, 5]

    # List of undirected edges
    undir_edges = [
        (london, madrid),
        (oslo, vilnius),
        (berlin, vilnius),
        (madrid, oslo),
        (madrid, dublin),
        (london, oslo),
        (madrid, berlin),
        (berlin, oslo),
        (dublin, oslo),
        (london, dublin),
        (london, berlin),
        (berlin, dublin)
    ]
    
    # Create directed edges (both directions)
    edges = []
    for u, v in undir_edges:
        edges.append((u, v))
        edges.append((v, u))
    
    s = Solver()
    
    # Order of cities (permutation)
    order = [Int(f'order_{i}') for i in range(6)]
    for i in range(6):
        s.add(order[i] >= 0, order[i] < 6)
    s.add(Distinct(order))
    
    # Flight connections: consecutive cities must have a direct flight
    for i in range(5):
        s.add(Or([And(order[i] == a, order[i+1] == b) for (a, b) in edges]))
    
    # Start days for each city
    start = [Int(f'start_{i}') for i in range(6)]
    
    # First city starts at day 1
    s.add(start[order[0]] == 1)
    
    # Subsequent cities start at the end day of the previous city
    for i in range(1, 6):
        prev_city = order[i-1]
        s.add(start[order[i]] == start[prev_city] + dur[prev_city] - 1)
    
    # Event constraints
    s.add(start[dublin] >= 5, start[dublin] <= 9)  # Dublin between day 7-9
    s.add(start[madrid] == 2)  # Madrid starts on day 2
    s.add(start[berlin] <= 7)  # Berlin starts by day 7
    
    if s.check() == sat:
        m = s.model()
        order_vals = [m.evaluate(order[i]).as_long() for i in range(6)]
        start_vals = [m.evaluate(start[i]).as_long() for i in range(6)]
        
        itinerary = []
        for i in range(6):
            city_idx = order_vals[i]
            s_day = start_vals[city_idx]
            e_day = s_day + dur[city_idx] - 1
            itinerary.append({"day_range": f"Day {s_day}-{e_day}", "place": cities[city_idx]})
            if i < 5:
                itinerary.append({"day_range": f"Day {e_day}", "place": cities[city_idx]})
                next_city_idx = order_vals[i+1]
                itinerary.append({"day_range": f"Day {e_day}", "place": cities[next_city_idx]})
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()