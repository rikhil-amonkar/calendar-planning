from z3 import *

def main():
    # Define the city to integer mapping
    city_to_int = {
        "Berlin": 0,
        "Lyon": 1,
        "Paris": 2,
        "Riga": 3,
        "Stockholm": 4,
        "Zurich": 5,
        "Nice": 6,
        "Seville": 7,
        "Milan": 8,
        "Naples": 9
    }
    int_to_city = {v: k for k, v in city_to_int.items()}
    
    # Duration offsets (duration - 1) for each city (by integer)
    d_offset_map = {
        0: 1,  # Berlin: 2 days -> 2-1=1
        1: 2,  # Lyon: 3-1=2
        2: 4,  # Paris: 5-1=4
        3: 1,  # Riga: 2-1=1
        4: 2,  # Stockholm: 3-1=2
        5: 4,  # Zurich: 5-1=4
        6: 1,  # Nice: 2-1=1
        7: 2,  # Seville: 3-1=2
        8: 2,  # Milan: 3-1=2
        9: 3   # Naples: 4-1=3
    }
    
    # List of direct flights
    flights = [
        ("Paris", "Stockholm"), ("Seville", "Paris"), ("Naples", "Zurich"),
        ("Nice", "Riga"), ("Berlin", "Milan"), ("Paris", "Zurich"),
        ("Paris", "Nice"), ("Milan", "Paris"), ("Milan", "Riga"),
        ("Paris", "Lyon"), ("Milan", "Naples"), ("Paris", "Riga"),
        ("Berlin", "Stockholm"), ("Stockholm", "Riga"), ("Nice", "Zurich"),
        ("Milan", "Zurich"), ("Lyon", "Nice"), ("Zurich", "Stockholm"),
        ("Zurich", "Riga"), ("Berlin", "Naples"), ("Milan", "Stockholm"),
        ("Berlin", "Zurich"), ("Milan", "Seville"), ("Paris", "Naples"),
        ("Berlin", "Riga"), ("Nice", "Stockholm"), ("Berlin", "Paris"),
        ("Nice", "Naples"), ("Berlin", "Nice")
    ]
    
    # Build neighbor dictionary
    neighbors_dict = {i: [] for i in range(10)}
    for a_str, b_str in flights:
        a_int = city_to_int[a_str]
        b_int = city_to_int[b_str]
        neighbors_dict[a_int].append(b_int)
        neighbors_dict[b_int].append(a_int)
    
    # Create Z3 solver and variables
    s = Solver()
    
    # Order of cities after Berlin: 9 integers, each in [1,9] and distinct
    order = [Int(f"order_{i}") for i in range(9)]
    for i in range(9):
        s.add(order[i] >= 1, order[i] <= 9)
    s.add(Distinct(order))
    
    # Cumulative sums for the non-Berlin cities
    cum = [0] * 10
    cum[0] = 0  # Before any non-Berlin city
    for i in range(1, 10):
        # The city at timeline position i (which is the (i-1)-th in the order list) has offset = d_offset_map[city_int]
        # But note: d_offset_map for non-Berlin cities uses the global integer (1..9)
        cum[i] = cum[i-1] + d_offset_map[order[i-1]]
    
    # Constraints for Nice (6) and Stockholm (4)
    nice_cons = []
    stockholm_cons = []
    for i in range(1, 10):
        # If the city at position i (order[i-1]) is Nice (6), then cum[i-1] must be 10
        nice_cons.append(Implies(order[i-1] == 6, cum[i-1] == 10))
        # If the city at position i is Stockholm (4), then cum[i-1] must be 18
        stockholm_cons.append(Implies(order[i-1] == 4, cum[i-1] == 18))
    s.add(And(nice_cons))
    s.add(And(stockholm_cons))
    
    # Ensure Nice and Stockholm are in the order
    s.add(Or([order[i] == 6 for i in range(9)]))
    s.add(Or([order[i] == 4 for i in range(9)]))
    
    # Flight constraint helper function
    def flight_ok(a, b, neighbors_dict):
        constraints = []
        for city in range(10):
            constraints.append(Implies(a == city, Or([b == nb for nb in neighbors_dict[city]])))
        return And(constraints)
    
    # Flight constraints:
    # Between Berlin (0) and the first city in the order
    s.add(flight_ok(0, order[0], neighbors_dict))
    # Between consecutive cities in the order
    for i in range(8):
        s.add(flight_ok(order[i], order[i+1], neighbors_dict))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        order_vals = [m[order[i]].as_long() for i in range(9)]
        
        # Compute start days for each city in the timeline
        s_timeline = [1]  # Berlin starts at day 1
        # After Berlin: duration offset is 1, so next city starts at 1+1=2
        s_timeline.append(s_timeline[0] + 1)
        # For the remaining 8 cities
        for i in range(8):
            city_int = order_vals[i]
            d_offset = d_offset_map[city_int]
            next_start = s_timeline[-1] + d_offset
            s_timeline.append(next_start)
        
        # Build itinerary
        itinerary = []
        for i in range(10):
            if i == 0:
                city_name = "Berlin"
                d_offset = 1
                start = s_timeline[i]
                end = start + d_offset
            else:
                city_int = order_vals[i-1]
                city_name = int_to_city[city_int]
                d_offset = d_offset_map[city_int]
                start = s_timeline[i]
                end = start + d_offset
            
            itinerary.append({"day_range": f"Day {start}-{end}", "place": city_name})
            
            if i < 9:
                itinerary.append({"day_range": f"Day {end}", "place": city_name})
                next_city_int = order_vals[i]  # Next city is at position i in order_vals
                next_city_name = int_to_city[next_city_int]
                itinerary.append({"day_range": f"Day {end}", "place": next_city_name})
        
        # Output the itinerary
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()