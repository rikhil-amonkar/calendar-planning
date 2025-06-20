from z3 import *
import json

def main():
    # Define city names and their indices
    city_names = ['Geneva', 'Istanbul', 'Venice', 'Vilnius', 'Vienna', 'Riga', 'Brussels', 'Madrid', 'Munich', 'Reykjavik']
    name_to_index = {name: idx for idx, name in enumerate(city_names)}
    index_to_name = {idx: name for name, idx in name_to_index.items()}
    
    # Required days for each city (index 0 to 9)
    req_days_arr = [4, 4, 5, 4, 4, 2, 2, 4, 5, 2]
    # For the middle cities, term = req_days - 1
    term_dict = {
        1: 3,   # Istanbul
        2: 4,   # Venice
        3: 3,   # Vilnius
        4: 3,   # Vienna
        5: 1,   # Riga
        7: 3,   # Madrid
        8: 4,   # Munich
        9: 1    # Reykjavik
    }
    
    # Build the flight graph
    flight_strs = [
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
        "from Riga to Vilnius", 
        "from Vilnius to Munich", 
        "Madrid and Vienna", 
        "Vienna and Riga", 
        "Geneva and Vienna", 
        "Geneva and Brussels", 
        "Geneva and Madrid", 
        "Munich and Brussels", 
        "Madrid and Brussels", 
        "Vienna and Brussels", 
        "Geneva and Munich", 
        "Madrid and Istanbul"
    ]
    
    allowed_edges = set()
    for s in flight_strs:
        if s.startswith('from'):
            parts = s.split()
            city1 = parts[1]
            city2 = parts[3]
        else:
            parts = s.split(' and ')
            city1 = parts[0]
            city2 = parts[1]
        idx1 = name_to_index[city1]
        idx2 = name_to_index[city2]
        if idx1 > idx2:
            idx1, idx2 = idx2, idx1
        allowed_edges.add((idx1, idx2))
    
    # Middle cities: indices 1,2,3,4,5,7,8,9 (excluding Geneva(0) and Brussels(6))
    middle_cities = [1,2,3,4,5,7,8,9]
    
    # Z3 setup
    s = Solver()
    n = 8
    order = [Int(f'c_{i}') for i in range(n)]
    
    # Each element in order must be one of the middle cities
    for i in range(n):
        s.add(Or([order[i] == c for c in middle_cities]))
    s.add(Distinct(order))
    
    # Function to check if two cities are connected
    def connected(a, b):
        constraints = []
        for edge in allowed_edges:
            constraints.append(Or(
                And(a == edge[0], b == edge[1]),
                And(a == edge[1], b == edge[0])
            ))
        return Or(constraints)
    
    # Flight connection constraints
    s.add(connected(0, order[0]))  # From Geneva to first city
    for i in range(n-1):
        s.add(connected(order[i], order[i+1]))  # Between middle cities
    s.add(connected(order[n-1], 6))  # From last city to Brussels
    
    # Cumulative constraints for events
    cum = [Int(f'cum_{i}') for i in range(n+1)]
    s.add(cum[0] == 0)
    for i in range(n):
        term_i = If(order[i] == 1, 3,
                   If(order[i] == 2, 4,
                   If(order[i] == 3, 3,
                   If(order[i] == 4, 3,
                   If(order[i] == 5, 1,
                   If(order[i] == 7, 3,
                   If(order[i] == 8, 4,
                   If(order[i] == 9, 1, 0))))))))
        s.add(cum[i+1] == cum[i] + term_i)
    
    # Event constraints
    for i in range(n):
        # Venice (index2) must be visited by day 11 (cumulative <= 7 at arrival)
        s.add(If(order[i] == 2, cum[i] <= 7, True))
        # Vilnius (index3) must be visited between days 20-23 (cumulative between 13 and 19 at arrival)
        s.add(If(order[i] == 3, And(cum[i] <= 19, cum[i+1] >= 16), True))
    
    # Solve
    if s.check() == sat:
        model = s.model()
        order_val = [model.evaluate(order[i]).as_long() for i in range(n)]
        full_sequence = [0] + order_val + [6]
        
        # Compute arrival and departure days
        a = [0] * 10
        d = [0] * 10
        a[0] = 1
        d[0] = a[0] + req_days_arr[full_sequence[0]] - 1
        for i in range(1, 10):
            a[i] = d[i-1]
            d[i] = a[i] + req_days_arr[full_sequence[i]] - 1
        
        # Build itinerary
        itinerary = []
        for i in range(10):
            city_idx = full_sequence[i]
            city_name = index_to_name[city_idx]
            # Entire stay record
            if a[i] == d[i]:
                day_range_str = f"Day {a[i]}"
            else:
                day_range_str = f"Day {a[i]}-{d[i]}"
            itinerary.append({"day_range": day_range_str, "place": city_name})
            # If not last city, add departure and arrival records
            if i < 9:
                # Departure from current city
                itinerary.append({"day_range": f"Day {d[i]}", "place": city_name})
                # Arrival at next city
                next_city_idx = full_sequence[i+1]
                next_city_name = index_to_name[next_city_idx]
                itinerary.append({"day_range": f"Day {d[i]}", "place": next_city_name})
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()