from z3 import *

def main():
    # Define city names and their required stay days
    city_names = ["Mykonos", "Prague", "Nice", "Valencia", "Riga", "Zurich", "Bucharest"]
    req_days = [3, 3, 2, 5, 5, 5, 5]
    
    # Direct flights as a list of strings
    edges_list = [
        "Mykonos and Nice",
        "Mykonos and Zurich",
        "Prague and Bucharest",
        "Valencia and Bucharest",
        "Zurich and Prague",
        "Riga and Nice",
        "Zurich and Riga",
        "Zurich and Bucharest",
        "Zurich and Valencia",
        "Bucharest and Riga",
        "Prague and Riga",
        "Prague and Valencia",
        "Zurich and Nice"
    ]
    
    # Build allowed flight pairs
    allowed_pairs = set()
    for edge_str in edges_list:
        parts = edge_str.split(" and ")
        a, b = parts
        allowed_pairs.add((a, b))
        allowed_pairs.add((b, a))
    
    # Create Z3 solver and variables for city order
    s = Solver()
    n = 7
    order = [Int(f'order_{i}') for i in range(n)]
    
    # Each order variable must be between 0 and 6 and all distinct
    s.add([And(order[i] >= 0, order[i] < n) for i in range(n)])
    s.add(Distinct(order))
    
    # Create start day variables for each city in the sequence
    start = [Int(f'start_{i}') for i in range(n)]
    
    # First city starts on day 1
    s.add(start[0] == 1)
    
    # Travel days are full days between city stays
    for i in range(1, n):
        # Start day of current city = 
        #   start of previous city + stay days of previous city + 1 travel day
        s.add(start[i] == start[i-1] + req_days[order[i-1]] + 1)
    
    # End day for each city
    end = [Int(f'end_{i}') for i in range(n)]
    for i in range(n):
        s.add(end[i] == start[i] + req_days[order[i]] - 1)
    
    # Entire trip must fit within 22 days
    s.add(end[n-1] <= 22)
    
    # Event constraints:
    # Mykonos must be visited during days 1-3
    # Prague must be visited during days 5-9
    for i in range(n):
        city_idx = order[i]
        # Mykonos constraint (starts by day 3)
        s.add(If(city_idx == 0, And(start[i] >= 1, start[i] <= 3), True))
        # Prague constraint (starts between days 5-9)
        s.add(If(city_idx == 1, And(start[i] >= 5, start[i] <= 9), True))
    
    # Flight constraints between consecutive cities
    for i in range(n-1):
        city1 = order[i]
        city2 = order[i+1]
        name1 = city_names[city1]
        name2 = city_names[city2]
        # Check if flight exists between these cities
        s.add(Or([And(city1 == j, city2 == k) for j in range(n) for k in range(n) 
                if (city_names[j], city_names[k]) in allowed_pairs]))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        order_vals = [m.evaluate(order[i]).as_long() for i in range(n)]
        start_vals = [m.evaluate(start[i]).as_long() for i in range(n)]
        end_vals = [m.evaluate(end[i]).as_long() for i in range(n)]
        
        # Build itinerary with day ranges
        itinerary = []
        for i in range(n):
            city_idx = order_vals[i]
            city_name = city_names[city_idx]
            s_day = start_vals[i]
            e_day = end_vals[i]
            day_range = f"Day {s_day}-{e_day}" if s_day != e_day else f"Day {s_day}"
            itinerary.append({"day_range": day_range, "place": city_name})
        
        result = {"itinerary": itinerary}
        print("Plan found:", result)
    else:
        print("No valid plan found")

if __name__ == "__main__":
    main()