from z3 import *
import json

def main():
    # Define city names and their indices
    city_names = ['Vienna', 'Lyon', 'Edinburgh', 'Reykjavik', 'Stuttgart', 'Manchester', 'Split', 'Prague']
    city_index = {name: idx for idx, name in enumerate(city_names)}
    
    # Total days required for each city by index
    total_days_list = [4, 3, 4, 5, 5, 2, 5, 4]  # [Vienna, Lyon, Edinburgh, ...]
    
    # Define allowed flight connections (undirected edges as tuples (a, b) with a < b)
    allowed_edges = [
        (0, 1), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7),
        (1, 6), (1, 7),
        (2, 4), (2, 7),
        (3, 4), (3, 7),
        (4, 5), (4, 6),
        (5, 6), (5, 7),
        (6, 7)
    ]
    
    # Create Z3 variables
    n = 8  # number of cities
    c = [Int(f'c_{i}') for i in range(n)]  # city at position i
    arrival = [Int(f'arrival_{i}') for i in range(n)]
    departure = [Int(f'departure_{i}') for i in range(n)]
    
    # Initialize solver
    s = Solver()
    
    # Each city index must be between 0 and 7
    for i in range(n):
        s.add(c[i] >= 0, c[i] < n)
    
    # All cities are distinct in the sequence
    s.add(Distinct(c))
    
    # Timeline constraints
    s.add(arrival[0] == 1)  # start on day 1
    s.add(departure[n-1] == 25)  # end on day 25
    for i in range(n-1):
        s.add(departure[i] == arrival[i+1])
    
    # Stay duration constraints for each city
    for i in range(n):
        total_days = If(
            c[i] == 0, total_days_list[0],
            If(c[i] == 1, total_days_list[1],
            If(c[i] == 2, total_days_list[2],
            If(c[i] == 3, total_days_list[3],
            If(c[i] == 4, total_days_list[4],
            If(c[i] == 5, total_days_list[5],
            If(c[i] == 6, total_days_list[6],
            total_days_list[7])))))))
        s.add(departure[i] - arrival[i] + 1 == total_days)
    
    # Fixed constraints for Edinburgh (index 2) and Split (index 6)
    for i in range(n):
        # If city at position i is Edinburgh, set arrival to 5 and departure to 8
        s.add(If(c[i] == 2, And(arrival[i] == 5, departure[i] == 8), True))
        # If city at position i is Split, set arrival to 19 and departure to 23
        s.add(If(c[i] == 6, And(arrival[i] == 19, departure[i] == 23), True))
    
    # Flight constraints: consecutive cities must have a direct flight
    for i in range(n-1):
        or_conditions = []
        for edge in allowed_edges:
            a, b = edge
            # Both (a, b) and (b, a) are allowed
            or_conditions.append(And(c[i] == a, c[i+1] == b))
            or_conditions.append(And(c[i] == b, c[i+1] == a))
        s.add(Or(or_conditions))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        # Build the itinerary
        itinerary_list = []
        for day in range(1, 26):  # days 1 to 25
            for pos_idx in range(n):
                arr_val = m[arrival[pos_idx]].as_long()
                dep_val = m[departure[pos_idx]].as_long()
                if arr_val <= day <= dep_val:
                    city_idx = m[c[pos_idx]].as_long()
                    city_name = city_names[city_idx]
                    itinerary_list.append({"day": day, "city": city_name})
        
        # Output the itinerary as JSON
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()