from z3 import *
import json

def main():
    # City indices and names
    city_names = {
        0: 'Copenhagen',
        1: 'Geneva',
        2: 'Naples',
        3: 'Prague',
        4: 'Dubrovnik',
        5: 'Athens',
        6: 'Santorini',
        7: 'Brussels',
        8: 'Munich'
    }
    city_indices = {v: k for k, v in city_names.items()}
    days_arr = [5, 3, 4, 2, 3, 4, 5, 4, 5]  # Corresponding to city indices 0-8

    # Build flight connections
    flight_connections_str = (
        "Copenhagen and Dubrovnik, Brussels and Copenhagen, Prague and Geneva, Athens and Geneva, "
        "Naples and Dubrovnik, Athens and Dubrovnik, Geneva and Mykonos, Naples and Mykonos, "
        "Naples and Copenhagen, Munich and Mykonos, Naples and Athens, Prague and Athens, "
        "Santorini and Geneva, Athens and Santorini, Naples and Munich, Prague and Copenhagen, "
        "Brussels and Naples, Athens and Mykonos, Athens and Copenhagen, Naples and Geneva, "
        "Dubrovnik and Munich, Brussels and Munich, Prague and Brussels, Brussels and Athens, "
        "Athens and Munich, Geneva and Munich, Copenhagen and Munich, Brussels and Geneva, "
        "Copenhagen and Geneva, Prague and Munich, Copenhagen and Santorini, Naples and Santorini, "
        "Geneva and Dubrovnik"
    )
    flight_pairs = [pair.strip() for pair in flight_connections_str.split(',')]
    flight_list = []
    for pair in flight_pairs:
        parts = pair.split(' and ')
        if len(parts) == 2:
            A = parts[0].strip()
            B = parts[1].strip()
            flight_list.append((A, B))

    # Initialize flight_matrix and flight_to_mykonos
    n_cities = 9
    flight_matrix = [[False]*n_cities for _ in range(n_cities)]
    flight_to_mykonos = [False]*n_cities

    for (A, B) in flight_list:
        if A == 'Mykonos' or B == 'Mykonos':
            if A == 'Mykonos':
                city = B
            else:
                city = A
            if city in city_indices:
                idx = city_indices[city]
                flight_to_mykonos[idx] = True
        else:
            if A in city_indices and B in city_indices:
                i = city_indices[A]
                j = city_indices[B]
                flight_matrix[i][j] = True
                flight_matrix[j][i] = True

    # Z3 solver setup
    s = Solver()
    order = [Int(f'order_{i}') for i in range(9)]
    
    # Constraints: each order[i] is between 0 and 8
    for i in range(9):
        s.add(order[i] >= 0, order[i] < 9)
    s.add(Distinct(order))
    
    # Start days calculation
    start_days = [Int(f'start_{i}') for i in range(9)]
    s.add(start_days[0] == 1)
    for i in range(8):
        s.add(start_days[i+1] == start_days[i] + (days_arr[order[i]] - 1))
    
    # Constraints for specific cities
    for i in range(9):
        # Copenhagen (index0): start day between 7 and 15
        s.add(If(order[i] == 0, And(start_days[i] >= 7, start_days[i] <= 15), True))
        # Naples (index2): start day between 2 and 8
        s.add(If(order[i] == 2, And(start_days[i] >= 2, start_days[i] <= 8), True))
        # Athens (index5): start day between 5 and 11
        s.add(If(order[i] == 5, And(start_days[i] >= 5, start_days[i] <= 11), True))
    
    # Flight constraints between consecutive cities
    for i in range(8):
        constraints = []
        for idx_i in range(n_cities):
            for idx_j in range(n_cities):
                if flight_matrix[idx_i][idx_j]:
                    constraints.append(And(order[i] == idx_i, order[i+1] == idx_j))
        s.add(Or(constraints))
    
    # Flight constraint from last city to Mykonos
    constraints_last = []
    for idx in range(n_cities):
        if flight_to_mykonos[idx]:
            constraints_last.append(order[8] == idx)
    s.add(Or(constraints_last))

    # Check and get model
    if s.check() == sat:
        model = s.model()
        order_val = [model.evaluate(order[i]).as_long() for i in range(9)]
        start_days_val = [1]
        for i in range(8):
            prev_start = start_days_val[-1]
            city_idx = order_val[i]
            dur = days_arr[city_idx]
            next_start = prev_start + (dur - 1)
            start_days_val.append(next_start)
        
        # Build itinerary
        itinerary = []
        for d in range(1, 29):
            if d >= 27:
                place = 'Mykonos'
            else:
                i = 0
                while i < 8 and d >= start_days_val[i+1]:
                    i += 1
                city_idx = order_val[i]
                place = city_names[city_idx]
            itinerary.append({"day": d, "place": place})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()