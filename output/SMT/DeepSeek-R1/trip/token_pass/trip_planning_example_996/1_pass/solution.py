from z3 import *
import json

def main():
    # City indices
    cities = ['Mykonos', 'Nice', 'Prague', 'Bucharest', 'Valencia', 'Zurich', 'Riga']
    n = len(cities)
    
    # Fixed days per city
    days = [3, 2, 3, 5, 5, 5, 5]
    
    # Direct flights as frozenset pairs
    allowed_edges = set([
        frozenset([0, 1]),  # Mykonos-Nice
        frozenset([0, 5]),  # Mykonos-Zurich
        frozenset([2, 3]),  # Prague-Bucharest
        frozenset([3, 4]),  # Valencia-Bucharest
        frozenset([2, 5]),  # Prague-Zurich
        frozenset([1, 6]),  # Riga-Nice
        frozenset([5, 6]),  # Zurich-Riga
        frozenset([3, 5]),  # Zurich-Bucharest
        frozenset([4, 5]),  # Zurich-Valencia
        frozenset([3, 6]),  # Bucharest-Riga
        frozenset([2, 6]),  # Prague-Riga
        frozenset([2, 4]),  # Prague-Valencia
        frozenset([1, 5])   # Zurich-Nice
    ])
    
    s = Solver()
    
    # Order of cities as a permutation
    order = [Int('order_%d' % i) for i in range(n)]
    for i in range(n):
        s.add(And(order[i] >= 0, order[i] < n))
    s.add(Distinct(order))
    
    # Start days for each city in the itinerary
    start = [Int('start_%d' % i) for i in range(n)]
    s.add(start[0] == 1)
    
    # Define start days based on previous city's duration
    for i in range(1, n):
        prev_city_days = days[order[i-1]]
        s.add(start[i] == start[i-1] + prev_city_days - 1)
    
    # Total trip must end on day 22
    s.add(start[n-1] + days[order[n-1]] - 1 == 22)
    
    # Event constraints: Mykonos must include a day between 1-3, Prague between 7-9
    for j in range(n):
        # Mykonos (index 0) must start no later than day 3
        s.add(If(order[j] == 0, start[j] <= 3, True))
        # Prague (index 2) must start between day 5 and 9 inclusive
        s.add(If(order[j] == 2, And(start[j] >= 5, start[j] <= 9), True))
    
    # Flight constraints between consecutive cities
    for i in range(n-1):
        city_i = order[i]
        city_j = order[i+1]
        edge_conditions = []
        for edge in allowed_edges:
            a, b = list(edge)
            edge_conditions.append(And(city_i == a, city_j == b))
            edge_conditions.append(And(city_i == b, city_j == a))
        s.add(Or(edge_conditions))
    
    if s.check() == sat:
        m = s.model()
        order_val = [m.evaluate(order[i]).as_long() for i in range(n)]
        start_val = [m.evaluate(start[i]).as_long() for i in range(n)]
        
        itinerary = []
        for i in range(n):
            city_idx = order_val[i]
            city_name = cities[city_idx]
            start_day = start_val[i]
            end_day = start_val[i] + days[city_idx] - 1
            day_range = f"Day {start_day}-{end_day}"
            itinerary.append({"day_range": day_range, "place": city_name})
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()