from z3 import *

def main():
    n_days = 19
    cities = ["Bucharest", "Warsaw", "Stuttgart", "Copenhagen", "Dubrovnik"]
    n_cities = len(cities)
    
    base_city = [Int('base_%d' % d) for d in range(n_days)]
    flight_taken = [Bool('flight_%d' % d) for d in range(n_days)]
    to_city = [Int('to_%d' % d) for d in range(n_days)]
    
    s = Solver()
    
    edges = [
        (0, 1), (0, 3),  # Bucharest - Warsaw, Bucharest - Copenhagen
        (1, 0), (1, 2), (1, 3),  # Warsaw - Bucharest, Warsaw - Stuttgart, Warsaw - Copenhagen
        (2, 1), (2, 3),  # Stuttgart - Warsaw, Stuttgart - Copenhagen
        (3, 0), (3, 1), (3, 2), (3, 4),  # Copenhagen - Bucharest, Warsaw, Stuttgart, Dubrovnik
        (4, 3)   # Dubrovnik - Copenhagen
    ]
    
    for d in range(n_days):
        s.add(base_city[d] >= 0, base_city[d] < n_cities)
        s.add(to_city[d] >= 0, to_city[d] < n_cities)
    
    for d in range(n_days - 1):
        s.add(base_city[d+1] == If(flight_taken[d], to_city[d], base_city[d]))
    
    for d in range(n_days):
        s.add(Implies(flight_taken[d], base_city[d] != to_city[d]))
        valid_flight = Or([And(base_city[d] == a, to_city[d] == b) for (a, b) in edges])
        s.add(Implies(flight_taken[d], valid_flight))
    
    total_flights = Sum([If(ft, 1, 0) for ft in flight_taken])
    s.add(total_flights == 4)
    
    in_city = [[Bool('in_%d_%s' % (d, cities[c])) for c in range(n_cities)] for d in range(n_days)]
    for d in range(n_days):
        for c in range(n_cities):
            s.add(in_city[d][c] == Or(base_city[d] == c, And(flight_taken[d], to_city[d] == c)))
    
    total_days = [Int('total_%s' % cities[c]) for c in range(n_cities)]
    for c in range(n_cities):
        s.add(total_days[c] == Sum([If(in_city[d][c], 1, 0) for d in range(n_days)]))
    
    s.add(total_days[0] == 6)  # Bucharest
    s.add(total_days[1] == 2)  # Warsaw
    s.add(total_days[2] == 7)  # Stuttgart
    s.add(total_days[3] == 3)  # Copenhagen
    s.add(total_days[4] == 5)  # Dubrovnik
    
    s.add(base_city[0] == 0)  # Start in Bucharest
    
    s.add(base_city[6] == 2)  # In Stuttgart on day 7 (index 6)
    s.add(Not(flight_taken[6]))  # No flight on day 7
    s.add(base_city[12] == 2)  # In Stuttgart on day 13 (index 12)
    s.add(Not(flight_taken[12]))  # No flight on day 13
    
    # Wedding in Bucharest between day 1 and 6 (indices 0 to 5)
    s.add(Or([in_city[d][0] for d in range(6)]))
    
    if s.check() == sat:
        m = s.model()
        schedule = []
        for d in range(n_days):
            base_val = m.evaluate(base_city[d]).as_long()
            ft_val = is_true(m.evaluate(flight_taken[d]))
            to_val = m.evaluate(to_city[d]).as_long() if ft_val else None
            day_cities = [cities[base_val]]
            if ft_val:
                day_cities.append(cities[to_val])
            schedule.append((d+1, day_cities))
        
        for day, cities_list in schedule:
            print(f"Day {day}: {', '.join(cities_list)}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()