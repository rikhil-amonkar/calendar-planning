from z3 import *

def main():
    n_days = 19
    cities = ["Bucharest", "Warsaw", "Stuttgart", "Copenhagen", "Dubrovnik"]
    n_cities = len(cities)
    
    base_city = [Int('base_%d' % d) for d in range(n_days)]
    flight_taken = [Bool('flight_%d' % d) for d in range(n_days)]
    to_city = [Int('to_%d' % d) for d in range(n_days)]
    
    s = Solver()
    
    # Define direct flight connections (bidirectional)
    edges = [
        (0, 1), (0, 3),  # Bucharest to Warsaw, Bucharest to Copenhagen
        (1, 0), (1, 2), (1, 3),  # Warsaw to Bucharest, Warsaw to Stuttgart, Warsaw to Copenhagen
        (2, 1), (2, 3),  # Stuttgart to Warsaw, Stuttgart to Copenhagen
        (3, 0), (3, 1), (3, 2), (3, 4),  # Copenhagen to Bucharest, Warsaw, Stuttgart, Dubrovnik
        (4, 3)  # Dubrovnik to Copenhagen
    ]
    
    # City indices must be valid
    for d in range(n_days):
        s.add(base_city[d] >= 0, base_city[d] < n_cities)
        s.add(to_city[d] >= 0, to_city[d] < n_cities)
    
    # Next day's base city is the flight destination if flight taken
    for d in range(n_days - 1):
        s.add(base_city[d+1] == If(flight_taken[d], to_city[d], base_city[d]))
    
    # Flight constraints: no self-flights, only allowed direct flights
    for d in range(n_days):
        s.add(Implies(flight_taken[d], base_city[d] != to_city[d]))
        valid_flight = Or([And(base_city[d] == a, to_city[d] == b) for (a, b) in edges])
        s.add(Implies(flight_taken[d], valid_flight))
    
    # Exactly 4 flight days (since 5+2+7+6+3=23 days, 23-19=4 flight days)
    total_flights = Sum([If(ft, 1, 0) for ft in flight_taken])
    s.add(total_flights == 4)
    
    # Matrix: in_city[day][city] is True if present in that city on that day
    in_city = [[Bool('in_%d_%s' % (d, cities[c])) for c in range(n_cities)] for d in range(n_days)]
    for d in range(n_days):
        for c in range(n_cities):
            s.add(in_city[d][c] == Or(base_city[d] == c, And(flight_taken[d], to_city[d] == c)))
    
    # Total days per city
    total_days = [Int('total_%s' % cities[c]) for c in range(n_cities)]
    for c in range(n_cities):
        s.add(total_days[c] == Sum([If(in_city[d][c], 1, 0) for d in range(n_days)]))
    
    # City day requirements
    s.add(total_days[0] == 6)  # Bucharest
    s.add(total_days[1] == 2)  # Warsaw
    s.add(total_days[2] == 7)  # Stuttgart
    s.add(total_days[3] == 3)  # Copenhagen
    s.add(total_days[4] == 5)  # Dubrovnik
    
    # Conference in Stuttgart on day 7 (index 6) and day 13 (index 12)
    s.add(in_city[6][2] == True)   # Day 7
    s.add(in_city[12][2] == True)  # Day 13
    
    # Wedding in Bucharest between day 1-6 (indices 0-5)
    s.add(Or([in_city[d][0] for d in range(6)]))
    
    # Solve and print schedule
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