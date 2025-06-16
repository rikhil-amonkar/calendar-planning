from z3 import *

def main():
    # Cities: Amsterdam=0, Vienna=1, Santorini=2, Lyon=3
    n_days = 14
    n_cities = 4
    city_names = ['Amsterdam', 'Vienna', 'Santorini', 'Lyon']
    amsterdam, vienna, santorini, lyon = 0, 1, 2, 3
    
    # x[i] = city at end of day i (start of day i+1)
    x = [Int('x%d' % i) for i in range(n_days + 1)]
    
    s = Solver()
    
    # Initial position: Vienna at the start of day 1 (x0)
    s.add(x[0] == vienna)
    
    # All x[i] must be valid cities
    for i in range(1, n_days + 1):
        s.add(x[i] >= 0, x[i] < n_cities)
    
    # Direct flights (bidirectional)
    direct_flights = [
        (vienna, lyon), (lyon, vienna),
        (vienna, santorini), (santorini, vienna),
        (vienna, amsterdam), (amsterdam, vienna),
        (amsterdam, santorini), (santorini, amsterdam),
        (amsterdam, lyon), (lyon, amsterdam)
    ]
    
    # Flight constraints between consecutive days
    for i in range(n_days):
        current = x[i]
        next_ = x[i+1]
        s.add(Or(
            current == next_,  # Stay in the same city
            Or([And(current == a, next_ == b) for (a, b) in direct_flights])
        ))
    
    # Count days per city (if in city at start or end of the day)
    days_in_city = [0] * n_cities
    for c in range(n_cities):
        total = 0
        for i in range(n_days):
            in_city = Or(x[i] == c, x[i+1] == c)
            total += If(in_city, 1, 0)
        days_in_city[c] = total
    
    s.add(days_in_city[amsterdam] == 3)
    s.add(days_in_city[vienna] == 7)
    s.add(days_in_city[santorini] == 4)
    s.add(days_in_city[lyon] == 3)
    
    # Workshop in Amsterdam (days 9-11 inclusive) - must be a full day
    day9_full = And(x[8] == amsterdam, x[9] == amsterdam)   # Day 9: full day in Amsterdam
    day10_full = And(x[9] == amsterdam, x[10] == amsterdam) # Day 10: full day in Amsterdam
    day11_full = And(x[10] == amsterdam, x[11] == amsterdam) # Day 11: full day in Amsterdam
    s.add(Or(day9_full, day10_full, day11_full))
    
    # Wedding in Lyon (days 7-9 inclusive) - must be a full day
    day7_full = And(x[6] == lyon, x[7] == lyon)   # Day 7: full day in Lyon
    day8_full = And(x[7] == lyon, x[8] == lyon)   # Day 8: full day in Lyon
    day9_full_lyon = And(x[8] == lyon, x[9] == lyon) # Day 9: full day in Lyon
    s.add(Or(day7_full, day8_full, day9_full_lyon))
    
    # Solve and print itinerary
    if s.check() == sat:
        m = s.model()
        sol = [m.evaluate(x[i]).as_long() for i in range(len(x))]
        print("Day-by-day itinerary:")
        for day in range(1, n_days + 1):
            start = sol[day-1]
            end = sol[day]
            if start == end:
                print(f"Day {day}: Stay in {city_names[start]}")
            else:
                print(f"Day {day}: Travel from {city_names[start]} to {city_names[end]} (thus in both cities on day {day})")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()