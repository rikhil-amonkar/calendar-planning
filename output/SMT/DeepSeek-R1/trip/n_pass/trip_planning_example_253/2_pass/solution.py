from z3 import *

def main():
    # Cities: Amsterdam=0, Vienna=1, Santorini=2, Lyon=3
    n_days = 14
    n_cities = 4
    city_names = ['Amsterdam', 'Vienna', 'Santorini', 'Lyon']
    
    # x[i] = city at end of day i (start of day i+1)
    x = [Int('x%d' % i) for i in range(n_days + 1)]
    
    s = Solver()
    
    # Initial and final positions can be any city
    for i in range(n_days + 1):
        s.add(x[i] >= 0, x[i] < n_cities)
    
    # Direct flights between cities (bidirectional)
    direct_flights = [
        (1, 3), (3, 1),  # Vienna-Lyon
        (1, 2), (2, 1),  # Vienna-Santorini
        (1, 0), (0, 1),  # Vienna-Amsterdam
        (0, 2), (2, 0),  # Amsterdam-Santorini
        (0, 3), (3, 0)   # Amsterdam-Lyon
    ]
    
    # Flight constraints between consecutive days
    for i in range(n_days):
        current = x[i]
        next_ = x[i+1]
        s.add(Or(
            current == next_,  # Stay in the same city
            Or([And(current == a, next_ == b) for (a, b) in direct_flights])
        ))
    
    # Count days per city
    amsterdam, vienna, santorini, lyon = 0, 1, 2, 3
    days_in_city = [0]*n_cities
    
    for c in range(n_cities):
        total = 0
        for i in range(n_days):
            # Count if city appears at start or end of day
            start_city = If(x[i] == c, 1, 0)
            end_city = If(x[i+1] == c, 1, 0)
            # If it's a travel day involving c, count 1
            # If full day in c, count 1 (not double-counted)
            total += If(Or(x[i] == c, x[i+1] == c), 1, 0)
        days_in_city[c] = total
    
    # Set day requirements
    s.add(days_in_city[amsterdam] == 3)
    s.add(days_in_city[vienna] == 7)
    s.add(days_in_city[santorini] == 4)
    s.add(days_in_city[lyon] == 3)
    
    # Workshop in Amsterdam (days 9-11 inclusive)
    day9 = Or(x[8] == amsterdam, x[9] == amsterdam)  # Day 9: start=x8, end=x9
    day10 = Or(x[9] == amsterdam, x[10] == amsterdam)  # Day 10: start=x9, end=x10
    day11 = Or(x[10] == amsterdam, x[11] == amsterdam)  # Day 11: start=x10, end=x11
    s.add(Or(day9, day10, day11))
    
    # Wedding in Lyon (days 7-9 inclusive)
    day7 = Or(x[6] == lyon, x[7] == lyon)  # Day 7: start=x6, end=x7
    day8 = Or(x[7] == lyon, x[8] == lyon)  # Day 8: start=x7, end=x8
    day9_lyon = Or(x[8] == lyon, x[9] == lyon)  # Day 9: start=x8, end=x9
    s.add(Or(day7, day8, day9_lyon))
    
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