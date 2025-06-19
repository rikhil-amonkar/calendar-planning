from z3 import *

def main():
    # Cities: Amsterdam=0, Vienna=1, Santorini=2, Lyon=3
    n_days = 14
    n_cities = 4
    city_names = ['Amsterdam', 'Vienna', 'Santorini', 'Lyon']
    amsterdam, vienna, santorini, lyon = 0, 1, 2, 3
    
    # x[i] = city at the start of day i (end of previous day)
    x = [Int('x%d' % i) for i in range(n_days + 1)]
    
    s = Solver()
    
    # Start in Vienna at day 1
    s.add(x[0] == vienna)
    
    # Valid cities only
    for i in range(n_days + 1):
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
            current == next_,  # Stay in same city
            Or([And(current == a, next_ == b) for (a, b) in direct_flights])
        ))
    
    # Count full days per city (same city at start and end of day)
    full_days_in_city = [0] * n_cities
    for c in range(n_cities):
        total = 0
        for i in range(n_days):
            # Full day requires same city at start and end
            full_day = And(x[i] == c, x[i+1] == c)
            total += If(full_day, 1, 0)
        full_days_in_city[c] = total
    
    # Count partial days (for travel days)
    partial_days_in_city = [0] * n_cities
    for c in range(n_cities):
        total = 0
        for i in range(n_days):
            # Partial day: either start or end but not both
            in_city = Or(x[i] == c, x[i+1] == c)
            full_day = And(x[i] == c, x[i+1] == c)
            partial_day = And(in_city, Not(full_day))
            total += If(partial_day, 1, 0)
        partial_days_in_city[c] = total
    
    # Apply constraints: full days + partial days = total days
    s.add(full_days_in_city[vienna] + partial_days_in_city[vienna] == 7)
    s.add(full_days_in_city[amsterdam] + partial_days_in_city[amsterdam] == 3)
    s.add(full_days_in_city[santorini] + partial_days_in_city[santorini] == 4)
    s.add(full_days_in_city[lyon] + partial_days_in_city[lyon] == 3)
    
    # Workshop in Amsterdam (full day between 9-11)
    workshop_days = []
    for day in [9, 10, 11]:  # Days 9, 10, 11
        # Full day requires same city at start and end
        workshop_days.append(And(x[day-1] == amsterdam, x[day] == amsterdam))
    s.add(Or(workshop_days))
    
    # Wedding in Lyon (full day between 7-9)
    wedding_days = []
    for day in [7, 8, 9]:  # Days 7, 8, 9
        wedding_days.append(And(x[day-1] == lyon, x[day] == lyon))
    s.add(Or(wedding_days))
    
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