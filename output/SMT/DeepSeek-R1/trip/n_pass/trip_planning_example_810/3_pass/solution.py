from z3 import *

def main():
    # City indices
    cities = {
        0: 'Berlin',
        1: 'Nice',
        2: 'Athens',
        3: 'Stockholm',
        4: 'Barcelona',
        5: 'Vilnius',
        6: 'Lyon'
    }
    required_days = [3, 5, 5, 5, 2, 4, 2]  # Berlin, Nice, Athens, Stockholm, Barcelona, Vilnius, Lyon
    
    allowed_flights = [
        (0, 1), (0, 2), (0, 3), (0, 4), (0, 5),
        (1, 2), (1, 3), (1, 4), (1, 6),
        (2, 3), (2, 4), (2, 5),
        (3, 4),
        (4, 6)
    ]
    
    s = Solver()
    c = [Int('c_%d' % i) for i in range(20)]
    
    # Each c[i] is between 0 and 6
    for i in range(20):
        s.add(And(c[i] >= 0, c[i] <= 6))
    
    # Helper function to check if a flight between a and b is allowed
    def flight_ok(a, b):
        conditions = []
        for (x, y) in allowed_flights:
            conditions.append(Or(And(a == x, b == y), And(a == y, b == x)))
        return Or(conditions)
    
    # Stay in Berlin for first two days (no travel)
    s.add(c[0] == 0)
    s.add(c[1] == 0)
    
    # Travel constraints for days 2 to 19
    for i in range(2, 20):
        s.add(Implies(c[i] != c[i-1], flight_ok(c[i-1], c[i])))
    
    # Total travel days must be 6
    moves = []
    for i in range(1, 20):
        moves.append(If(c[i] != c[i-1], 1, 0))
    s.add(sum(moves) == 6)
    
    # Total days per city
    for city_idx in range(7):
        total_days = 0
        for day in range(20):
            if day == 0:
                in_city = Or(city_idx == 0, city_idx == c[0])
            else:
                in_city = Or(city_idx == c[day-1], city_idx == c[day])
            total_days += If(in_city, 1, 0)
        s.add(total_days == required_days[city_idx])
    
    # Event constraints
    # Berlin must be present on day 1 and day 3
    s.add(Or(0 == c[1], 0 == c[2]))  # Day 3: c[1] and c[2]
    
    # Barcelona must be present on day 3 and day 4
    s.add(Or(4 == c[1], 4 == c[2]))  # Day 3
    s.add(Or(4 == c[2], 4 == c[3]))  # Day 4
    
    # Lyon must be present on day 4 and day 5
    s.add(Or(6 == c[2], 6 == c[3]))  # Day 4
    s.add(Or(6 == c[3], 6 == c[4]))  # Day 5
    
    if s.check() == sat:
        m = s.model()
        c_vals = [m.evaluate(c[i]) for i in range(20)]
        c_vals_int = [c_val.as_long() for c_val in c_vals]
        
        # Build the daily sets
        daily_sets = []
        # Day 1: start at Berlin (0), end at c[0] (0) -> only Berlin
        daily_sets.append({0})
        # Day 2: start at c[0] (0), end at c[1] (0) -> only Berlin
        daily_sets.append({0})
        
        # Days 3-20
        for i in range(2, 20):
            if c_vals_int[i] == c_vals_int[i-1]:
                daily_sets.append({c_vals_int[i]})
            else:
                daily_sets.append({c_vals_int[i-1], c_vals_int[i]})
        
        # Print the plan
        for day_idx, cities_set in enumerate(daily_sets):
            city_names = sorted([cities[city] for city in cities_set])
            print(f"Day {day_idx+1}: {', '.join(city_names)}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()