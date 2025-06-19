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
    
    # Travel constraints for day 0 (from start to c[0])
    s.add(Implies(c[0] != 0, flight_ok(0, c[0])))
    
    # Travel constraints for days 1 to 19
    for i in range(1, 20):
        s.add(Implies(c[i] != c[i-1], flight_ok(c[i-1], c[i])))
    
    # Total travel days must be 6
    moves = []
    moves.append(If(c[0] != 0, 1, 0))
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
    # Day 1: always true because we start in Berlin
    # Day 3: represented by day index 2 (c[1] and c[2])
    s.add(Or(0 == c[1], 0 == c[2]))
    # Barcelona must be present on day 3 and day 4
    s.add(Or(4 == c[1], 4 == c[2]))  # day3 (index2: c[1] and c[2])
    s.add(Or(4 == c[2], 4 == c[3]))  # day4 (index3: c[2] and c[3])
    # Lyon must be present on day 4 and day 5
    s.add(Or(6 == c[2], 6 == c[3]))  # day4 (index3: c[2] and c[3])
    s.add(Or(6 == c[3], 6 == c[4]))  # day5 (index4: c[3] and c[4])
    
    if s.check() == sat:
        m = s.model()
        c_vals = [m.evaluate(c[i]) for i in range(20)]
        c_vals_int = [c_val.as_long() for c_val in c_vals]
        
        # Build the daily sets
        daily_sets = []
        # Day 1 (index0): start at 0 (Berlin), end at c_vals_int[0]
        day0_set = {0}
        if c_vals_int[0] != 0:
            day0_set.add(c_vals_int[0])
        daily_sets.append(day0_set)
        
        for i in range(1, 20):
            if c_vals_int[i] == c_vals_int[i-1]:
                day_set = {c_vals_int[i]}
            else:
                day_set = {c_vals_int[i-1], c_vals_int[i]}
            daily_sets.append(day_set)
        
        # Print the plan
        for day_idx, cities_set in enumerate(daily_sets):
            city_names = sorted([cities[city] for city in cities_set])
            print(f"Day {day_idx+1}: {', '.join(city_names)}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()