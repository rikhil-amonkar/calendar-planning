from z3 import *
import json

def main():
    # The 7 cities and their durations
    cities2 = ['Amsterdam', 'Barcelona', 'Florence', 'Tallinn', 'Venice', 'Vilnius', 'Warsaw']
    dur_arr = [2, 5, 5, 2, 3, 3, 4]  # matches the order of cities2

    # Flight graph: create direct_int_set for the 9 cities (0..6,7,8)
    city_index = {
        'Amsterdam': 0,
        'Barcelona': 1,
        'Florence': 2,
        'Tallinn': 3,
        'Venice': 4,
        'Vilnius': 5,
        'Warsaw': 6,
        'Paris': 7,
        'Hamburg': 8
    }

    # The direct flight list as strings (bidirectional)
    direct_flights_str = [
        ('Paris', 'Venice'), 
        ('Barcelona', 'Amsterdam'), 
        ('Amsterdam', 'Warsaw'), 
        ('Amsterdam', 'Vilnius'), 
        ('Barcelona', 'Warsaw'), 
        ('Warsaw', 'Venice'), 
        ('Amsterdam', 'Hamburg'), 
        ('Barcelona', 'Hamburg'), 
        ('Barcelona', 'Florence'), 
        ('Barcelona', 'Venice'), 
        ('Paris', 'Hamburg'), 
        ('Paris', 'Vilnius'), 
        ('Paris', 'Amsterdam'), 
        ('Paris', 'Florence'),
        ('Florence', 'Amsterdam'), 
        ('Vilnius', 'Warsaw'), 
        ('Barcelona', 'Tallinn'), 
        ('Paris', 'Warsaw'), 
        ('Tallinn', 'Warsaw'), 
        ('Tallinn', 'Vilnius'),
        ('Amsterdam', 'Tallinn'), 
        ('Paris', 'Tallinn'), 
        ('Paris', 'Barcelona'), 
        ('Venice', 'Hamburg'), 
        ('Warsaw', 'Hamburg'), 
        ('Amsterdam', 'Venice')
    ]

    # Build direct_set as a set of string tuples with both orders
    direct_set_str = set()
    for a, b in direct_flights_str:
        direct_set_str.add((a, b))
        direct_set_str.add((b, a))

    # Build direct_int_set: a set of integer tuples for the pairs in the 9 cities
    direct_int_set = set()
    for a, b in direct_set_str:
        if a in city_index and b in city_index:
            i1 = city_index[a]
            i2 = city_index[b]
            direct_int_set.add((i1, i2))

    # Precompute allowed_pairs for the 7 cities (0..6)
    allowed_pairs_middle = set((a, b) for (a, b) in direct_int_set if a in range(7) and b in range(7))

    # Allowed last cities in the 7 that have a direct flight to Hamburg
    allowed_last_cities = set()
    for a in range(7):
        if (a, 8) in direct_int_set:
            allowed_last_cities.add(a)

    # Z3 solver
    s = Solver()

    # The 7 variables for the permutation: c0..c6 for positions 2-8
    c = [Int('c%d' % i) for i in range(7)]
    for i in range(7):
        s.add(c[i] >= 0, c[i] <= 6)
    s.add(Distinct(c))

    # Durations for each position: d0..d6
    d = [Int('d%d' % i) for i in range(7)]
    for i in range(7):
        cases = []
        for idx in range(7):
            cases.append(And(c[i] == idx, d[i] == dur_arr[idx]))
        s.add(Or(cases))

    # Start days for the 7 positions
    start_day = [Int('start_day%d' % i) for i in range(7)]
    s.add(start_day[0] == 2)
    for i in range(1, 7):
        s.add(start_day[i] == start_day[i-1] + d[i-1] - 1)

    # End of the last of the 7 must be 19 (since Hamburg starts at 19)
    s.add(start_day[6] + d[6] - 1 == 19)

    # Barcelona constraint: start day between 1 and 6
    barcelona_constraint = []
    for i in range(7):
        barcelona_constraint.append(And(c[i] == 1, start_day[i] >= 1, start_day[i] <= 6))
    s.add(Or(barcelona_constraint))

    # Tallinn constraint: start day between 10 and 12
    tallinn_constraint = []
    for i in range(7):
        tallinn_constraint.append(And(c[i] == 3, start_day[i] >= 10, start_day[i] <= 12))
    s.add(Or(tallinn_constraint))

    # Flight constraints: last city must connect to Hamburg
    s.add(Or([c[6] == idx for idx in allowed_last_cities]))

    # Consecutive cities must have direct flights
    for i in range(6):
        consec_constraint = []
        for (a, b) in allowed_pairs_middle:
            consec_constraint.append(And(c[i] == a, c[i+1] == b))
        s.add(Or(consec_constraint))

    # Solve
    if s.check() == sat:
        model = s.model()
        c_val = [model.eval(c[i]).as_long() for i in range(7)]
        
        # Build stays for all cities
        stays = [('Paris', 1, 2)]  # Paris fixed
        
        current_end = 2  # End of Paris
        for i in range(7):
            city_idx = c_val[i]
            city_name = cities2[city_idx]
            start = current_end
            duration = dur_arr[city_idx]
            end = start + duration - 1
            stays.append((city_name, start, end))
            current_end = end
        
        # Add Hamburg and Salzburg
        stays.append(('Hamburg', 19, 22))
        stays.append(('Salzburg', 22, 25))
        
        # Build itinerary
        itinerary = []
        for day in range(1, 26):
            cities_today = []
            for (name, start, end) in stays:
                if start <= day <= end:
                    cities_today.append(name)
            cities_today.sort()
            itinerary.append({"day": day, "place": cities_today})
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()