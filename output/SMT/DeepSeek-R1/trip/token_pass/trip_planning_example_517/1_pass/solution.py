from z3 import *
import json

def main():
    # Cities encoding
    cities = ['Dubrovnik', 'Warsaw', 'Stuttgart', 'Bucharest', 'Copenhagen']
    n_days = 19
    n_cities = len(cities)
    
    # Required days per city
    required_days = [5, 2, 7, 6, 3]
    
    # Direct flights (undirected)
    flights = [(1,4), (2,4), (1,2), (3,4), (3,1), (4,0)]
    
    # Z3 variables
    city_day = [Int(f'city_day_{i}') for i in range(n_days)]
    flight_day = [Bool(f'flight_day_{i}') for i in range(n_days-1)]
    
    solver = Solver()
    
    # Constraint 1: Each city_day is within [0,4]
    for i in range(n_days):
        solver.add(And(city_day[i] >= 0, city_day[i] <= 4))
    
    # Constraint 2: Flight day constraints (direct flights or same city)
    for i in range(n_days-1):
        solver.add(If(flight_day[i],
                      Or([Or(And(city_day[i] == a, city_day[i+1] == b),
                           And(city_day[i] == b, city_day[i+1] == a)) for (a,b) in flights]),
                      city_day[i] == city_day[i+1]))
    
    # Constraint 3: Total flight days = 4
    solver.add(Sum([If(flight_day[i], 1, 0) for i in range(n_days-1)]) == 4)
    
    # Constraint 4: Count days per city
    city_count = [Int(f'city_count_{c}') for c in range(n_cities)]
    count_expr = [0] * n_cities
    # Day 1
    for c in range(n_cities):
        count_expr[c] = If(city_day[0] == c, 1, 0)
    # Days 2 to 19
    for d in range(1, n_days):
        for c in range(n_cities):
            cond = If(flight_day[d-1],
                      Or(city_day[d-1] == c, city_day[d] == c),
                      city_day[d] == c)
            count_expr[c] = count_expr[c] + If(cond, 1, 0)
    for c in range(n_cities):
        solver.add(city_count[c] == count_expr[c])
        solver.add(city_count[c] == required_days[c])
    
    # Constraint 5: Stuttgart on day 7 and day 13
    # Day 7 (index 6)
    solver.add(If(flight_day[5],
                  Or(city_day[5] == 2, city_day[6] == 2),
                  city_day[6] == 2))
    # Day 13 (index 12)
    solver.add(If(flight_day[11],
                  Or(city_day[11] == 2, city_day[12] == 2),
                  city_day[12] == 2))
    
    # Constraint 6: Wedding in Bucharest between day 1 and day 6
    wedding_constraints = []
    # Day 1
    wedding_constraints.append(city_day[0] == 3)
    # Days 2 to 6
    for i in range(0,5):
        wedding_constraints.append(
            If(flight_day[i],
               Or(city_day[i] == 3, city_day[i+1] == 3),
               city_day[i+1] == 3))
    solver.add(Or(wedding_constraints))
    
    # Solve
    if solver.check() == sat:
        model = solver.model()
        city_day_vals = [model.evaluate(city_day[i]).as_long() for i in range(n_days)]
        # Group consecutive days
        itinerary_segments = []
        start_index = 0
        for i in range(1, n_days):
            if city_day_vals[i] != city_day_vals[i-1]:
                end_day = i
                itinerary_segments.append({
                    'start': start_index + 1,
                    'end': end_day,
                    'city': cities[city_day_vals[start_index]]
                })
                start_index = i
        itinerary_segments.append({
            'start': start_index + 1,
            'end': n_days,
            'city': cities[city_day_vals[start_index]]
        })
        # Format output
        itinerary = []
        for seg in itinerary_segments:
            start = seg['start']
            end = seg['end']
            if start == end:
                day_range = f"Day {start}"
            else:
                day_range = f"Day {start}-{end}"
            itinerary.append({
                'day_range': day_range,
                'place': seg['city']
            })
        result = {'itinerary': itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()