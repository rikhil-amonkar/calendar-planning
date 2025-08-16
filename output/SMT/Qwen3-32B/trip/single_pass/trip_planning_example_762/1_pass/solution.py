import json
from z3 import *

def main():
    cities_list = ['Dublin', 'Madrid', 'Oslo', 'London', 'Vilnius', 'Berlin']
    durations = [3, 2, 3, 2, 3, 5]  # index 0-5

    allowed_transitions = [
        (0,1), (1,0), 
        (0,2), (2,0), 
        (0,3), (3,0), 
        (0,5), (5,0), 
        (1,2), (2,1), 
        (1,3), (3,1), 
        (1,5), (5,1), 
        (2,4), (4,2), 
        (2,5), (5,2), 
        (3,2), (2,3), 
        (3,5), (5,3), 
        (4,5), (5,4), 
    ]

    solver = Solver()

    cities = [Int(f'city_{i}') for i in range(6)]
    start_days = [Int(f'start_day_{i}') for i in range(6)]

    # All cities are distinct and in 0-5
    solver.add(Distinct(cities))
    for c in cities:
        solver.add(And(c >= 0, c <= 5))

    # start_days[0] = 1
    solver.add(start_days[0] == 1)

    # For i >=1, start_days[i] = start_days[i-1] + duration_prev - 1
    for i in range(1, 6):
        prev_city = cities[i-1]
        # Compute duration_prev
        duration_prev = If(prev_city == 0, 3,
                           If(prev_city == 1, 2,
                              If(prev_city == 2, 3,
                                 If(prev_city == 3, 2,
                                    If(prev_city == 4, 3, 5)))))
        # start_days[i] = start_days[i-1] + duration_prev - 1
        solver.add(start_days[i] == start_days[i-1] + duration_prev - 1)

    # Constraints for event days
    for i in range(6):
        c = cities[i]
        # Dublin (0): start >=5, <=9
        solver.add(Implies(c == 0, And(start_days[i] >=5, start_days[i] <=9)))
        # Madrid (1): start <=3, >=1
        solver.add(Implies(c == 1, And(start_days[i] >=1, start_days[i] <=3)))
        # Berlin (5): start <=7
        solver.add(Implies(c == 5, start_days[i] <=7))

    # Flight constraints between consecutive cities
    for i in range(5):
        a = cities[i]
        b = cities[i+1]
        # Check if (a, b) is in allowed_transitions
        constraints = []
        for (x, y) in allowed_transitions:
            constraints.append(And(a == x, b == y))
        solver.add(Or(constraints))

    if solver.check() == sat:
        model = solver.model()
        # Extract cities order and start_days
        cities_order = [model.eval(cities[i]).as_long() for i in range(6)]
        start_days_values = [model.eval(start_days[i]).as_long() for i in range(6)]
        # Now generate the itinerary
        day_city = []
        for i in range(6):
            city_idx = cities_order[i]
            start = start_days_values[i]
            duration = durations[city_idx]
            city_name = cities_list[city_idx]
            for day in range(start, start + duration):
                day_city.append( (day, city_name) )
        # Now sort day_city by day
        day_city.sort()
        # Now create the itinerary list
        itinerary_list = [ {f'day_{day}': city} for day, city in day_city ]
        # Now create the JSON dictionary
        result = {'itinerary': itinerary_list}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()