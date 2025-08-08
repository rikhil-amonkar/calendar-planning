import json
from z3 import *

def main():
    cities = ["Krakow", "Stockholm", "Hamburg", "Florence", "Istanbul", "Oslo", "Vilnius", "Santorini", "Munich", "Frankfurt"]
    durations = [5, 3, 5, 2, 5, 5, 5, 2, 5, 4]
    
    allowed_flights = [
        (5,1), (1,5),
        (0,9), (9,0),
        (0,4), (4,0),
        (8,1), (1,8),
        (2,1), (1,2),
        (0,6),
        (5,4), (4,5),
        (4,1), (1,4),
        (5,0), (0,5),
        (6,4), (4,6),
        (5,6), (6,5),
        (9,4), (4,9),
        (5,9), (9,5),
        (8,2), (2,8),
        (3,8),
        (0,8), (8,0),
        (2,4), (4,2),
        (9,1), (1,9),
        (1,7),
        (9,8), (8,9),
        (5,2), (2,5),
        (7,5),
        (0,1), (1,0),
        (6,8),
        (9,2), (2,9)
    ]
    
    # Generate all directed flight pairs for bidirectional travel
    directed_flights = set()
    for a, b in allowed_flights:
        directed_flights.add((a, b))
        directed_flights.add((b, a))
    directed_flights = list(directed_flights)
    
    s = Solver()
    
    order = [Int('c_%d' % i) for i in range(10)]
    starts = [Int('start_%d' % i) for i in range(10)]
    ends = [Int('end_%d' % i) for i in range(10)]
    
    # Ensure city indices are valid and distinct
    for i in range(10):
        s.add(order[i] >= 0, order[i] < 10)
    s.add(Distinct(order))
    
    # Create Z3 array for durations
    duration_arr = Array('durations', IntSort(), IntSort())
    for i, d in enumerate(durations):
        s.add(duration_arr[i] == d)
    
    # First city starts on day 1
    s.add(starts[0] == 1)
    s.add(ends[0] == starts[0] + Select(duration_arr, order[0]) - 1)
    
    # Subsequent cities start where the previous ended
    for i in range(1, 10):
        s.add(starts[i] == ends[i-1])
        s.add(ends[i] == starts[i] + Select(duration_arr, order[i]) - 1)
    
    # Total trip must end on day 32
    s.add(ends[9] == 32)
    
    # Fixed constraints for Krakow and Istanbul
    for k in range(10):
        s.add(Implies(order[k] == 0, starts[k] == 5))
        s.add(Implies(order[k] == 0, ends[k] == 9))
        s.add(Implies(order[k] == 4, starts[k] == 25))
        s.add(Implies(order[k] == 4, ends[k] == 29))
    
    # Flight constraints between consecutive cities
    for i in range(9):
        current_city = order[i]
        next_city = order[i+1]
        allowed = Or([And(current_city == a, next_city == b) for a, b in directed_flights])
        s.add(allowed)
    
    # Generate itinerary if solution exists
    if s.check() == sat:
        m = s.model()
        order_val = [m.evaluate(order[i]).as_long() for i in range(10)]
        starts_val = [m.evaluate(starts[i]).as_long() for i in range(10)]
        ends_val = [m.evaluate(ends[i]).as_long() for i in range(10)]
        
        itinerary_list = []
        for k in range(10):
            city_idx = order_val[k]
            city_name = cities[city_idx]
            start_day = starts_val[k]
            end_day = ends_val[k]
            for d in range(start_day, end_day + 1):
                itinerary_list.append({"day": d, "city": city_name})
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()