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
    
    # Generate bidirectional flight connections
    directed_flights = set()
    for a, b in allowed_flights:
        directed_flights.add((a, b))
        directed_flights.add((b, a))
    
    s = Solver()
    
    # Create Z3 variables
    order = [Int('order_%d' % i) for i in range(10)]
    starts = [Int('start_%d' % i) for i in range(10)]
    ends = [Int('end_%d' % i) for i in range(10)]
    
    # Ensure valid city indices and distinct order
    for i in range(10):
        s.add(order[i] >= 0, order[i] < 10)
    s.add(Distinct(order))
    
    # Prevent Krakow from being first city
    s.add(order[0] != 0)
    # Prevent Istanbul from being last city
    s.add(order[9] != 4)
    
    # Create duration array for symbolic access
    duration_arr = Array('durations', IntSort(), IntSort())
    for i, d in enumerate(durations):
        s.add(duration_arr[i] == d)
    
    # First city starts on day 1
    s.add(starts[0] == 1)
    s.add(ends[0] == starts[0] + Select(duration_arr, order[0]) - 1)
    
    # Consecutive cities have contiguous stays
    for i in range(1, 10):
        s.add(starts[i] == ends[i-1])
        s.add(ends[i] == starts[i] + Select(duration_arr, order[i]) - 1)
    
    # Total trip must end on day 32
    s.add(ends[9] == 32)
    
    # Fixed event constraints
    for i in range(10):
        # Krakow must be exactly days 5-9
        s.add(Implies(order[i] == 0, starts[i] == 5))
        s.add(Implies(order[i] == 0, ends[i] == 9))
        # Istanbul must be exactly days 25-29
        s.add(Implies(order[i] == 4, starts[i] == 25))
        s.add(Implies(order[i] == 4, ends[i] == 29))
    
    # Flight constraints between consecutive cities
    for i in range(9):
        current_city = order[i]
        next_city = order[i+1]
        # Check if flight exists in either direction
        constraints = []
        for a, b in directed_flights:
            constraints.append(And(current_city == a, next_city == b))
        s.add(Or(constraints))
    
    # Find valid itinerary
    if s.check() == sat:
        m = s.model()
        order_val = [m.evaluate(order[i]).as_long() for i in range(10)]
        starts_val = [m.evaluate(starts[i]).as_long() for i in range(10)]
        ends_val = [m.evaluate(ends[i]).as_long() for i in range(10)]
        
        itinerary = []
        for i in range(10):
            city_idx = order_val[i]
            city = cities[city_idx]
            for day in range(starts_val[i], ends_val[i] + 1):
                itinerary.append({"day": day, "city": city})
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()