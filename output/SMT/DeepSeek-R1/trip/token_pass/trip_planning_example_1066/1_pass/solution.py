import json
from z3 import *

def main():
    # Define cities and mapping
    cities = ['Brussels', 'Bucharest', 'Stuttgart', 'Mykonos', 'Madrid', 'Helsinki', 'Split', 'London']
    city_dict = {c: i for i, c in enumerate(cities)}
    rev_city_dict = {i: c for i, c in enumerate(cities)}
    
    # Required days per city
    req_days = [4, 3, 4, 2, 2, 5, 3, 5]
    
    # Direct flights
    direct_flights_str = [
        ('Helsinki', 'London'), ('Split', 'Madrid'), ('Helsinki', 'Madrid'), ('London', 'Madrid'),
        ('Brussels', 'London'), ('Bucharest', 'London'), ('Brussels', 'Bucharest'), ('Bucharest', 'Madrid'),
        ('Split', 'Helsinki'), ('Mykonos', 'Madrid'), ('Stuttgart', 'London'), ('Helsinki', 'Brussels'),
        ('Brussels', 'Madrid'), ('Split', 'London'), ('Stuttgart', 'Split'), ('London', 'Mykonos')
    ]
    
    allowed_pairs = set()
    for (c1, c2) in direct_flights_str:
        i1 = city_dict[c1]
        i2 = city_dict[c2]
        allowed_pairs.add((i1, i2))
        allowed_pairs.add((i2, i1))
    
    # Initialize solver
    s = Solver()
    
    # Variables for each day (1 to 21)
    days = list(range(1, 22))
    morning = [Int('morning_%d' % d) for d in days]
    evening = [Int('evening_%d' % d) for d in days]
    
    # Domain constraints
    for i in range(21):
        s.add(And(morning[i] >= 0, morning[i] < 8))
        s.add(And(evening[i] >= 0, evening[i] < 8))
    
    # Consistency: evening[i] equals morning[i+1]
    for i in range(20):
        s.add(evening[i] == morning[i+1])
    
    # Travel constraints: if travel day, must use allowed flight
    for i in range(21):
        travel_day = (morning[i] != evening[i])
        constraints = []
        for (a, b) in allowed_pairs:
            constraints.append(And(morning[i] == a, evening[i] == b))
        s.add(If(travel_day, Or(constraints), True))
    
    # City count constraints
    for c in range(8):
        total = 0
        for i in range(21):
            total += If(morning[i] == c, 1, 0)
            total += If(And(evening[i] == c, morning[i] != evening[i]), 1, 0)
        s.add(total == req_days[c])
    
    # Madrid constraints (days 20 and 21)
    madrid_index = city_dict['Madrid']
    s.add(morning[19] == madrid_index)  # Day 20
    s.add(evening[19] == madrid_index)
    s.add(morning[20] == madrid_index)  # Day 21
    s.add(evening[20] == madrid_index)
    
    # Stuttgart meeting constraint (days 1-4)
    stuttgart_index = city_dict['Stuttgart']
    stuttgart_constraints = []
    for i in range(0, 4):
        stuttgart_constraints.append(morning[i] == stuttgart_index)
        stuttgart_constraints.append(And(evening[i] == stuttgart_index, morning[i] != evening[i]))
    s.add(Or(stuttgart_constraints))
    
    # Solve
    if s.check() == sat:
        m = s.model()
        morning_values = [m.evaluate(morning[i]).as_long() for i in range(21)]
        itinerary_cities = [rev_city_dict[idx] for idx in morning_values]
        
        # Group consecutive days with the same city
        segments = []
        start_day = 1
        current_city = itinerary_cities[0]
        
        for day in range(2, 22):
            if itinerary_cities[day-1] != current_city:
                end_day = day - 1
                if start_day == end_day:
                    day_range = f"Day {start_day}"
                else:
                    day_range = f"Day {start_day}-{end_day}"
                segments.append({"day_range": day_range, "place": current_city})
                current_city = itinerary_cities[day-1]
                start_day = day
        
        # Add the last segment
        if start_day == 21:
            day_range = "Day 21"
        else:
            day_range = f"Day {start_day}-21"
        segments.append({"day_range": day_range, "place": current_city})
        
        # Output as JSON
        result = {"itinerary": segments}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()