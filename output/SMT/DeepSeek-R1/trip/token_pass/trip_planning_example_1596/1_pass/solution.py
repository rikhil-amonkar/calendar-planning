from z3 import *
import json

def main():
    # City mapping
    cities = {
        'Bucharest': 0,
        'Krakow': 1,
        'Munich': 2,
        'Barcelona': 3,
        'Warsaw': 4,
        'Budapest': 5,
        'Stockholm': 6,
        'Riga': 7,
        'Edinburgh': 8,
        'Vienna': 9
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Required days per city
    req_days = [2, 4, 3, 5, 5, 5, 2, 5, 5, 5]
    
    # Direct flights (as symmetric pairs)
    flight_pairs = [
        (5, 2), (0, 7), (2, 1), (2, 4), (2, 0), (8, 6), (3, 4), (8, 1), (3, 2),
        (6, 1), (5, 9), (3, 6), (6, 2), (8, 5), (3, 7), (8, 3), (9, 7), (3, 5),
        (0, 4), (9, 1), (8, 2), (3, 0), (8, 7), (9, 6), (4, 1), (3, 1), (7, 2),
        (9, 0), (5, 4), (9, 4), (3, 9), (5, 0), (9, 2), (7, 4), (6, 7), (6, 4)
    ]
    allowed_flights = set()
    for a, b in flight_pairs:
        allowed_flights.add((a, b))
        allowed_flights.add((b, a))
    
    # Events: (city_index, start_day, end_day)
    events = [
        (2, 18, 20),  # Munich workshop
        (4, 25, 29),  # Warsaw conference
        (5, 9, 13),   # Budapest show
        (6, 17, 18),  # Stockholm friends
        (8, 1, 5)     # Edinburgh friend
    ]
    
    # Create Z3 variables for c0 to c32
    n = 33
    c = IntVector('c', n)
    
    solver = Solver()
    
    # Constraint: each c_i must be between 0 and 9
    for i in range(n):
        solver.add(And(c[i] >= 0, c[i] <= 9))
    
    # Constraint: allowed flights for transitions
    for i in range(1, n):
        cond = Or([And(c[i-1] == a, c[i] == b) for (a, b) in allowed_flights])
        solver.add(If(c[i-1] != c[i], cond, True))
    
    # Constraint: required days per city
    for city_idx in range(10):
        total = 0
        for i in range(1, n):
            total += If(And(c[i-1] == c[i], c[i] == city_idx), 1, 0)
            total += If(And(c[i-1] != c[i], c[i-1] == city_idx), 1, 0)
            total += If(And(c[i-1] != c[i], c[i] == city_idx), 1, 0)
        solver.add(total == req_days[city_idx])
    
    # Constraint: events
    for (city_idx, start, end) in events:
        for day in range(start, end+1):
            # day index corresponds to c[day] for evening and c[day-1] for morning
            solver.add(Or(c[day-1] == city_idx, c[day] == city_idx))
    
    # Check and get model
    if solver.check() == sat:
        model = solver.model()
        seq = [model.evaluate(c[i]).as_long() for i in range(n)]
        
        # Generate itinerary segments
        segments = []
        for city_idx in range(10):
            days = []
            # Collect days where city appears (as morning or evening)
            for day in range(1, 33):  # day from 1 to 32
                if seq[day-1] == city_idx or seq[day] == city_idx:
                    days.append(day)
            # Group consecutive days
            if days:
                current_start = days[0]
                current_end = days[0]
                for i in range(1, len(days)):
                    if days[i] == current_end + 1:
                        current_end = days[i]
                    else:
                        segments.append((current_start, current_end, city_idx))
                        current_start = days[i]
                        current_end = days[i]
                segments.append((current_start, current_end, city_idx))
        
        # Sort segments by start day
        segments.sort(key=lambda x: x[0])
        
        # Convert to JSON output format
        itinerary = []
        for start, end, city_idx in segments:
            place = city_names[city_idx]
            if start == end:
                day_range = f"Day {start}"
            else:
                day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": place})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()