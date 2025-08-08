import json
from z3 import *

def main():
    # Define city names and their indices
    cities = ["Istanbul", "Rome", "Seville", "Naples", "Santorini"]
    req_days = [2, 3, 4, 7, 4]  # Days required for each city
    allowed_flights = [
        (0, 3), (3, 0),  # Istanbul <-> Naples
        (3, 4), (4, 3),  # Naples <-> Santorini
        (1, 4), (4, 1),  # Rome <-> Santorini
        (2, 1), (1, 2),  # Seville <-> Rome
        (0, 1), (1, 0),  # Istanbul <-> Rome
        (1, 3), (3, 1)   # Rome <-> Naples
    ]
    
    # Create solver and variables
    s = Solver()
    start = [Int('start_%d' % i) for i in range(5)]
    end = [Int('end_%d' % i) for i in range(5)]
    city = [Int('city_%d' % i) for i in range(5)]
    
    # Fixed constraints for the entire trip
    s.add(start[0] == 1)
    s.add(end[4] == 16)
    
    # Segments must be contiguous
    for i in range(4):
        s.add(end[i] == start[i+1])
    
    # Fixed segments for Istanbul and Santorini
    s.add(city[2] == 0)  # Istanbul
    s.add(start[2] == 6, end[2] == 7)
    s.add(city[4] == 4)  # Santorini
    s.add(start[4] == 13, end[4] == 16)
    
    # Other segments: Rome (1), Seville (2), Naples (3)
    s.add(city[0] >= 1, city[0] <= 3)
    s.add(city[1] >= 1, city[1] <= 3)
    s.add(city[3] == 3)  # Segment 3 must be Naples (7 days)
    s.add(Distinct(city[0], city[1], city[3]))
    
    # Length of each segment
    days_in_segment = [end[i] - start[i] + 1 for i in range(5)]
    
    # Total days per city must meet requirements
    for c in range(5):
        total = 0
        for i in range(5):
            total += If(city[i] == c, days_in_segment[i], 0)
        s.add(total == req_days[c])
    
    # Flight constraints between consecutive segments
    for i in range(4):
        s.add(Or([And(city[i] == a, city[i+1] == b) for (a, b) in allowed_flights]))
    
    # Ensure segment starts are within bounds
    s.add(start[1] >= 1, start[1] <= 6)
    s.add(start[3] == 7)  # Since end[2] = 7 and end[2] = start[3]
    
    # Check and get model
    if s.check() == sat:
        model = s.model()
        # Build itinerary
        itinerary = []
        for d in range(1, 17):  # Days 1 to 16
            for i in range(5):  # Check each segment
                start_val = model.evaluate(start[i]).as_long()
                end_val = model.evaluate(end[i]).as_long()
                if start_val <= d <= end_val:
                    city_idx = model.evaluate(city[i]).as_long()
                    itinerary.append({"day": d, "city": cities[city_idx]})
        # Output as JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()