from z3 import *

def solve_itinerary():
    s = Solver()
    
    cities = ["Stuttgart", "Split", "Helsinki", "Brussels", "Bucharest", "London", "Mykonos", "Madrid"]
    n = len(cities)
    total_days = 21
    travel_days = [5, 10, 15, 20]
    
    # Segment assignment for each city
    segment = [Int(f"segment_{i}") for i in range(n)]
    
    # Each city is assigned to a unique segment
    s.add(Distinct(segment))
    for i in range(n):
        s.add(segment[i] >= 0, segment[i] < n)
    
    # Start and end days for each segment
    start = [Int(f"start_{i}") for i in range(n)]
    end = [Int(f"end_{i}") for i in range(n)]
    
    # Travel days between segments (end of segment i and start of segment i+1)
    travel = [Int(f"travel_{i}") for i in range(n-1)]
    
    # First city starts on day 1
    s.add(start[0] == 1)
    # Last city ends on day 21
    s.add(end[n-1] == total_days)
    
    # Segment 0 must be Stuttgart
    s.add(segment[0] == cities.index("Stuttgart"))
    # Last segment must be Madrid
    s.add(segment[n-1] == cities.index("Madrid"))
    
    # Ensure travel days are in {5,10,15,20}
    for i in range(n-1):
        s.add(Or([travel[i] == d for d in travel_days]))
    
    # Connectivity: end of segment i is the day before travel, and start of next is the travel day
    for i in range(n-1):
        s.add(end[i] == travel[i] - 1)
        s.add(start[i+1] == travel[i])
    
    # Consecutive days within a segment
    for i in range(n):
        s.add(end[i] >= start[i])
        duration = end[i] - start[i] + 1
        if i == 0:
            # First segment must have at least 4 days (since travel on day 5 is the earliest)
            s.add(duration >= 4)
        else:
            s.add(duration >= 1)
    
    # For segments, ensure they are ordered by start day
    for i in range(n-1):
        s.add(start[i] < start[i+1])
        s.add(end[i] < start[i+1])
    
    # Sum of durations must be 21
    total_duration = Int("total_duration")
    s.add(total_duration == total_days)
    durations = [end[i] - start[i] + 1 for i in range(n)]
    s.add(sum(durations) == total_days)
    
    # Exactly one city has a duration of 1, others >= 2
    one_day_city = Int("one_day_city")
    s.add(one_day_city >= 0, one_day_city < n)
    for i in range(n):
        duration = end[i] - start[i] + 1
        if i == 0:
            # First city cannot be 1 day
            s.add(duration != 1)
        else:
            s.add(Implies(one_day_city == i, duration == 1))
            s.add(Implies(one_day_city != i, duration >= 2))
    
    if s.check() == sat:
        model = s.model()
        seg_order = [model.evaluate(segment[i]).as_long() for i in range(n)]
        start_days = [model.evaluate(start[i]).as_long() for i in range(n)]
        end_days = [model.evaluate(end[i]).as_long() for i in range(n)]
        
        itinerary = []
        for i in range(n):
            city_index = seg_order[i]
            s_day = start_days[i]
            e_day = end_days[i]
            if s_day == e_day:
                day_range = f"Day {s_day}"
            else:
                day_range = f"Day {s_day}-{e_day}"
            itinerary.append({'day_range': day_range, 'place': cities[city_index]})
        
        return {'itinerary': itinerary}
    else:
        return None

result = solve_itinerary()
if result is not None:
    print(result)
else:
    print("No valid itinerary found.")