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
    
    # First city starts on day 1
    s.add(start[0] == 1)
    # Last city ends on day 21
    s.add(end[n-1] == total_days)
    
    # Segment 0 must be Stuttgart
    s.add(segment[0] == cities.index("Stuttgart"))
    # Last segment must be Madrid
    s.add(segment[n-1] == cities.index("Madrid"))
    
    # Connectivity: end of segment i is the day before the next segment's start
    for i in range(n-1):
        next_start = Int(f"next_start_{i}")
        s.add(next_start == start[i+1])
        s.add(end[i] == next_start - 1)
        # Ensure travel day (start of next segment) is in travel_days
        s.add(Or([next_start == d for d in travel_days]))
    
    # Consecutive days within a segment
    for i in range(n):
        s.add(end[i] >= start[i])
        duration = end[i] - start[i] + 1
        s.add(duration >= 1)
    
    # For segments, ensure they are ordered by start day
    for i in range(n-1):
        s.add(start[i] < start[i+1])
        s.add(end[i] < start[i+1])
    
    # Sum of durations must be 21
    durations = [end[i] - start[i] + 1 for i in range(n)]
    s.add(sum(durations) == total_days)
    
    # Exactly one city has a duration of 1, others >= 2
    one_day_city = Int("one_day_city")
    s.add(one_day_city >= 0, one_day_city < n)
    for i in range(n):
        duration = end[i] - start[i] + 1
        if i == 0:
            # First city must be at least 4 days (since earliest travel is day 5)
            s.add(duration >= 4)
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