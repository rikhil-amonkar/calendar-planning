from z3 import *

def solve_itinerary():
    s = Solver()
    
    cities = ["Stuttgart", "Split", "Helsinki", "Brussels", "Bucharest", "London", "Mykonos", "Madrid"]
    n = len(cities)
    travel_days = [5, 10, 15, 20]
    num_travels = len(travel_days)
    
    # Segment assignment for each city
    segment = [Int(f"segment_{i}") for i in range(n)]
    for i in range(n):
        s.add(segment[i] >= 0, segment[i] < n)
    s.add(Distinct(segment))
    
    # First segment is Stuttgart, last is Madrid
    s.add(segment[0] == cities.index("Stuttgart"))
    s.add(segment[n-1] == cities.index("Madrid"))
    
    # Start and end days for each segment
    start = [Int(f"start_{i}") for i in range(n)]
    end = [Int(f"end_{i}") for i in range(n)]
    
    # Travel indices for the 4 travels
    travel_index = [Int(f"travel_{i}") for i in range(num_travels)]
    for i in range(num_travels):
        s.add(travel_index[i] >= 1, travel_index[i] < n-1)
    
    # Travel indices are ordered and distinct
    s.add(Distinct(travel_index))
    for i in range(num_travels-1):
        s.add(travel_index[i] < travel_index[i+1])
    
    # First segment starts on day 1
    s.add(start[0] == 1)
    # Last segment ends on day 21
    s.add(end[n-1] == 21)
    
    # Connect segments with travel days
    for i in range(num_travels):
        idx = travel_index[i]
        # End of current segment is day before travel
        s.add(end[idx] == travel_days[i] - 1)
        # Next segment starts on travel day
        s.add(start[idx+1] == travel_days[i])
    
    # For segments not involving travel, end day is start of next segment minus 1
    k = 0
    for i in range(n-1):
        if i+1 == travel_index[k] if k < num_travels else False:
            k += 1
        else:
            s.add(end[i] == start[i+1] - 1)
    
    # Durations and constraints
    durations = []
    for i in range(n):
        duration = end[i] - start[i] + 1
        s.add(duration >= 1)
        durations.append(duration)
    
    # Total days = 21
    s.add(sum(durations) == 21)
    
    # Exactly one city has duration 1, others >= 2
    one_city = Int("one_city")
    s.add(one_city >= 0, one_city < n)
    for i in range(n):
        duration = end[i] - start[i] + 1
        s.add(If(one_city == i, duration == 1, duration >= 2))
    
    # Ensure travel indices point to different segments
    s.add(Distinct([travel_index[i] for i in range(num_travels)]))
    
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