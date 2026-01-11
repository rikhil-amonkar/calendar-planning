import itertools
import json

def solve():
    cities = ["Bucharest", "Venice", "Prague", "Frankfurt", "Zurich", "Florence", "Tallinn"]
    required_days = {
        "Bucharest": 3,
        "Venice": 5,
        "Prague": 4,
        "Frankfurt": 5,
        "Zurich": 5,
        "Florence": 5,
        "Tallinn": 5
    }
    
    direct_flights = [
        ("Prague", "Tallinn"),
        ("Prague", "Zurich"),
        ("Florence", "Prague"),
        ("Frankfurt", "Bucharest"),
        ("Frankfurt", "Venice"),
        ("Prague", "Bucharest"),
        ("Bucharest", "Zurich"),
        ("Tallinn", "Frankfurt"),
        ("Zurich", "Florence"),
        ("Frankfurt", "Zurich"),
        ("Zurich", "Venice"),
        ("Florence", "Frankfurt"),
        ("Prague", "Frankfurt"),
        ("Tallinn", "Zurich")
    ]
    
    # Make it undirected
    flight_set = set()
    for a, b in direct_flights:
        flight_set.add((a, b))
        flight_set.add((b, a))
    
    # Fixed date ranges (1-based days)
    fixed = {
        "Tallinn": (8, 12),
        "Frankfurt": (12, 16),
        "Venice": (22, 26)
    }
    
    # Check if a sequence can be scheduled
    def can_schedule(order):
        # We need to assign start day for each city
        # Total calendar days = 26
        # Start day of first city = 1
        # When moving from city i to i+1 on travel day d, 
        # city i ends on d, city i+1 starts on d (overlap)
        
        # We'll simulate
        day = 1
        schedule = []
        
        for i, city in enumerate(order):
            needed = required_days[city]
            if i == 0:
                start = day
                end = start + needed - 1
                schedule.append((city, start, end))
                day = end  # last day in this city
            else:
                # Check flight connection
                if (order[i-1], city) not in flight_set:
                    return None
                # Travel day is the same as last day of previous city
                # So previous city ended on 'day'
                # This city starts on 'day' (overlap)
                start = day
                end = start + needed - 1
                schedule.append((city, start, end))
                day = end  # update current day to last day in this city
        
        total_calendar_days = schedule[-1][2]  # last end day
        if total_calendar_days != 26:
            return None
        
        # Check fixed constraints
        for city, (fixed_start, fixed_end) in fixed.items():
            # Find this city in schedule
            found = False
            for c, start, end in schedule:
                if c == city:
                    if not (start <= fixed_start and end >= fixed_end):
                        return None
                    found = True
                    break
            if not found:
                return None
        
        return schedule
    
    # Try all permutations
    for perm in itertools.permutations(cities):
        sched = can_schedule(perm)
        if sched is not None:
            # Convert to required output format
            itinerary = []
            for city, start, end in sched:
                if start == end:
                    day_range = f"Day {start}"
                else:
                    day_range = f"Day {start}-{end}"
                itinerary.append({"day_range": day_range, "place": city})
            return {"itinerary": itinerary}
    
    return {"itinerary": []}

if __name__ == "__main__":
    result = solve()
    print(json.dumps(result, indent=2))