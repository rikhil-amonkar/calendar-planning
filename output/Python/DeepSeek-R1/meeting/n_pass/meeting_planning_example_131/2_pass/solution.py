import json

def format_time(minutes):
    hours = minutes // 60
    minutes_part = minutes % 60
    return f"{hours:02d}:{minutes_part:02d}"

def main():
    base = 9 * 60  # 9:00 AM in minutes (540)
    
    travel_times = {
        ('PacificHeights', 'Presidio'): 11,
        ('PacificHeights', 'Marina'): 6,
        ('Presidio', 'PacificHeights'): 11,
        ('Presidio', 'Marina'): 10,
        ('Marina', 'PacificHeights'): 7,
        ('Marina', 'Presidio'): 10
    }
    
    constraints = {
        'Jason': (10 * 60, 16 * 60 + 15),    # 10:00-16:15 (600-975 min)
        'Kenneth': (15 * 60 + 30, 16 * 60 + 45)  # 15:30-16:45 (930-1005 min)
    }
    
    durations = {
        'Jason': 90,
        'Kenneth': 45
    }
    
    locations = {
        'Jason': 'Presidio',
        'Kenneth': 'Marina'
    }
    
    current_location = 'PacificHeights'
    current_time = base
    
    # Calculate earliest possible start time for Jason
    travel_to_jason = travel_times[(current_location, locations['Jason'])]
    jason_start_min = max(current_time + travel_to_jason, constraints['Jason'][0])
    # Calculate latest possible start time considering Kenneth's constraints
    jason_start_max = min(
        constraints['Jason'][1] - durations['Jason'],  # 885 min (14:45)
        constraints['Kenneth'][1] - durations['Kenneth'] - travel_times[(locations['Jason'], locations['Kenneth'])] - durations['Jason']  # 860 min (14:20)
    )
    
    if jason_start_min <= jason_start_max:
        # Ideal time to balance waits (690.5 min) - evaluate nearest integers
        candidates = [691, 690]  # Prefer 691 if tie
        best_t1 = None
        best_max_wait = float('inf')
        
        for t1 in candidates:
            if t1 < jason_start_min or t1 > jason_start_max:
                continue
            # Calculate initial wait at Presidio
            wait_start = t1 - (current_time + travel_to_jason)
            # Calculate arrival time at Marina
            arrival_marina = t1 + durations['Jason'] + travel_times[(locations['Jason'], locations['Kenneth'])]
            # Calculate wait at Marina (if any)
            wait_marina = max(0, constraints['Kenneth'][0] - arrival_marina)
            max_wait = max(wait_start, wait_marina)
            
            if max_wait < best_max_wait:
                best_max_wait = max_wait
                best_t1 = t1
        
        if best_t1 is None:
            best_t1 = jason_start_min
        
        # Build itinerary
        jason_start = best_t1
        jason_end = jason_start + durations['Jason']
        arrival_marina = jason_end + travel_times[(locations['Jason'], locations['Kenneth'])]
        kenneth_start = max(arrival_marina, constraints['Kenneth'][0])
        kenneth_end = kenneth_start + durations['Kenneth']
        
        itinerary = [
            {
                "action": "meet",
                "location": locations['Jason'],
                "person": "Jason",
                "start_time": format_time(jason_start),
                "end_time": format_time(jason_end)
            },
            {
                "action": "meet",
                "location": locations['Kenneth'],
                "person": "Kenneth",
                "start_time": format_time(kenneth_start),
                "end_time": format_time(kenneth_end)
            }
        ]
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        # Fallback if scheduling both isn't possible (not needed here)
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()