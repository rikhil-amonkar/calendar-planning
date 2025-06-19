import json

def main():
    base = 9 * 60  # 9:00 AM in minutes from midnight (540 minutes)
    
    travel_times = {
        ('PacificHeights', 'Presidio'): 11,
        ('PacificHeights', 'Marina'): 6,
        ('Presidio', 'PacificHeights'): 11,
        ('Presidio', 'Marina'): 10,
        ('Marina', 'PacificHeights'): 7,
        ('Marina', 'Presidio'): 10
    }
    
    constraints = {
        'Jason': (10 * 60, 16 * 60 + 15),    # 10:00 to 16:15 (600 to 975 minutes)
        'Kenneth': (15 * 60 + 30, 16 * 60 + 45)  # 15:30 to 16:45 (930 to 1005 minutes)
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
    
    # Calculate feasible start time range for Jason
    travel_to_jason = travel_times[(current_location, locations['Jason'])]
    jason_start_min = max(current_time + travel_to_jason, constraints['Jason'][0])
    jason_start_max = min(
        constraints['Jason'][1] - durations['Jason'],
        constraints['Kenneth'][1] - durations['Kenneth'] - travel_times[('Presidio', 'Marina')] - durations['Jason']
    )
    
    # If meeting both is feasible
    if jason_start_min <= jason_start_max:
        # Candidates to minimize maximum wait
        t1_candidate1 = 690  # 11:30 AM
        t1_candidate2 = 691  # 11:31 AM
        best_t1 = None
        best_max_wait = float('inf')
        
        for t1 in [t1_candidate1, t1_candidate2]:
            if t1 < jason_start_min or t1 > jason_start_max:
                continue
            wait_start = (t1 - travel_to_jason) - base
            arrival_at_marina = t1 + durations['Jason'] + travel_times[('Presidio', 'Marina')]
            wait_marina = max(0, constraints['Kenneth'][0] - arrival_at_marina)
            max_wait = max(wait_start, wait_marina)
            if max_wait < best_max_wait:
                best_max_wait = max_wait
                best_t1 = t1
        
        if best_t1 is None:
            best_t1 = jason_start_min
        
        jason_start_abs = best_t1
        jason_end_abs = jason_start_abs + durations['Jason']
        arrival_at_marina = jason_end_abs + travel_times[('Presidio', 'Marina')]
        kenneth_start_abs = max(arrival_at_marina, constraints['Kenneth'][0])
        kenneth_end_abs = kenneth_start_abs + durations['Kenneth']
        
        def format_time(minutes):
            hours = minutes // 60
            minutes_part = minutes % 60
            return f"{hours}:{minutes_part:02d}"
        
        itinerary = [
            {
                "action": "meet",
                "location": locations['Jason'],
                "person": "Jason",
                "start_time": format_time(jason_start_abs),
                "end_time": format_time(jason_end_abs)
            },
            {
                "action": "meet",
                "location": locations['Kenneth'],
                "person": "Kenneth",
                "start_time": format_time(kenneth_start_abs),
                "end_time": format_time(kenneth_end_abs)
            }
        ]
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        # Fallback to meeting only one if both not feasible (though both are feasible here)
        pass

if __name__ == "__main__":
    main()