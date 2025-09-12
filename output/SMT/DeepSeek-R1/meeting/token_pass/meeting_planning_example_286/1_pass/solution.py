from z3 import *
import json

def main():
    # Travel times in minutes between locations
    travel_times = {
        "Union Square": {
            "Mission District": 14,
            "Bayview": 15,
            "Sunset District": 26
        },
        "Mission District": {
            "Union Square": 15,
            "Bayview": 15,
            "Sunset District": 24
        },
        "Bayview": {
            "Union Square": 17,
            "Mission District": 13,
            "Sunset District": 23
        },
        "Sunset District": {
            "Union Square": 30,
            "Mission District": 24,
            "Bayview": 22
        }
    }
    
    # Convert all times to minutes since 9:00 AM
    meetings = [
        {
            "name": "Rebecca",
            "location": "Mission District",
            "avail_start": 11*60 + 30,  # 11:30 AM
            "avail_end": 20*60 + 15,    # 8:15 PM
            "min_dur": 120
        },
        {
            "name": "Karen",
            "location": "Bayview",
            "avail_start": 12*60 + 45,  # 12:45 PM
            "avail_end": 15*60 + 0,     # 3:00 PM
            "min_dur": 120
        },
        {
            "name": "Carol",
            "location": "Sunset District",
            "avail_start": 10*60 + 15,  # 10:15 AM
            "avail_end": 11*60 + 45,    # 11:45 AM
            "min_dur": 30
        }
    ]
    
    # Try to schedule all meetings, then subsets if needed
    best_schedule = None
    best_count = 0
    current_location = "Union Square"
    start_time = 0  # 9:00 AM in minutes
    
    # Try all subsets in descending order of size
    for subset_size in range(3, 0, -1):
        from itertools import combinations, permutations
        for subset in combinations(range(3), subset_size):
            for order in permutations(subset):
                s = Solver()
                start_vars = [Int(f"start_{i}") for i in range(subset_size)]
                dur_vars = [Int(f"dur_{i}") for i in range(subset_size)]
                travel_from = [None] * subset_size
                
                # Constraints for each meeting in the order
                prev_end = start_time
                prev_loc = current_location
                for idx, meet_idx in enumerate(order):
                    meet = meetings[meet_idx]
                    travel_time = travel_times[prev_loc][meet["location"]]
                    s.add(start_vars[idx] >= prev_end + travel_time)
                    s.add(start_vars[idx] >= meet["avail_start"])
                    s.add(start_vars[idx] + dur_vars[idx] <= meet["avail_end"])
                    s.add(dur_vars[idx] >= meet["min_dur"])
                    prev_end = start_vars[idx] + dur_vars[idx]
                    prev_loc = meet["location"]
                    travel_from[idx] = meet["location"]
                
                if s.check() == sat:
                    m = s.model()
                    schedule = []
                    for idx, meet_idx in enumerate(order):
                        meet = meetings[meet_idx]
                        start_val = m.evaluate(start_vars[idx]).as_long()
                        dur_val = m.evaluate(dur_vars[idx]).as_long()
                        end_val = start_val + dur_val
                        schedule.append({
                            "action": "meet",
                            "location": meet["location"],
                            "person": meet["name"],
                            "start_time": format_time(start_val),
                            "end_time": format_time(end_val)
                        })
                    if subset_size > best_count:
                        best_schedule = schedule
                        best_count = subset_size
                    break  # Found a schedule for this subset size
            if best_schedule is not None:
                break  # Break subset loop if found
        if best_schedule is not None:
            break  # Break size loop if found
    
    # Output the best schedule found
    if best_schedule is None:
        result = {"itinerary": []}
    else:
        result = {"itinerary": best_schedule}
    
    print(json.dumps(result, indent=2))

def format_time(minutes):
    total_minutes = minutes
    hours = total_minutes // 60
    mins = total_minutes % 60
    return f"{hours}:{mins:02d}"

if __name__ == "__main__":
    main()