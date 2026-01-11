import json
from itertools import permutations

def time_to_min(timestr):
    # "H:MM" or "HH:MM" to minutes from midnight
    h, m = map(int, timestr.split(':'))
    return h * 60 + m

def min_to_time(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

def main():
    # Locations indices
    loc_index = {
        "Sunset District": 0,
        "Russian Hill": 1,
        "Chinatown": 2,
        "Presidio": 3,
        "Fisherman's Wharf": 4
    }
    index_to_loc = {v: k for k, v in loc_index.items()}
    
    # Travel times matrix [from][to]
    travel = [
        [0, 24, 30, 16, 29],
        [23, 0, 9, 14, 7],
        [29, 7, 0, 19, 8],
        [15, 14, 21, 0, 19],
        [27, 7, 12, 17, 0]
    ]
    
    # People data: (location_index, window_start_min, window_end_min, min_duration_min)
    people = {
        "William": (loc_index["Russian Hill"], time_to_min("18:30"), time_to_min("20:45"), 105),
        "Michelle": (loc_index["Chinatown"], time_to_min("8:15"), time_to_min("14:00"), 15),
        "George": (loc_index["Presidio"], time_to_min("10:30"), time_to_min("18:45"), 30),
        "Robert": (loc_index["Fisherman's Wharf"], time_to_min("9:00"), time_to_min("13:45"), 30)
    }
    
    start_time = time_to_min("9:00")
    start_loc = loc_index["Sunset District"]
    
    # We must meet William at 18:30 exactly for 105 minutes
    william_fixed_start = time_to_min("18:30")
    william_fixed_end = william_fixed_start + 105
    
    best_schedule = None
    best_count = 0
    
    # Try all permutations of the other 3 people before William
    others = [("Michelle", *people["Michelle"]), 
              ("George", *people["George"]), 
              ("Robert", *people["Robert"])]
    
    for perm in permutations(others):
        current_time = start_time
        current_loc = start_loc
        schedule = []
        possible = True
        
        for name, loc, win_start, win_end, dur in perm:
            # Travel to this person
            travel_time = travel[current_loc][loc]
            arrival = current_time + travel_time
            start_meeting = max(arrival, win_start)
            if start_meeting + dur > win_end:
                possible = False
                break
            end_meeting = start_meeting + dur
            schedule.append((name, loc, start_meeting, end_meeting))
            current_time = end_meeting
            current_loc = loc
        
        if not possible:
            continue
        
        # Now go to William
        travel_to_william = travel[current_loc][people["William"][0]]
        arrival_william = current_time + travel_to_william
        if arrival_william > william_fixed_start:
            # We can try leaving earlier by ending last meeting earlier
            # But simpler: shift last meeting earlier if possible
            # For brute force, we can allow waiting before William if we arrive early
            # Actually we must arrive exactly at or before 18:30
            if arrival_william > william_fixed_start:
                continue  # late for William
        # If we arrive earlier, we wait until 18:30
        schedule.append(("William", people["William"][0], william_fixed_start, william_fixed_end))
        
        # If we get here, we met all 4
        best_schedule = schedule
        best_count = 4
        break  # found a valid schedule meeting all
    
    # If not all 4, try subsets, but we know all 4 is possible
    
    # Convert to required JSON format
    itinerary = []
    for name, loc_idx, start_m, end_m in best_schedule:
        itinerary.append({
            "action": "meet",
            "location": index_to_loc[loc_idx],
            "person": name,
            "start_time": min_to_time(start_m),
            "end_time": min_to_time(end_m)
        })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()