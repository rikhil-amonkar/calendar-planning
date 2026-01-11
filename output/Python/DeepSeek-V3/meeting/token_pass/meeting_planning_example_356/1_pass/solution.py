import itertools
import json

def time_to_minutes(t):
    """Convert 'H:MM' string to minutes since midnight."""
    if isinstance(t, str):
        h, m = map(int, t.split(':'))
        return h * 60 + m
    return t

def minutes_to_time(m):
    """Convert minutes since midnight to 'H:MM' string."""
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

def add_time(t, delta_minutes):
    """Add minutes to a time string, return time string."""
    return minutes_to_time(time_to_minutes(t) + delta_minutes)

def main():
    # Travel times matrix (in minutes)
    locations = ["Bayview", "North Beach", "Presidio", "Haight-Ashbury", "Union Square"]
    loc_index = {loc: i for i, loc in enumerate(locations)}
    
    travel = [
        [0, 21, 31, 19, 17],   # Bayview
        [22, 0, 17, 18, 7],    # North Beach
        [31, 18, 0, 15, 22],   # Presidio
        [18, 19, 15, 0, 17],   # Haight-Ashbury
        [15, 10, 24, 18, 0]    # Union Square
    ]
    
    friends = [
        {"name": "Barbara", "location": "North Beach", "start": "13:45", "end": "20:15", "min_duration": 60},
        {"name": "Margaret", "location": "Presidio", "start": "10:15", "end": "15:15", "min_duration": 30},
        {"name": "Kevin", "location": "Haight-Ashbury", "start": "20:00", "end": "20:45", "min_duration": 30},
        {"name": "Kimberly", "location": "Union Square", "start": "7:45", "end": "16:45", "min_duration": 30}
    ]
    
    # Start at Bayview at 9:00 AM
    current_time = time_to_minutes("9:00")
    current_loc = "Bayview"
    
    best_schedule = []
    max_met = 0
    
    # Try all permutations of friends (order of meeting)
    for perm in itertools.permutations(range(len(friends))):
        schedule = []
        cur_time = current_time
        cur_loc = current_loc
        met_count = 0
        
        for idx in perm:
            f = friends[idx]
            loc = f["location"]
            travel_time = travel[loc_index[cur_loc]][loc_index[loc]]
            arrive_time = cur_time + travel_time
            
            # Check if we can meet within friend's window
            window_start = time_to_minutes(f["start"])
            window_end = time_to_minutes(f["end"])
            min_dur = f["min_duration"]
            
            # If arrive before window starts, wait
            start_meeting = max(arrive_time, window_start)
            end_meeting = start_meeting + min_dur
            
            if end_meeting <= window_end:
                # Meeting possible
                schedule.append({
                    "action": "meet",
                    "location": loc,
                    "person": f["name"],
                    "start_time": minutes_to_time(start_meeting),
                    "end_time": minutes_to_time(end_meeting)
                })
                met_count += 1
                cur_time = end_meeting
                cur_loc = loc
            else:
                # Cannot meet this friend in this order, skip them
                break
        
        if met_count > max_met:
            max_met = met_count
            best_schedule = schedule
    
    # Output result
    result = {
        "itinerary": best_schedule
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()