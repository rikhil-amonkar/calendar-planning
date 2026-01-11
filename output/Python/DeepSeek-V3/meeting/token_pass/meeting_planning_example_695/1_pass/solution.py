import json
import itertools
from datetime import datetime, timedelta

def time_to_minutes(t):
    """Convert 'H:MMAM/PM' to minutes since midnight."""
    try:
        dt = datetime.strptime(t.strip(), "%I:%M%p")
    except ValueError:
        # Handle case where AM/PM might be missing or different format
        if "AM" in t or "PM" in t:
            dt = datetime.strptime(t.strip(), "%I:%M%p")
        else:
            # Assume 24-hour format given in problem statement
            h, m = map(int, t.split(":"))
            return h * 60 + m
    return dt.hour * 60 + dt.minute

def minutes_to_time(m):
    """Convert minutes since midnight to 'H:MM' 24-hour format."""
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def main():
    # Travel times matrix (in minutes)
    locations = ["Bayview", "Nob Hill", "Union Square", "Chinatown", "The Castro", "Presidio", "Pacific Heights", "Russian Hill"]
    loc_index = {loc: i for i, loc in enumerate(locations)}
    
    travel_matrix = [
        [0, 20, 17, 18, 20, 31, 23, 23],  # Bayview
        [19, 0, 7, 6, 17, 17, 8, 5],      # Nob Hill
        [15, 9, 0, 7, 19, 24, 15, 13],    # Union Square
        [22, 8, 7, 0, 22, 19, 10, 7],     # Chinatown
        [19, 16, 19, 20, 0, 20, 16, 18],  # The Castro
        [31, 18, 22, 21, 21, 0, 11, 14],  # Presidio
        [22, 8, 12, 11, 16, 11, 0, 7],    # Pacific Heights
        [23, 5, 11, 9, 21, 14, 7, 0]      # Russian Hill
    ]
    
    # Friends data: name, location, window_start, window_end, min_duration (minutes)
    friends = [
        ("Paul", "Nob Hill", "4:15PM", "9:15PM", 60),
        ("Carol", "Union Square", "6:00PM", "8:15PM", 120),
        ("Patricia", "Chinatown", "8:00PM", "9:30PM", 75),
        ("Karen", "The Castro", "5:00PM", "7:00PM", 45),
        ("Nancy", "Presidio", "11:45AM", "10:00PM", 30),
        ("Jeffrey", "Pacific Heights", "8:00PM", "8:45PM", 45),
        ("Matthew", "Russian Hill", "3:45PM", "9:45PM", 75)
    ]
    
    # Convert times to minutes
    friends_min = []
    for name, loc, start, end, dur in friends:
        friends_min.append((
            name,
            loc,
            time_to_minutes(start),
            time_to_minutes(end),
            dur
        ))
    
    # Start at Bayview at 9:00 AM
    start_time = time_to_minutes("9:00AM")
    current_loc = "Bayview"
    
    best_count = 0
    best_schedule = []
    best_finish = float('inf')
    
    # Try all permutations of friends
    for perm in itertools.permutations(range(len(friends))):
        current_time = start_time
        current_loc_index = loc_index["Bayview"]
        met_count = 0
        schedule = []
        feasible = True
        
        for idx in perm:
            name, loc, win_start, win_end, min_dur = friends_min[idx]
            loc_idx = loc_index[loc]
            travel = travel_matrix[current_loc_index][loc_idx]
            arrive_time = current_time + travel
            
            # Can we meet this friend?
            # We must start meeting by win_end - min_dur at latest
            latest_start = win_end - min_dur
            if arrive_time > latest_start:
                feasible = False
                break
            
            # Start time is max(arrive_time, win_start)
            meet_start = max(arrive_time, win_start)
            meet_end = meet_start + min_dur
            if meet_end > win_end:
                feasible = False
                break
            
            # Record meeting
            schedule.append((name, loc, meet_start, meet_end))
            met_count += 1
            
            # Update for next
            current_time = meet_end
            current_loc_index = loc_idx
        
        if feasible:
            if met_count > best_count or (met_count == best_count and current_time < best_finish):
                best_count = met_count
                best_schedule = schedule
                best_finish = current_time
    
    # Convert best_schedule to required JSON format
    itinerary = []
    for name, loc, start_m, end_m in best_schedule:
        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": name,
            "start_time": minutes_to_time(start_m),
            "end_time": minutes_to_time(end_m)
        })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()