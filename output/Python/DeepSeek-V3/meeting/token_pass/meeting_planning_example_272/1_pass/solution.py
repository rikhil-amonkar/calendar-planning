import json
from itertools import permutations

def time_to_min(t):
    """Convert 'H:MM' string to minutes since midnight."""
    h, m = map(int, t.split(':'))
    return h * 60 + m

def min_to_time(m):
    """Convert minutes since midnight to 'H:MM' string."""
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

def main():
    # Travel times matrix
    locations = ["Russian Hill", "Nob Hill", "Mission District", "Embarcadero"]
    loc_index = {loc: i for i, loc in enumerate(locations)}
    travel = [
        [0, 5, 16, 8],
        [5, 0, 13, 9],
        [15, 12, 0, 19],
        [8, 10, 20, 0]
    ]
    
    # Friend data: name, location, window start, window end, min duration
    friends = [
        ("Patricia", "Nob Hill", time_to_min("18:30"), time_to_min("21:45"), 90),
        ("Ashley", "Mission District", time_to_min("20:30"), time_to_min("21:15"), 45),
        ("Timothy", "Embarcadero", time_to_min("9:45"), time_to_min("17:45"), 120)
    ]
    
    start_loc = "Russian Hill"
    start_time = time_to_min("9:00")
    
    best_schedule = []
    best_count = 0
    
    # Try all permutations of friends
    for perm in permutations(friends):
        current_time = start_time
        current_loc = start_loc
        schedule = []
        for person, loc, win_start, win_end, min_dur in perm:
            # Travel to friend's location
            travel_time = travel[loc_index[current_loc]][loc_index[loc]]
            arrive_time = current_time + travel_time
            
            # Check if we can meet within window
            # Start meeting at max(arrive_time, win_start)
            meet_start = max(arrive_time, win_start)
            if meet_start + min_dur > win_end:
                break  # cannot meet this friend in this order
            
            meet_end = meet_start + min_dur
            schedule.append((person, loc, meet_start, meet_end))
            
            # Update current time and location
            current_time = meet_end
            current_loc = loc
        
        if len(schedule) > best_count:
            best_count = len(schedule)
            best_schedule = schedule
    
    # Convert best schedule to output format
    itinerary = []
    for person, loc, meet_start, meet_end in best_schedule:
        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": person,
            "start_time": min_to_time(meet_start),
            "end_time": min_to_time(meet_end)
        })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()