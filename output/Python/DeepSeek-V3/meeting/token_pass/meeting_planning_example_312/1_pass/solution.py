import json
from itertools import permutations

def time_to_minutes(t):
    """Convert 'H:MM' string to minutes since midnight."""
    hours, minutes = map(int, t.split(':'))
    return hours * 60 + minutes

def minutes_to_time(m):
    """Convert minutes since midnight to 'H:MM' string."""
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

def main():
    # Travel times matrix: from_index to to_index in minutes
    # Indices: 0=Richmond, 1=Sunset, 2=Haight-Ashbury, 3=Mission, 4=Golden Gate Park
    travel_times = [
        [0, 11, 10, 20, 9],   # from Richmond
        [12, 0, 15, 24, 11],  # from Sunset
        [10, 15, 0, 11, 7],   # from Haight-Ashbury
        [20, 24, 12, 0, 17],  # from Mission
        [7, 10, 7, 17, 0]     # from Golden Gate Park
    ]
    
    location_names = ["Richmond District", "Sunset District", "Haight-Ashbury", "Mission District", "Golden Gate Park"]
    
    # Friend data: name, location index, window start, window end, min duration (minutes)
    friends = [
        ("Sarah", 1, time_to_minutes("10:45"), time_to_minutes("19:00"), 30),
        ("Richard", 2, time_to_minutes("11:45"), time_to_minutes("15:45"), 90),
        ("Elizabeth", 3, time_to_minutes("11:00"), time_to_minutes("17:15"), 120),
        ("Michelle", 4, time_to_minutes("18:15"), time_to_minutes("20:45"), 90)
    ]
    
    start_location = 0  # Richmond
    start_time = time_to_minutes("9:00")
    
    best_schedule = []
    max_meetings = 0
    
    # Try all permutations of friends to find feasible schedule
    for perm in permutations(range(len(friends))):
        current_location = start_location
        current_time = start_time
        schedule = []
        
        for idx in perm:
            name, loc, win_start, win_end, min_dur = friends[idx]
            
            # Travel to friend's location
            travel = travel_times[current_location][loc]
            arrival = current_time + travel
            
            # If we arrive before window start, wait
            if arrival < win_start:
                arrival = win_start
            
            # Check if we can meet before window ends
            if arrival + min_dur > win_end:
                break  # cannot meet this friend in this permutation
            
            # Schedule meeting
            meeting_end = arrival + min_dur
            schedule.append((name, loc, arrival, meeting_end))
            
            # Update current location and time
            current_location = loc
            current_time = meeting_end
        
        # If we scheduled all 4 friends, that's optimal
        if len(schedule) == 4:
            best_schedule = schedule
            break
        elif len(schedule) > max_meetings:
            max_meetings = len(schedule)
            best_schedule = schedule
    
    # Build itinerary in required format
    itinerary = []
    for name, loc, start_m, end_m in best_schedule:
        itinerary.append({
            "action": "meet",
            "location": location_names[loc],
            "person": name,
            "start_time": minutes_to_time(start_m),
            "end_time": minutes_to_time(end_m)
        })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()