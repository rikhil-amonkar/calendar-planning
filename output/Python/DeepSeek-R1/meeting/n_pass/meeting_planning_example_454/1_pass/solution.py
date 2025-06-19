import itertools
import json

def main():
    # Convert time string to minutes since midnight
    def time_to_min(time_str):
        parts = time_str.split(':')
        hour = int(parts[0])
        minute = int(parts[1]) if len(parts) > 1 else 0
        return hour * 60 + minute

    # Convert minutes back to "H:MM" format
    def min_to_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h}:{m:02d}"

    # Build travel time matrix
    travel_times = {
        "Presidio": {
            "Golden Gate Park": 12,
            "Bayview": 31,
            "Chinatown": 21,
            "North Beach": 18,
            "Mission District": 26
        },
        "Golden Gate Park": {
            "Presidio": 11,
            "Bayview": 23,
            "Chinatown": 23,
            "North Beach": 24,
            "Mission District": 17
        },
        "Bayview": {
            "Presidio": 31,
            "Golden Gate Park": 22,
            "Chinatown": 18,
            "North Beach": 21,
            "Mission District": 13
        },
        "Chinatown": {
            "Presidio": 19,
            "Golden Gate Park": 23,
            "Bayview": 22,
            "North Beach": 3,
            "Mission District": 18
        },
        "North Beach": {
            "Presidio": 17,
            "Golden Gate Park": 22,
            "Bayview": 22,
            "Chinatown": 6,
            "Mission District": 17
        },
        "Mission District": {
            "Presidio": 25,
            "Golden Gate Park": 17,
            "Bayview": 15,
            "Chinatown": 16,
            "North Beach": 17
        }
    }

    # Define friends with their constraints (converted to minutes)
    friends = [
        {"name": "Jessica", "location": "Golden Gate Park", "start_avail": time_to_min("13:45"), "end_avail": time_to_min("15:00"), "min_duration": 30},
        {"name": "Ashley", "location": "Bayview", "start_avail": time_to_min("17:15"), "end_avail": time_to_min("20:00"), "min_duration": 105},
        {"name": "Ronald", "location": "Chinatown", "start_avail": time_to_min("7:15"), "end_avail": time_to_min("14:45"), "min_duration": 90},
        {"name": "William", "location": "North Beach", "start_avail": time_to_min("13:15"), "end_avail": time_to_min("20:15"), "min_duration": 15},
        {"name": "Daniel", "location": "Mission District", "start_avail": time_to_min("7:00"), "end_avail": time_to_min("11:15"), "min_duration": 105}
    ]

    # Start time at Presidio: 9:00 AM
    start_time = time_to_min("9:00")
    start_location = "Presidio"
    
    # Try to meet as many friends as possible, starting from 5 down to 1
    best_schedule = None
    max_count = 0
    found = False
    n = len(friends)
    
    # We'll iterate from largest subset (5) down to 1
    for size in range(n, 0, -1):
        for subset in itertools.combinations(friends, size):
            for perm in itertools.permutations(subset):
                current_time = start_time
                current_loc = start_location
                schedule = []
                feasible = True
                
                for friend in perm:
                    # Get travel time to friend's location
                    travel = travel_times[current_loc][friend["location"]]
                    current_time += travel
                    
                    # Determine meeting start time (max of arrival and friend's availability start)
                    meeting_start = max(current_time, friend["start_avail"])
                    # If we arrive after the friend's availability ends, not feasible
                    if meeting_start > friend["end_avail"]:
                        feasible = False
                        break
                    
                    meeting_end = meeting_start + friend["min_duration"]
                    # If meeting duration exceeds friend's availability end, not feasible
                    if meeting_end > friend["end_avail"]:
                        feasible = False
                        break
                    
                    # Record meeting details
                    schedule.append({
                        "friend": friend,
                        "start": meeting_start,
                        "end": meeting_end
                    })
                    
                    # Update current time and location after meeting
                    current_time = meeting_end
                    current_loc = friend["location"]
                
                if feasible:
                    best_schedule = schedule
                    max_count = size
                    found = True
                    break  # break out of permutation loop
            if found:
                break  # break out of subset loop
        if found:
            break  # break out of size loop
    
    # Prepare the itinerary for output
    itinerary = []
    if best_schedule:
        for meeting in best_schedule:
            friend = meeting["friend"]
            itinerary.append({
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": min_to_time(meeting["start"]),
                "end_time": min_to_time(meeting["end"])
            })
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()