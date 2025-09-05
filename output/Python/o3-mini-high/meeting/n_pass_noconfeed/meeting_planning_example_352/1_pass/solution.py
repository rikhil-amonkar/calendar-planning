import itertools
import json

def time_to_minutes(t):
    # Convert a "H:MM" time string to minutes since midnight.
    parts = t.split(":")
    hour = int(parts[0])
    minute = int(parts[1])
    return hour * 60 + minute

def minutes_to_time(m):
    # Convert minutes since midnight to a "H:MM" time string (24‐hour format, no leading zero for hours).
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

def main():
    # Define travel times (in minutes) between locations.
    travel_times = {
        ("Union Square", "Nob Hill"): 9,
        ("Union Square", "Haight-Ashbury"): 18,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Marina District"): 18,
        ("Nob Hill", "Union Square"): 7,
        ("Nob Hill", "Haight-Ashbury"): 13,
        ("Nob Hill", "Chinatown"): 6,
        ("Nob Hill", "Marina District"): 11,
        ("Haight-Ashbury", "Union Square"): 17,
        ("Haight-Ashbury", "Nob Hill"): 15,
        ("Haight-Ashbury", "Chinatown"): 19,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Chinatown", "Union Square"): 7,
        ("Chinatown", "Nob Hill"): 8,
        ("Chinatown", "Haight-Ashbury"): 19,
        ("Chinatown", "Marina District"): 12,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Chinatown"): 16
    }
    
    # Meeting constraints for each friend.
    # Each friend has a location, an available time window, and a minimum meeting duration.
    meetings = {
        "Karen": {
            "location": "Nob Hill",
            "avail_start": time_to_minutes("21:15"),
            "avail_end": time_to_minutes("21:45"),
            "duration": 30
        },
        "Joseph": {
            "location": "Haight-Ashbury",
            "avail_start": time_to_minutes("12:30"),
            "avail_end": time_to_minutes("19:45"),
            "duration": 90
        },
        "Sandra": {
            "location": "Chinatown",
            "avail_start": time_to_minutes("7:15"),
            "avail_end": time_to_minutes("19:15"),
            "duration": 75
        },
        "Nancy": {
            "location": "Marina District",
            "avail_start": time_to_minutes("11:00"),
            "avail_end": time_to_minutes("20:15"),
            "duration": 105
        }
    }
    
    # List of friends to consider.
    friends = list(meetings.keys())
    
    # The day starts at Union Square at 9:00 AM.
    start_time = time_to_minutes("9:00")
    start_location = "Union Square"
    
    best_schedule = None
    best_meetings_count = 0
    best_idle_time = None
    best_finish_time = None

    # Try all possible orders (permutations) of meeting friends.
    # The simulation will incorporate travel times, waiting if arriving early, and meeting duration.
    for perm in itertools.permutations(friends):
        curr_time = start_time
        curr_location = start_location
        itinerary = []
        total_idle = 0
        feasible = True
        
        # Simulate the schedule for the current permutation.
        for friend in perm:
            friend_data = meetings[friend]
            destination = friend_data["location"]
            
            # Get the travel time from the current location to the friend's location.
            if (curr_location, destination) not in travel_times:
                feasible = False
                break
            travel = travel_times[(curr_location, destination)]
            arrival = curr_time + travel
            
            # The meeting can only start when the friend is available.
            meeting_start = max(arrival, friend_data["avail_start"])
            wait_time = meeting_start - arrival
            total_idle += wait_time
            
            meeting_end = meeting_start + friend_data["duration"]
            # Check if the meeting can be completed within the friend's available time window.
            if meeting_end > friend_data["avail_end"]:
                feasible = False
                break
            
            # Add this meeting to the itinerary.
            itinerary.append({
                "action": "meet",
                "location": destination,
                "person": friend,
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            })
            
            # Update the current time and location.
            curr_time = meeting_end
            curr_location = destination
        
        # If the schedule was feasible, check if it's better than the current best.
        if feasible:
            meetings_count = len(itinerary)
            finish_time = curr_time
            # Optimize for maximum number of meetings.
            # If tied, choose the schedule with the least total idle waiting time.
            # If still tied, choose the one that finishes earlier.
            if (meetings_count > best_meetings_count or 
                (meetings_count == best_meetings_count and (best_idle_time is None or total_idle < best_idle_time)) or
                (meetings_count == best_meetings_count and total_idle == best_idle_time and finish_time < best_finish_time)):
                best_schedule = itinerary
                best_meetings_count = meetings_count
                best_idle_time = total_idle
                best_finish_time = finish_time

    # Output the result as a JSON-formatted dictionary.
    result = {"itinerary": best_schedule if best_schedule is not None else []}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()