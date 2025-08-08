#!/usr/bin/env python3
import itertools
import json

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def compute_schedule(order, meetings, travel_times, start_location, start_time):
    itinerary = []
    current_time = start_time
    current_location = start_location
    total_idle = 0
    for person in order:
        meeting = meetings[person]
        location = meeting["location"]
        avail_start = meeting["avail_start"]
        avail_end = meeting["avail_end"]
        duration = meeting["duration"]
        # Get travel time from current location to next meeting location
        if (current_location, location) not in travel_times:
            return None, None  # Infeasible if no travel time available
        travel_time = travel_times[(current_location, location)]
        arrival_time = current_time + travel_time
        meeting_start = max(arrival_time, avail_start)
        idle = meeting_start - arrival_time
        meeting_end = meeting_start + duration
        if meeting_end > avail_end:
            return None, None  # Not feasible within available window
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": person,
            "start_time": meeting_start,  # stored as minutes from midnight
            "end_time": meeting_end
        })
        total_idle += idle
        current_time = meeting_end
        current_location = location
    return itinerary, (current_location, current_time, total_idle)

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
        ("Marina District", "Chinatown"): 16,
    }
    
    # Define meeting constraints.
    # Times are expressed in minutes from midnight.
    meetings = {
        "Karen": {
            "location": "Nob Hill",
            "avail_start": 21 * 60 + 15,  # 21:15 -> 1275
            "avail_end": 21 * 60 + 45,    # 21:45 -> 1305
            "duration": 30
        },
        "Joseph": {
            "location": "Haight-Ashbury",
            "avail_start": 12 * 60 + 30,  # 12:30 -> 750
            "avail_end": 19 * 60 + 45,    # 19:45 -> 1185
            "duration": 90
        },
        "Sandra": {
            "location": "Chinatown",
            "avail_start": 7 * 60 + 15,   # 7:15 -> 435
            "avail_end": 19 * 60 + 15,    # 19:15 -> 1155
            "duration": 75
        },
        "Nancy": {
            "location": "Marina District",
            "avail_start": 11 * 60,       # 11:00 -> 660
            "avail_end": 20 * 60 + 15,    # 20:15 -> 1215
            "duration": 105
        }
    }
    
    # You arrive at Union Square at 9:00 (9*60 = 540 minutes).
    start_location = "Union Square"
    start_time = 9 * 60  # 540 minutes
    
    # Since Karen is only available very late in the day,
    # we assume an optimal full-meeting schedule will schedule her last.
    other_friends = ["Sandra", "Joseph", "Nancy"]
    best_schedule = None
    best_idle = float('inf')
    
    # Try all orders for the other three friends, then append Karen.
    for perm in itertools.permutations(other_friends):
        order = list(perm) + ["Karen"]
        schedule, result = compute_schedule(order, meetings, travel_times, start_location, start_time)
        if schedule is None:
            continue
        _, finish_time, total_idle = result
        # Choose schedule with minimum total idle waiting time
        if total_idle < best_idle:
            best_idle = total_idle
            best_schedule = (order, schedule)
    
    # Convert meeting times from minutes to "H:MM" strings
    if best_schedule is not None:
        final_itinerary = []
        for meeting in best_schedule[1]:
            start_str = minutes_to_time_str(meeting["start_time"])
            end_str = minutes_to_time_str(meeting["end_time"])
            final_itinerary.append({
                "action": "meet",
                "location": meeting["location"],
                "person": meeting["person"],
                "start_time": start_str,
                "end_time": end_str
            })
        output = {"itinerary": final_itinerary}
    else:
        output = {"itinerary": []}
    
    print(json.dumps(output))

if __name__ == "__main__":
    main()