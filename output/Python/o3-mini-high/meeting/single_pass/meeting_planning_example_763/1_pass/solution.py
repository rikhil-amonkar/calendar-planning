#!/usr/bin/env python3
import json

def minutes_to_time_str(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Define meeting constraints for each friend.
# Times are stored as minutes from midnight.
friends = [
    {"name": "Richard", "location": "Embarcadero", "window_start": 15*60+15, "window_end": 18*60+45, "duration": 90},
    {"name": "Mark", "location": "Pacific Heights", "window_start": 15*60, "window_end": 17*60, "duration": 45},
    {"name": "Matthew", "location": "Russian Hill", "window_start": 17*60+30, "window_end": 21*60, "duration": 90},
    {"name": "Rebecca", "location": "Haight-Ashbury", "window_start": 14*60+45, "window_end": 18*60, "duration": 60},
    {"name": "Melissa", "location": "Golden Gate Park", "window_start": 13*60+45, "window_end": 17*60+30, "duration": 90},
    {"name": "Margaret", "location": "Fisherman's Wharf", "window_start": 14*60+45, "window_end": 20*60+15, "duration": 15},
    {"name": "Emily", "location": "Sunset District", "window_start": 15*60+45, "window_end": 17*60, "duration": 45},
    {"name": "George", "location": "The Castro", "window_start": 14*60, "window_end": 16*60+15, "duration": 75}
]

# Define directed travel times (in minutes) between locations.
# Note: travel times are not necessarily symmetric.
travel_times = {
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "The Castro"): 22,
    
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Pacific Heights"): 11,
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "The Castro"): 25,
    
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Embarcadero"): 10,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "The Castro"): 16,
    
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "The Castro"): 21,
    
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "The Castro"): 6,
    
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "The Castro"): 13,
    
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Fisherman's Wharf", "The Castro"): 27,
    
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Embarcadero"): 30,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "The Castro"): 17,
    
    ("The Castro", "Chinatown"): 22,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Sunset District"): 17
}

# Global variable to track the best solution found.
# The best solution is determined by the maximum number of meetings.
# In case of a tie, the schedule with the earliest finishing time is preferred.
best_solution = {"count": 0, "itinerary": [], "finish_time": float('inf')}

def dfs(current_time, current_location, remaining_friends, current_itinerary):
    global best_solution
    # Update best solution if the current itinerary is better
    if (len(current_itinerary) > best_solution["count"]) or (len(current_itinerary) == best_solution["count"] and current_time < best_solution["finish_time"]):
        best_solution["count"] = len(current_itinerary)
        best_solution["itinerary"] = current_itinerary
        best_solution["finish_time"] = current_time

    # Try to schedule each remaining friend next
    for index, friend in enumerate(remaining_friends):
        # Check if there is a defined travel time from current location to friend's location.
        if (current_location, friend["location"]) not in travel_times:
            continue
        travel_time = travel_times[(current_location, friend["location"])]
        arrival_time = current_time + travel_time
        # The meeting can only start when the friend is available
        meeting_start = max(arrival_time, friend["window_start"])
        meeting_end = meeting_start + friend["duration"]

        # Verify if the meeting can be completed within the friend’s available window.
        if meeting_end <= friend["window_end"]:
            meeting_event = {
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": minutes_to_time_str(meeting_start),
                "end_time": minutes_to_time_str(meeting_end)
            }
            new_itinerary = current_itinerary + [meeting_event]
            # Remove the scheduled friend and continue exploring
            new_remaining = remaining_friends[:index] + remaining_friends[index+1:]
            dfs(meeting_end, friend["location"], new_remaining, new_itinerary)

if __name__ == '__main__':
    # Start at Chinatown at 9:00 AM (9*60 minutes)
    start_time = 9 * 60
    start_location = "Chinatown"
    
    dfs(start_time, start_location, friends, [])
    
    result = {"itinerary": best_solution["itinerary"]}
    print(json.dumps(result, indent=2))