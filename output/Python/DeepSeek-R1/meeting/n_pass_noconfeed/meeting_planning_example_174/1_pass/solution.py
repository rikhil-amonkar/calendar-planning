import json
from itertools import permutations

def format_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def main():
    # Define start location and time
    start_location = "Nob Hill"
    start_time_minutes = 9 * 60  # 9:00 AM in minutes

    # Define friends with their constraints
    friends = [
        {
            "name": "Kenneth",
            "location": "Mission District",
            "start_avail": 12 * 60,      # 12:00
            "end_avail": 15 * 60 + 45,   # 15:45
            "duration": 45
        },
        {
            "name": "Thomas",
            "location": "Pacific Heights",
            "start_avail": 15 * 60 + 30, # 15:30
            "end_avail": 19 * 60 + 15,   # 19:15
            "duration": 75
        }
    ]

    # Define travel matrix with given travel times
    travel_matrix = {
        ("Nob Hill", "Pacific Heights"): 8,
        ("Nob Hill", "Mission District"): 13,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "Mission District"): 15,
        ("Mission District", "Nob Hill"): 12,
        ("Mission District", "Pacific Heights"): 16
    }

    # Initialize variables to track the best itinerary
    best_itinerary = []
    best_count = 0
    best_end_time = float('inf')

    # Generate all permutations of friends to consider different orders
    for order in permutations(friends):
        current_loc = start_location
        current_time = start_time_minutes
        itinerary = []
        
        for friend in order:
            # Get travel time from current location to friend's location
            travel_key = (current_loc, friend["location"])
            if travel_key not in travel_matrix:
                continue  # Skip if travel time not defined
            travel_duration = travel_matrix[travel_key]
            
            # Calculate arrival time at friend's location
            arrival_time = current_time + travel_duration
            # Determine meeting start time (cannot start before friend is available)
            meeting_start = max(arrival_time, friend["start_avail"])
            meeting_end = meeting_start + friend["duration"]
            
            # Check if meeting fits within friend's availability
            if meeting_end <= friend["end_avail"]:
                # Add meeting to itinerary
                itinerary.append({
                    "action": "meet",
                    "location": friend["location"],
                    "person": friend["name"],
                    "start_time": format_time(meeting_start),
                    "end_time": format_time(meeting_end)
                })
                # Update current location and time after the meeting
                current_loc = friend["location"]
                current_time = meeting_end
        
        # Evaluate this itinerary
        count = len(itinerary)
        end_time = current_time if count > 0 else float('inf')
        
        # Update best itinerary if this one schedules more meetings or finishes earlier in case of tie
        if count > best_count or (count == best_count and end_time < best_end_time):
            best_count = count
            best_end_time = end_time
            best_itinerary = itinerary

    # Output the best itinerary as JSON
    result = {"itinerary": best_itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()