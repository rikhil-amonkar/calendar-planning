import json
from datetime import datetime, timedelta

# Define travel times as a dictionary of dictionaries
travel_times = {
    "Marina District": {"Bayview": 27, "Sunset District": 19, "Richmond District": 11, "Nob Hill": 12, "Chinatown": 15, "Haight-Ashbury": 16, "North Beach": 11, "Russian Hill": 8, "Embarcadero": 14},
    "Bayview": {"Marina District": 27, "Sunset District": 23, "Richmond District": 25, "Nob Hill": 20, "Chinatown": 19, "Haight-Ashbury": 19, "North Beach": 22, "Russian Hill": 23, "Embarcadero": 19},
    "Sunset District": {"Marina District": 21, "Bayview": 22, "Richmond District": 12, "Nob Hill": 27, "Chinatown": 30, "Haight-Ashbury": 15, "North Beach": 28, "Russian Hill": 24, "Embarcadero": 30},
    "Richmond District": {"Marina District": 9, "Bayview": 27, "Sunset District": 11, "Nob Hill": 17, "Chinatown": 20, "Haight-Ashbury": 10, "North Beach": 17, "Russian Hill": 13, "Embarcadero": 19},
    "Nob Hill": {"Marina District": 11, "Bayview": 19, "Sunset District": 24, "Richmond District": 14, "Chinatown": 6, "Haight-Ashbury": 13, "North Beach": 8, "Russian Hill": 5, "Embarcadero": 9},
    "Chinatown": {"Marina District": 12, "Bayview": 20, "Sunset District": 29, "Richmond District": 20, "Nob Hill": 9, "Haight-Ashbury": 19, "North Beach": 3, "Russian Hill": 7, "Embarcadero": 5},
    "Haight-Ashbury": {"Marina District": 17, "Bayview": 18, "Sunset District": 15, "Richmond District": 10, "Nob Hill": 15, "Chinatown": 19, "North Beach": 19, "Russian Hill": 17, "Embarcadero": 20},
    "North Beach": {"Marina District": 9, "Bayview": 25, "Sunset District": 27, "Richmond District": 18, "Nob Hill": 7, "Chinatown": 6, "Haight-Ashbury": 18, "Russian Hill": 4, "Embarcadero": 6},
    "Russian Hill": {"Marina District": 7, "Bayview": 23, "Sunset District": 23, "Richmond District": 14, "Nob Hill": 5, "Chinatown": 9, "Haight-Ashbury": 17, "North Beach": 5, "Embarcadero": 8},
    "Embarcadero": {"Marina District": 12, "Bayview": 21, "Sunset District": 30, "Richmond District": 21, "Nob Hill": 10, "Chinatown": 7, "Haight-Ashbury": 21, "North Beach": 5, "Russian Hill": 8}
}

# Define meeting constraints
meetings = {
    "Charles": {"location": "Bayview", "start": "11:30", "end": "14:30", "min_duration": 45},
    "Robert": {"location": "Sunset District", "start": "16:45", "end": "21:00", "min_duration": 30},
    "Karen": {"location": "Richmond District", "start": "19:15", "end": "21:30", "min_duration": 60},
    "Rebecca": {"location": "Nob Hill", "start": "16:15", "end": "20:30", "min_duration": 90},
    "Margaret": {"location": "Chinatown", "start": "14:15", "end": "19:45", "min_duration": 120},
    "Patricia": {"location": "Haight-Ashbury", "start": "14:30", "end": "20:30", "min_duration": 45},
    "Mark": {"location": "North Beach", "start": "14:00", "end": "18:30", "min_duration": 105},
    "Melissa": {"location": "Russian Hill", "start": "13:00", "end": "19:45", "min_duration": 30},
    "Laura": {"location": "Embarcadero", "start": "07:45", "end": "13:15", "min_duration": 105}
}

# Convert times to minutes since midnight
def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

# Convert minutes since midnight to time string
def minutes_to_time(minutes):
    h, m = divmod(minutes, 60)
    return f"{h}:{m:02}"

# Recursive function to find the best itinerary
def find_best_itinerary(current_location, current_time, visited_meetings, current_itinerary):
    global best_itinerary
    
    # Check if the current itinerary is better than the best found so far
    if len(visited_meetings) > len(best_itinerary["itinerary"]):
        best_itinerary["itinerary"] = current_itinerary[:]
    
    # Try to add each meeting to the itinerary
    for person, details in meetings.items():
        if person in visited_meetings:
            continue
        
        meeting_start = time_to_minutes(details["start"])
        meeting_end = time_to_minutes(details["end"])
        min_duration = details["min_duration"]
        
        # Calculate travel time to the meeting location
        travel_time = travel_times[current_location][details["location"]]
        
        # Calculate potential meeting start and end times
        potential_start = max(current_time + travel_time, meeting_start)
        potential_end = potential_start + min_duration
        
        # Check if the meeting fits within the available time
        if potential_end <= meeting_end and potential_end <= time_to_minutes("21:00"):
            # Add the meeting to the current itinerary
            current_itinerary.append({
                "action": "meet",
                "location": details["location"],
                "person": person,
                "start_time": minutes_to_time(potential_start),
                "end_time": minutes_to_time(potential_end)
            })
            
            # Recursively try to add more meetings
            find_best_itinerary(details["location"], potential_end, visited_meetings | {person}, current_itinerary)
            
            # Backtrack: remove the last added meeting
            current_itinerary.pop()

# Initialize the best itinerary
best_itinerary = {"itinerary": []}

# Start the search from Marina District at 9:00 AM
find_best_itinerary("Marina District", time_to_minutes("09:00"), set(), [])

# Output the best itinerary as JSON
print(json.dumps(best_itinerary, indent=2))