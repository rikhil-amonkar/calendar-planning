import json
import copy

# Helper functions to convert time formats
def time_to_minutes(t):
    # t is a string in format "H:MM" (24-hour)
    parts = t.split(":")
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Travel times (in minutes) between locations as provided.
# Note: These values are directional and may not be symmetric.
travel_times = {
    ("Union Square", "The Castro"): 17,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Haight-Ashbury"): 18,

    ("The Castro", "Union Square"): 19,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Haight-Ashbury"): 6,

    ("North Beach", "Union Square"): 7,
    ("North Beach", "The Castro"): 23,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Mission District"): 18,
    ("North Beach", "Haight-Ashbury"): 18,

    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Mission District"): 20,
    ("Embarcadero", "Haight-Ashbury"): 21,

    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Haight-Ashbury"): 5,

    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Haight-Ashbury"): 13,

    ("Presidio", "Union Square"): 22,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Haight-Ashbury"): 15,

    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "The Castro"): 27,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,

    ("Mission District", "Union Square"): 15,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Embarcadero"): 19,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Haight-Ashbury"): 12,

    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Mission District"): 11,
}

# Meeting constraints as provided.
# Each meeting has: person, location, available start, available end, and minimum meeting duration (in minutes)
meetings = [
    {
        "person": "Melissa",
        "location": "The Castro",
        "available_start": time_to_minutes("20:15"),
        "available_end": time_to_minutes("21:15"),
        "duration": 30
    },
    {
        "person": "Kimberly",
        "location": "North Beach",
        "available_start": time_to_minutes("7:00"),
        "available_end": time_to_minutes("10:30"),
        "duration": 15
    },
    {
        "person": "Joseph",
        "location": "Embarcadero",
        "available_start": time_to_minutes("15:30"),
        "available_end": time_to_minutes("19:30"),
        "duration": 75
    },
    {
        "person": "Barbara",
        "location": "Alamo Square",
        "available_start": time_to_minutes("20:45"),
        "available_end": time_to_minutes("21:45"),
        "duration": 15
    },
    {
        "person": "Kenneth",
        "location": "Nob Hill",
        "available_start": time_to_minutes("12:15"),
        "available_end": time_to_minutes("17:15"),
        "duration": 105
    },
    {
        "person": "Joshua",
        "location": "Presidio",
        "available_start": time_to_minutes("16:30"),
        "available_end": time_to_minutes("18:15"),
        "duration": 105
    },
    {
        "person": "Brian",
        "location": "Fisherman's Wharf",
        "available_start": time_to_minutes("9:30"),
        "available_end": time_to_minutes("15:30"),
        "duration": 45
    },
    {
        "person": "Steven",
        "location": "Mission District",
        "available_start": time_to_minutes("19:30"),
        "available_end": time_to_minutes("21:00"),
        "duration": 90
    },
    {
        "person": "Betty",
        "location": "Haight-Ashbury",
        "available_start": time_to_minutes("19:00"),
        "available_end": time_to_minutes("20:30"),
        "duration": 90
    }
]

# Global variable to hold the best (maximum number of meetings) itinerary found.
best_itinerary = []

def search(current_location, current_time, remaining_meetings, current_itinerary):
    global best_itinerary

    # Update best itinerary if current one has more meetings.
    if len(current_itinerary) > len(best_itinerary):
        best_itinerary = current_itinerary[:]
    
    # Try scheduling each meeting from the remaining ones.
    for i, meet in enumerate(remaining_meetings):
        # Check if travel time exists between current location and meeting location.
        if (current_location, meet["location"]) not in travel_times:
            continue
        travel = travel_times[(current_location, meet["location"])]
        arrival_time = current_time + travel

        # The meeting can only start at or after the arrival time and the meeting's availability start.
        meeting_start = max(arrival_time, meet["available_start"])
        meeting_end = meeting_start + meet["duration"]

        # Check if the meeting can be completed within the available window.
        if meeting_end <= meet["available_end"]:
            # Create an itinerary entry for this meeting.
            itinerary_entry = {
                "action": "meet",
                "location": meet["location"],
                "person": meet["person"],
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            }
            new_itinerary = current_itinerary + [itinerary_entry]
            # Create a new list of remaining meetings (without the current one).
            new_remaining = remaining_meetings[:i] + remaining_meetings[i+1:]
            # Recursively search from the new state.
            search(meet["location"], meeting_end, new_remaining, new_itinerary)

# Starting point: Arrive at Union Square at 9:00 AM.
start_location = "Union Square"
start_time = time_to_minutes("9:00")

# Begin the recursive search with all meetings available.
search(start_location, start_time, meetings, [])

# Prepare the result dictionary
result = {
    "itinerary": best_itinerary
}

# Output the result as JSON
print(json.dumps(result, indent=2))