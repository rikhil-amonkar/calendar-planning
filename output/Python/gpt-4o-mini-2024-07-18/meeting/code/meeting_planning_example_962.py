import json
from datetime import datetime, timedelta

# Input parameters
travel_times = {
    ("The Castro", "Marina District"): 22,
    ("The Castro", "Presidio"): 21,
    ("The Castro", "North Beach"): 23,
    ("The Castro", "Embarcadero"): 25,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Golden Gate Park"): 13,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Financial District"): 20,
    ("The Castro", "Sunset District"): 17,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Embarcadero"): 12,
    ("Marina District", "Haight-Ashbury"): 17,
    ("Marina District", "Golden Gate Park"): 16,
    ("Marina District", "Richmond District"): 9,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Financial District"): 15,
    ("Marina District", "Sunset District"): 21,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Marina District"): 10,
    ("Presidio", "North Beach"): 17,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Golden Gate Park"): 11,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Sunset District"): 15,
    ("North Beach", "The Castro"): 23,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Haight-Ashbury"): 19,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Sunset District"): 27,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "Sunset District"): 30,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Financial District"): 19,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Richmond District"): 9,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Sunset District"): 11,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Sunset District"): 16,
    ("Financial District", "The Castro"): 20,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Sunset District"): 30,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Embarcadero"): 30,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Financial District"): 30,
}

# Meeting constraints
meetings = [
    {"name": "Elizabeth", "location": "Marina District", "available_from": "19:00", "available_to": "20:45", "min_duration": 105},
    {"name": "Joshua", "location": "Presidio", "available_from": "08:30", "available_to": "13:15", "min_duration": 105},
    {"name": "Timothy", "location": "North Beach", "available_from": "19:45", "available_to": "22:00", "min_duration": 90},
    {"name": "David", "location": "Embarcadero", "available_from": "10:45", "available_to": "12:30", "min_duration": 30},
    {"name": "Kimberly", "location": "Haight-Ashbury", "available_from": "16:45", "available_to": "21:30", "min_duration": 75},
    {"name": "Lisa", "location": "Golden Gate Park", "available_from": "17:30", "available_to": "21:45", "min_duration": 45},
    {"name": "Ronald", "location": "Richmond District", "available_from": "08:00", "available_to": "09:30", "min_duration": 90},
    {"name": "Stephanie", "location": "Alamo Square", "available_from": "15:30", "available_to": "16:30", "min_duration": 30},
    {"name": "Helen", "location": "Financial District", "available_from": "17:30", "available_to": "18:30", "min_duration": 45},
    {"name": "Laura", "location": "Sunset District", "available_from": "17:45", "available_to": "21:15", "min_duration": 90},
]

# Function to parse time
def parse_time(t):
    return datetime.strptime(t, "%H:%M")

# Function to compute the meeting schedule
def compute_meeting_schedule():
    itinerary = []
    current_time = parse_time("09:00")
    current_location = "The Castro"

    # Meeting each person as per constraints
    for meeting in meetings:
        start_time = parse_time(meeting["available_from"])
        end_time = parse_time(meeting["available_to"])
        min_duration = timedelta(minutes=meeting["min_duration"])

        # Calculate travel to the meeting location
        travel_time = travel_times[(current_location, meeting["location"])]
        travel_duration = timedelta(minutes=travel_time)

        # Determine the latest possible start time
        latest_start = end_time - min_duration

        # Check if current_time and travel time allows meeting
        if current_time + travel_duration >= start_time and current_time + travel_duration <= latest_start:
            # Start meeting
            meeting_start_time = max(start_time, current_time + travel_duration)
            meeting_end_time = meeting_start_time + min_duration

            itinerary.append({
                "action": "meet",
                "location": meeting["location"],
                "person": meeting["name"],
                "start_time": meeting_start_time.strftime("%H:%M"),
                "end_time": meeting_end_time.strftime("%H:%M"),
            })

            # Update current_time and location
            current_time = meeting_end_time
            current_location = meeting["location"]

        # Handle end point where we need to head back to previous or other meeting points
        if current_time > end_time:  # If we exceed person's end time
            current_time = end_time # Reset current_time for next meetings

    return itinerary

# Generate the optimal meeting schedule
optimal_schedule = compute_meeting_schedule()

# Convert to JSON format
output = {"itinerary": optimal_schedule}
print(json.dumps(output, indent=2))