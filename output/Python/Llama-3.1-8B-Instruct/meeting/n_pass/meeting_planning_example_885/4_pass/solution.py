import json
from datetime import datetime, timedelta

# Define travel distances and times
travel_distances = {
    "Russian Hill": {
        "Marina District": 7,
        "Financial District": 11,
        "Alamo Square": 15,
        "Golden Gate Park": 21,
        "The Castro": 21,
        "Bayview": 23,
        "Sunset District": 23,
        "Haight-Ashbury": 17,
        "Nob Hill": 5
    },
    "Marina District": {
        "Russian Hill": 8,
        "Financial District": 17,
        "Alamo Square": 15,
        "Golden Gate Park": 18,
        "The Castro": 22,
        "Bayview": 27,
        "Sunset District": 19,
        "Haight-Ashbury": 16,
        "Nob Hill": 12
    },
    "Financial District": {
        "Russian Hill": 11,
        "Marina District": 15,
        "Alamo Square": 17,
        "Golden Gate Park": 23,
        "The Castro": 20,
        "Bayview": 19,
        "Sunset District": 30,
        "Haight-Ashbury": 19,
        "Nob Hill": 8
    },
    "Alamo Square": {
        "Russian Hill": 13,
        "Marina District": 15,
        "Financial District": 17,
        "Golden Gate Park": 9,
        "The Castro": 8,
        "Bayview": 16,
        "Sunset District": 16,
        "Haight-Ashbury": 5,
        "Nob Hill": 11
    },
    "Golden Gate Park": {
        "Russian Hill": 19,
        "Marina District": 16,
        "Financial District": 26,
        "Alamo Square": 9,
        "The Castro": 13,
        "Bayview": 23,
        "Sunset District": 10,
        "Haight-Ashbury": 7,
        "Nob Hill": 20
    },
    "The Castro": {
        "Russian Hill": 18,
        "Marina District": 21,
        "Financial District": 21,
        "Alamo Square": 8,
        "Golden Gate Park": 11,
        "Bayview": 19,
        "Sunset District": 17,
        "Haight-Ashbury": 6,
        "Nob Hill": 16
    },
    "Bayview": {
        "Russian Hill": 23,
        "Marina District": 27,
        "Financial District": 19,
        "Alamo Square": 16,
        "Golden Gate Park": 22,
        "The Castro": 19,
        "Sunset District": 23,
        "Haight-Ashbury": 19,
        "Nob Hill": 20
    },
    "Sunset District": {
        "Russian Hill": 24,
        "Marina District": 21,
        "Financial District": 30,
        "Alamo Square": 17,
        "Golden Gate Park": 11,
        "The Castro": 17,
        "Bayview": 22,
        "Haight-Ashbury": 15,
        "Nob Hill": 27
    },
    "Haight-Ashbury": {
        "Russian Hill": 17,
        "Marina District": 17,
        "Financial District": 21,
        "Alamo Square": 5,
        "Golden Gate Park": 7,
        "The Castro": 6,
        "Bayview": 18,
        "Sunset District": 15,
        "Nob Hill": 15
    },
    "Nob Hill": {
        "Russian Hill": 5,
        "Marina District": 11,
        "Financial District": 9,
        "Alamo Square": 11,
        "Golden Gate Park": 17,
        "The Castro": 17,
        "Bayview": 19,
        "Sunset District": 24,
        "Haight-Ashbury": 13
    }
}

# Define meeting constraints
constraints = {
    "Mark": {"start_time": "18:45", "end_time": "21:00", "location": "The Castro", "duration": 90},
    "Karen": {"start_time": "09:30", "end_time": "12:45", "location": "Marina District", "duration": 90},
    "Barbara": {"start_time": "10:00", "end_time": "19:30", "location": "Alamo Square", "duration": 90},
    "Nancy": {"start_time": "16:45", "end_time": "20:00", "location": "The Castro", "duration": 105},
    "David": {"start_time": "09:00", "end_time": "18:00", "location": "Financial District", "duration": 120},
    "Linda": {"start_time": "18:15", "end_time": "19:45", "location": "The Castro", "duration": 45},
    "Kevin": {"start_time": "10:00", "end_time": "17:45", "location": "Alamo Square", "duration": 120},
    "Matthew": {"start_time": "10:15", "end_time": "15:30", "location": "Haight-Ashbury", "duration": 45},
    "Andrew": {"start_time": "11:45", "end_time": "16:45", "location": "Financial District", "duration": 105}
}

# Initialize schedule
schedule = []

# Start at Russian Hill at 09:00
current_location = "Russian Hill"
current_time = datetime.strptime("09:00", "%H:%M")

# Iterate over constraints
for person, constraint in constraints.items():
    start_time = datetime.strptime(constraint["start_time"], "%H:%M")
    end_time = datetime.strptime(constraint["end_time"], "%H:%M")
    duration = constraint["duration"]
    location = constraint["location"]

    # Check if person is available
    if start_time <= current_time:
        # Calculate travel time
        travel_time = travel_distances[current_location][location]
        travel_time = timedelta(minutes=travel_time)

        # Calculate meeting start time
        meeting_start_time = current_time + travel_time

        # Check if meeting fits in schedule
        if meeting_start_time + timedelta(minutes=duration) <= end_time:
            # Check if meeting time falls within person's available time
            if meeting_start_time >= start_time and meeting_start_time + timedelta(minutes=duration) <= end_time:
                # Add meeting to schedule
                schedule.append({
                    "action": "meet",
                    "location": location,
                    "person": person,
                    "start_time": meeting_start_time.strftime("%H:%M"),
                    "end_time": (meeting_start_time + timedelta(minutes=duration)).strftime("%H:%M")
                })

                # Update current time and location
                current_time = meeting_start_time + timedelta(minutes=duration)
                current_location = location

# Print schedule as JSON
print(json.dumps({"itinerary": schedule}, indent=4))