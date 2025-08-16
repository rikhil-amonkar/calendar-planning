import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Golden Gate Park"): 23,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Chinatown"): 23
}

# Define constraints
start_time = datetime.strptime("9:00", "%H:%M")
kenneth_start = datetime.strptime("12:00", "%H:%M")
kenneth_end = datetime.strptime("15:00", "%H:%M")
barbara_start = datetime.strptime("8:15", "%H:%M")
barbara_end = datetime.strptime("19:00", "%H:%M")
kenneth_min_meeting = timedelta(minutes=90)
barbara_min_meeting = timedelta(minutes=45)

# Function to convert datetime to string in H:MM format
def time_to_str(time):
    return time.strftime("%-H:%M")

# Function to find the optimal schedule
def find_optimal_schedule():
    itinerary = []
    current_location = "Financial District"
    current_time = start_time

    # Try to meet Barbara first if possible
    if barbara_start <= current_time + timedelta(minutes=travel_times[(current_location, "Golden Gate Park")]):
        travel_time = travel_times[(current_location, "Golden Gate Park")]
        current_time += timedelta(minutes=travel_time)
        current_location = "Golden Gate Park"
        meeting_start = max(current_time, barbara_start)
        meeting_end = min(meeting_start + barbara_min_meeting, barbara_end)
        if meeting_end - meeting_start >= barbara_min_meeting:
            itinerary.append({
                "action": "meet",
                "location": "Golden Gate Park",
                "person": "Barbara",
                "start_time": time_to_str(meeting_start),
                "end_time": time_to_str(meeting_end)
            })
            current_time = meeting_end

    # Try to meet Kenneth next if possible
    if kenneth_start <= current_time + timedelta(minutes=travel_times[(current_location, "Chinatown")]):
        travel_time = travel_times[(current_location, "Chinatown")]
        current_time += timedelta(minutes=travel_time)
        current_location = "Chinatown"
        meeting_start = max(current_time, kenneth_start)
        meeting_end = min(meeting_start + kenneth_min_meeting, kenneth_end)
        if meeting_end - meeting_start >= kenneth_min_meeting:
            itinerary.append({
                "action": "meet",
                "location": "Chinatown",
                "person": "Kenneth",
                "start_time": time_to_str(meeting_start),
                "end_time": time_to_str(meeting_end)
            })

    return itinerary

# Generate the optimal schedule
optimal_schedule = find_optimal_schedule()

# Output the result as JSON
print(json.dumps({"itinerary": optimal_schedule}))