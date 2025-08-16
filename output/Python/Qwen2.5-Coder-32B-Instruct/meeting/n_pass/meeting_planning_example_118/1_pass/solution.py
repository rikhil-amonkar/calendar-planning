import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ("Bayview", "Union Square"): 17,
    ("Bayview", "Presidio"): 31,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Presidio"): 24,
    ("Presidio", "Bayview"): 31,
    ("Presidio", "Union Square"): 22
}

# Define constraints
arrival_time = datetime.strptime("9:00", "%H:%M")
richard_start = datetime.strptime("8:45", "%H:%M")
richard_end = datetime.strptime("13:00", "%H:%M")
charles_start = datetime.strptime("9:45", "%H:%M")
charles_end = datetime.strptime("13:00", "%H:%M")
min_meeting_duration = timedelta(minutes=120)

# Function to convert datetime to string in H:MM format
def time_to_str(time):
    return time.strftime("%H:%M")

# Function to find the optimal schedule
def find_optimal_schedule():
    itinerary = []

    # Try to meet Richard first
    current_location = "Bayview"
    current_time = arrival_time

    # Travel to Union Square if needed and check availability
    if current_location != "Union Square":
        travel_time = travel_times[(current_location, "Union Square")]
        current_time += timedelta(minutes=travel_time)
        current_location = "Union Square"

    # Meet Richard
    if current_time + min_meeting_duration <= richard_end:
        meeting_start = max(current_time, richard_start)
        meeting_end = meeting_start + min_meeting_duration
        itinerary.append({
            "action": "meet",
            "location": "Union Square",
            "person": "Richard",
            "start_time": time_to_str(meeting_start),
            "end_time": time_to_str(meeting_end)
        })
        current_time = meeting_end

    # Travel to Presidio if needed and check availability
    if current_location != "Presidio":
        travel_time = travel_times[(current_location, "Presidio")]
        current_time += timedelta(minutes=travel_time)
        current_location = "Presidio"

    # Meet Charles
    if current_time + min_meeting_duration <= charles_end:
        meeting_start = max(current_time, charles_start)
        meeting_end = meeting_start + min_meeting_duration
        itinerary.append({
            "action": "meet",
            "location": "Presidio",
            "person": "Charles",
            "start_time": time_to_str(meeting_start),
            "end_time": time_to_str(meeting_end)
        })

    return itinerary

# Generate the optimal schedule
optimal_itinerary = find_optimal_schedule()

# Output the result as JSON
print(json.dumps({"itinerary": optimal_itinerary}, indent=2))