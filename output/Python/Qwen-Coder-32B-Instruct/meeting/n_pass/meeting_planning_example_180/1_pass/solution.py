import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ("North Beach", "Mission District"): 18,
    ("North Beach", "The Castro"): 22,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "The Castro"): 7,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Mission District"): 7,
}

# Define constraints
arrival_time = datetime.strptime("9:00", "%H:%M")
james_start = datetime.strptime("12:45", "%H:%M")
james_end = datetime.strptime("14:00", "%H:%M")
robert_start = datetime.strptime("12:45", "%H:%M")
robert_end = datetime.strptime("15:15", "%H:%M")

# Minimum meeting times
min_meeting_james = timedelta(minutes=75)
min_meeting_robert = timedelta(minutes=30)

def calculate_schedule():
    itinerary = []
    current_time = arrival_time
    current_location = "North Beach"

    # Try to meet James first
    if james_start - current_time >= min_meeting_james + travel_times[(current_location, "Mission District")]:
        travel_time = travel_times[(current_location, "Mission District")]
        current_time += timedelta(minutes=travel_time)
        current_location = "Mission District"
        itinerary.append({
            "action": "travel",
            "location": current_location,
            "start_time": current_time.strftime("%H:%M"),
            "end_time": (current_time + timedelta(minutes=travel_time)).strftime("%H:%M")
        })
        meeting_start = max(current_time, james_start)
        meeting_end = min(meeting_start + min_meeting_james, james_end)
        itinerary.append({
            "action": "meet",
            "location": current_location,
            "person": "James",
            "start_time": meeting_start.strftime("%H:%M"),
            "end_time": meeting_end.strftime("%H:%M")
        })
        current_time = meeting_end

    # Try to meet Robert next
    if robert_start - current_time >= min_meeting_robert + travel_times[(current_location, "The Castro")]:
        travel_time = travel_times[(current_location, "The Castro")]
        current_time += timedelta(minutes=travel_time)
        current_location = "The Castro"
        itinerary.append({
            "action": "travel",
            "location": current_location,
            "start_time": current_time.strftime("%H:%M"),
            "end_time": (current_time + timedelta(minutes=travel_time)).strftime("%H:%M")
        })
        meeting_start = max(current_time, robert_start)
        meeting_end = min(meeting_start + min_meeting_robert, robert_end)
        itinerary.append({
            "action": "meet",
            "location": current_location,
            "person": "Robert",
            "start_time": meeting_start.strftime("%H:%M"),
            "end_time": meeting_end.strftime("%H:%M")
        })
        current_time = meeting_end

    return itinerary

itinerary = calculate_schedule()
output = {
    "itinerary": itinerary
}

print(json.dumps(output))