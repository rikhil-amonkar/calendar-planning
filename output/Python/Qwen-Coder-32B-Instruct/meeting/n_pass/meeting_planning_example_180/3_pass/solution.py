import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ("North Beach", "Mission District"): timedelta(minutes=18),
    ("North Beach", "The Castro"): timedelta(minutes=22),
    ("Mission District", "North Beach"): timedelta(minutes=17),
    ("Mission District", "The Castro"): timedelta(minutes=7),
    ("The Castro", "North Beach"): timedelta(minutes=20),
    ("The Castro", "Mission District"): timedelta(minutes=7),
}

# Define constraints
arrival_time = datetime.strptime("9:00", "%H:%M").time()
james_start = datetime.strptime("12:45", "%H:%M").time()
james_end = datetime.strptime("14:00", "%H:%M").time()
robert_start = datetime.strptime("12:45", "%H:%M").time()
robert_end = datetime.strptime("15:15", "%H:%M").time()

# Minimum meeting times
min_meeting_james = timedelta(minutes=75)
min_meeting_robert = timedelta(minutes=30)

def calculate_schedule():
    itinerary = []
    current_time = datetime.combine(datetime.today(), arrival_time)
    current_location = "North Beach"

    # Try to meet James first
    if datetime.combine(datetime.today(), james_start) - current_time >= min_meeting_james + travel_times[(current_location, "Mission District")]:
        travel_time = travel_times[(current_location, "Mission District")]
        current_time += travel_time
        current_location = "Mission District"
        itinerary.append({
            "action": "travel",
            "location": current_location,
            "start_time": current_time.time().strftime("%H:%M"),
            "end_time": (current_time + travel_time).time().strftime("%H:%M")
        })
        meeting_start = max(current_time, datetime.combine(datetime.today(), james_start))
        meeting_end = min(meeting_start + min_meeting_james, datetime.combine(datetime.today(), james_end))
        itinerary.append({
            "action": "meet",
            "location": current_location,
            "person": "James",
            "start_time": meeting_start.time().strftime("%H:%M"),
            "end_time": meeting_end.time().strftime("%H:%M")
        })
        current_time = meeting_end

    # Try to meet Robert next
    if datetime.combine(datetime.today(), robert_start) - current_time >= min_meeting_robert + travel_times[(current_location, "The Castro")]:
        travel_time = travel_times[(current_location, "The Castro")]
        current_time += travel_time
        current_location = "The Castro"
        itinerary.append({
            "action": "travel",
            "location": current_location,
            "start_time": current_time.time().strftime("%H:%M"),
            "end_time": (current_time + travel_time).time().strftime("%H:%M")
        })
        meeting_start = max(current_time, datetime.combine(datetime.today(), robert_start))
        meeting_end = min(meeting_start + min_meeting_robert, datetime.combine(datetime.today(), robert_end))
        itinerary.append({
            "action": "meet",
            "location": current_location,
            "person": "Robert",
            "start_time": meeting_start.time().strftime("%H:%M"),
            "end_time": meeting_end.time().strftime("%H:%M")
        })
        current_time = meeting_end

    # If James' meeting can't be scheduled first, try to schedule Robert first
    if not itinerary or itinerary[-1]["person"] != "James":
        current_time = datetime.combine(datetime.today(), arrival_time)
        current_location = "North Beach"

        if datetime.combine(datetime.today(), robert_start) - current_time >= min_meeting_robert + travel_times[(current_location, "The Castro")]:
            travel_time = travel_times[(current_location, "The Castro")]
            current_time += travel_time
            current_location = "The Castro"
            itinerary.append({
                "action": "travel",
                "location": current_location,
                "start_time": current_time.time().strftime("%H:%M"),
                "end_time": (current_time + travel_time).time().strftime("%H:%M")
            })
            meeting_start = max(current_time, datetime.combine(datetime.today(), robert_start))
            meeting_end = min(meeting_start + min_meeting_robert, datetime.combine(datetime.today(), robert_end))
            itinerary.append({
                "action": "meet",
                "location": current_location,
                "person": "Robert",
                "start_time": meeting_start.time().strftime("%H:%M"),
                "end_time": meeting_end.time().strftime("%H:%M")
            })
            current_time = meeting_end

            # Now try to meet James
            if datetime.combine(datetime.today(), james_start) - current_time >= min_meeting_james + travel_times[(current_location, "Mission District")]:
                travel_time = travel_times[(current_location, "Mission District")]
                current_time += travel_time
                current_location = "Mission District"
                itinerary.append({
                    "action": "travel",
                    "location": current_location,
                    "start_time": current_time.time().strftime("%H:%M"),
                    "end_time": (current_time + travel_time).time().strftime("%H:%M")
                })
                meeting_start = max(current_time, datetime.combine(datetime.today(), james_start))
                meeting_end = min(meeting_start + min_meeting_james, datetime.combine(datetime.today(), james_end))
                itinerary.append({
                    "action": "meet",
                    "location": current_location,
                    "person": "James",
                    "start_time": meeting_start.time().strftime("%H:%M"),
                    "end_time": meeting_end.time().strftime("%H:%M")
                })
                current_time = meeting_end

    return itinerary

itinerary = calculate_schedule()
output = {
    "itinerary": itinerary
}

print(json.dumps(output, indent=4))