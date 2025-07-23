import json
from datetime import datetime, timedelta

def time_to_minutes(time_str):
    dt = datetime.strptime(time_str, "%H:%M")
    return dt.hour * 60 + dt.minute

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def calculate_schedule():
    # Travel times in minutes
    travel_times = {
        ("North Beach", "Mission District"): 18,
        ("North Beach", "The Castro"): 22,
        ("Mission District", "North Beach"): 17,
        ("Mission District", "The Castro"): 7,
        ("The Castro", "North Beach"): 20,
        ("The Castro", "Mission District"): 7
    }

    # Constraints
    current_location = "North Beach"
    current_time = time_to_minutes("9:00")

    james_available_start = time_to_minutes("12:45")
    james_available_end = time_to_minutes("14:00")
    james_min_duration = 75
    james_location = "Mission District"

    robert_available_start = time_to_minutes("12:45")
    robert_available_end = time_to_minutes("15:15")
    robert_min_duration = 30
    robert_location = "The Castro"

    itinerary = []

    # Try to meet James first
    # Travel to James
    travel_time_to_james = travel_times[(current_location, james_location)]
    arrival_at_james = current_time + travel_time_to_james

    # Calculate meeting time with James
    james_meeting_start = max(arrival_at_james, james_available_start)
    james_meeting_end = james_meeting_start + james_min_duration

    if james_meeting_end <= james_available_end:
        # Can meet James
        itinerary.append({
            "action": "meet",
            "location": james_location,
            "person": "James",
            "start_time": minutes_to_time(james_meeting_start),
            "end_time": minutes_to_time(james_meeting_end)
        })

        # Travel to Robert
        travel_time_to_robert = travel_times[(james_location, robert_location)]
        arrival_at_robert = james_meeting_end + travel_time_to_robert

        # Calculate meeting time with Robert
        robert_meeting_start = max(arrival_at_robert, robert_available_start)
        robert_meeting_end = robert_meeting_start + robert_min_duration

        if robert_meeting_end <= robert_available_end:
            itinerary.append({
                "action": "meet",
                "location": robert_location,
                "person": "Robert",
                "start_time": minutes_to_time(robert_meeting_start),
                "end_time": minutes_to_time(robert_meeting_end)
            })
    else:
        # Cannot meet James, try meeting Robert first
        travel_time_to_robert = travel_times[(current_location, robert_location)]
        arrival_at_robert = current_time + travel_time_to_robert

        # Calculate meeting time with Robert
        robert_meeting_start = max(arrival_at_robert, robert_available_start)
        robert_meeting_end = robert_meeting_start + robert_min_duration

        if robert_meeting_end <= robert_available_end:
            itinerary.append({
                "action": "meet",
                "location": robert_location,
                "person": "Robert",
                "start_time": minutes_to_time(robert_meeting_start),
                "end_time": minutes_to_time(robert_meeting_end)
            })

            # Travel to James
            travel_time_to_james = travel_times[(robert_location, james_location)]
            arrival_at_james = robert_meeting_end + travel_time_to_james

            # Calculate meeting time with James
            james_meeting_start = max(arrival_at_james, james_available_start)
            james_meeting_end = james_meeting_start + james_min_duration

            if james_meeting_end <= james_available_end:
                itinerary.append({
                    "action": "meet",
                    "location": james_location,
                    "person": "James",
                    "start_time": minutes_to_time(james_meeting_start),
                    "end_time": minutes_to_time(james_meeting_end)
                })

    return {"itinerary": itinerary}

if __name__ == "__main__":
    schedule = calculate_schedule()
    print(json.dumps(schedule, indent=2))