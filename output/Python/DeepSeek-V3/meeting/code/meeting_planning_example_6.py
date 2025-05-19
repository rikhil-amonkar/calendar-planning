import json
from datetime import datetime, timedelta

def calculate_optimal_schedule():
    # Input parameters
    arrival_time = datetime.strptime("9:00", "%H:%M")
    kenneth_available_start = datetime.strptime("14:15", "%H:%M")
    kenneth_available_end = datetime.strptime("19:45", "%H:%M")
    min_meeting_duration = timedelta(minutes=90)
    travel_time_to_nob_hill = timedelta(minutes=11)
    travel_time_to_fishermans_wharf = timedelta(minutes=11)

    # Calculate possible meeting window with Kenneth
    earliest_departure_to_meet = arrival_time + travel_time_to_nob_hill
    meeting_start = max(earliest_departure_to_meet, kenneth_available_start)
    meeting_end = meeting_start + min_meeting_duration

    # Check if meeting is possible within Kenneth's availability
    if meeting_end <= kenneth_available_end:
        # Calculate return time
        return_departure = meeting_end
        return_arrival = return_departure + travel_time_to_fishermans_wharf

        itinerary = [
            {
                "action": "travel",
                "location": "Nob Hill",
                "person": None,
                "start_time": arrival_time.strftime("%H:%M"),
                "end_time": earliest_departure_to_meet.strftime("%H:%M")
            },
            {
                "action": "meet",
                "location": "Nob Hill",
                "person": "Kenneth",
                "start_time": meeting_start.strftime("%H:%M"),
                "end_time": meeting_end.strftime("%H:%M")
            },
            {
                "action": "travel",
                "location": "Fisherman's Wharf",
                "person": None,
                "start_time": return_departure.strftime("%H:%M"),
                "end_time": return_arrival.strftime("%H:%M")
            }
        ]
    else:
        itinerary = [
            {
                "action": "no_meeting_possible",
                "location": None,
                "person": None,
                "start_time": None,
                "end_time": None
            }
        ]

    return {"itinerary": itinerary}

result = calculate_optimal_schedule()
print(json.dumps(result, indent=2))