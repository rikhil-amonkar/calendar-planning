import json
from datetime import datetime, timedelta

# Input parameters
arrival_time = datetime.strptime("9:00", "%H:%M")
travel_time_sun_to_golden = timedelta(minutes=11)
travel_time_golden_to_sun = timedelta(minutes=10)
joshua_start_time = datetime.strptime("20:45", "%H:%M")
joshua_end_time = datetime.strptime("21:45", "%H:%M")
minimum_meeting_duration = timedelta(minutes=15)

def calculate_schedule(arrival_time, joshua_start_time, joshua_end_time, travel_time_sun_to_golden, travel_time_golden_to_sun, minimum_meeting_duration):
    itinerary = []

    # Check if we can meet Joshua
    latest_departure_time_for_joshua = joshua_end_time - minimum_meeting_duration
    if arrival_time + travel_time_sun_to_golden <= latest_departure_time_for_joshua:
        # Calculate meeting time with Joshua
        meeting_start_time_with_joshua = max(arrival_time + travel_time_sun_to_golden, joshua_start_time)
        meeting_end_time_with_joshua = meeting_start_time_with_joshua + minimum_meeting_duration

        # Add Joshua meeting to itinerary
        itinerary.append({
            "action": "meet",
            "location": "Golden Gate Park",
            "person": "Joshua",
            "start_time": meeting_start_time_with_joshua.strftime("%H:%M"),
            "end_time": meeting_end_time_with_joshua.strftime("%H:%M")
        })

    return itinerary

itinerary = calculate_schedule(arrival_time, joshua_start_time, joshua_end_time, travel_time_sun_to_golden, travel_time_golden_to_sun, minimum_meeting_duration)
result = {
    "itinerary": itinerary
}

print(json.dumps(result))