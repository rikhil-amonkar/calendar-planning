import json
from datetime import datetime, timedelta

def calculate_optimal_schedule():
    # Input parameters
    arrival_time = datetime.strptime("9:00", "%H:%M")
    joshua_start = datetime.strptime("20:45", "%H:%M")
    joshua_end = datetime.strptime("21:45", "%H:%M")
    min_meeting_duration = timedelta(minutes=15)
    sunset_to_golden_gate = timedelta(minutes=11)
    golden_gate_to_sunset = timedelta(minutes=10)
    
    # Calculate latest departure time to meet Joshua
    latest_departure_from_sunset = joshua_start + min_meeting_duration - sunset_to_golden_gate
    if latest_departure_from_sunset < arrival_time:
        # Cannot meet Joshua
        itinerary = []
    else:
        # Can meet Joshua
        travel_start = latest_departure_from_sunset
        travel_end = travel_start + sunset_to_golden_gate
        meeting_end = min(travel_end + min_meeting_duration, joshua_end)
        
        itinerary = [
            {
                "action": "travel",
                "location": "Sunset District to Golden Gate Park",
                "person": None,
                "start_time": travel_start.strftime("%-H:%M"),
                "end_time": travel_end.strftime("%-H:%M")
            },
            {
                "action": "meet",
                "location": "Golden Gate Park",
                "person": "Joshua",
                "start_time": travel_end.strftime("%-H:%M"),
                "end_time": meeting_end.strftime("%-H:%M")
            }
        ]
    
    return {
        "itinerary": itinerary
    }

result = calculate_optimal_schedule()
print(json.dumps(result, indent=2))