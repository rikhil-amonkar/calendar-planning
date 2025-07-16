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
    
    # Calculate latest possible departure time from Sunset to meet Joshua for 15 minutes
    latest_departure_sunset = joshua_end - min_meeting_duration - sunset_to_golden_gate
    
    # Check if we can make it to meet Joshua
    if arrival_time + golden_gate_to_sunset <= latest_departure_sunset:
        # We can meet Joshua
        meet_start = max(joshua_start, arrival_time + sunset_to_golden_gate)
        meet_end = meet_start + min_meeting_duration
        if meet_end <= joshua_end:
            itinerary = [
                {
                    "action": "travel",
                    "location": "Sunset District to Golden Gate Park",
                    "person": "None",
                    "start_time": arrival_time.strftime("%H:%M"),
                    "end_time": (arrival_time + sunset_to_golden_gate).strftime("%H:%M")
                },
                {
                    "action": "meet",
                    "location": "Golden Gate Park",
                    "person": "Joshua",
                    "start_time": meet_start.strftime("%H:%M"),
                    "end_time": meet_end.strftime("%H:%M")
                },
                {
                    "action": "travel",
                    "location": "Golden Gate Park to Sunset District",
                    "person": "None",
                    "start_time": meet_end.strftime("%H:%M"),
                    "end_time": (meet_end + golden_gate_to_sunset).strftime("%H:%M")
                }
            ]
        else:
            # Can't meet Joshua for full duration
            itinerary = []
    else:
        # Can't meet Joshua at all
        itinerary = []
    
    result = {
        "itinerary": itinerary
    }
    
    return json.dumps(result, indent=2)

if __name__ == "__main__":
    print(calculate_optimal_schedule())