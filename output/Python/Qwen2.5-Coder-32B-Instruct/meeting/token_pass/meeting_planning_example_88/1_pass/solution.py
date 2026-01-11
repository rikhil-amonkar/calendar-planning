import json
from datetime import datetime, timedelta

def calculate_meeting_schedule():
    # Define constants
    start_time_sunset = datetime.strptime("9:00", "%H:%M")
    travel_time_to_golden_gate = timedelta(minutes=11)
    joshua_start_time = datetime.strptime("20:45", "%H:%M")
    joshua_end_time = datetime.strptime("21:45", "%H:%M")
    min_meeting_duration = timedelta(minutes=15)

    # Calculate the latest possible arrival time at Golden Gate Park
    latest_arrival_time_golden_gate = joshua_end_time - min_meeting_duration

    # Calculate the earliest possible departure time from Sunset District
    earliest_departure_time_sunset = latest_arrival_time_golden_gate - travel_time_to_golden_gate

    # Construct the itinerary
    itinerary = []
    if earliest_departure_time_sunset >= start_time_sunset:
        # Add meeting with Joshua to the itinerary
        itinerary.append({
            "action": "meet",
            "location": "Golden Gate Park",
            "person": "Joshua",
            "start_time": latest_arrival_time_golden_gate.strftime("%H:%M"),
            "end_time": joshua_end_time.strftime("%H:%M")
        })

    # Output the itinerary as JSON
    return json.dumps({"itinerary": itinerary}, indent=2)

# Run the function and print the result
print(calculate_meeting_schedule())