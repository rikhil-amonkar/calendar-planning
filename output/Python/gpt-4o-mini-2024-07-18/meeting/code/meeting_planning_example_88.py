import json
from datetime import datetime, timedelta

def compute_meeting_schedule():
    # Input parameters
    arrival_time = datetime.strptime('09:00', '%H:%M')
    travel_to_park = timedelta(minutes=11)
    travel_back = timedelta(minutes=10)
    joshua_start = datetime.strptime('20:45', '%H:%M')
    joshua_end = datetime.strptime('21:45', '%H:%M')
    minimum_meeting_duration = timedelta(minutes=15)

    # Calculate times
    depart_for_park_time = arrival_time + travel_to_park
    meeting_start_time = max(depart_for_park_time, joshua_start)
    meeting_end_time = meeting_start_time + minimum_meeting_duration

    # Check if the meeting can happen
    if meeting_end_time <= joshua_end:
        # Create itinerary
        itinerary = [
            {
                "action": "meet",
                "location": "Golden Gate Park",
                "person": "Joshua",
                "start_time": meeting_start_time.strftime('%H:%M'),
                "end_time": meeting_end_time.strftime('%H:%M')
            }
        ]
    else:
        # No feasible meeting can be arranged
        itinerary = []

    result = {
        "itinerary": itinerary
    }

    return json.dumps(result, indent=2)

# Run the function and print the output
if __name__ == "__main__":
    output = compute_meeting_schedule()
    print(output)