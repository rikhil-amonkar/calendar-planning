import json
from datetime import datetime, timedelta

def calculate_meeting_schedule():
    # Constants
    arrival_time = datetime.strptime("9:00", "%H:%M")
    travel_time_minutes = 23
    david_start_time = datetime.strptime("16:00", "%H:%M")  # 4:00 PM
    david_end_time = datetime.strptime("21:45", "%H:%M")  # 9:45 PM
    required_meeting_duration = timedelta(minutes=105)

    # Calculate the latest possible start time for meeting David
    latest_meeting_start_time = david_end_time - required_meeting_duration
    latest_departure_time_from_park = latest_meeting_start_time - timedelta(minutes=travel_time_minutes)

    # Construct the itinerary
    itinerary = [
        {
            "action": "travel",
            "location": "Golden Gate Park",
            "start_time": arrival_time.strftime("%H:%M"),
            "end_time": latest_departure_time_from_park.strftime("%H:%M")
        },
        {
            "action": "travel",
            "location": "Chinatown",
            "start_time": latest_departure_time_from_park.strftime("%H:%M"),
            "end_time": latest_meeting_start_time.strftime("%H:%M")
        },
        {
            "action": "meet",
            "location": "Chinatown",
            "person": "David",
            "start_time": latest_meeting_start_time.strftime("%H:%M"),
            "end_time": david_end_time.strftime("%H:%M")
        }
    ]

    # Remove the travel actions since they are implied by the meet actions
    optimal_itinerary = [item for item in itinerary if item["action"] == "meet"]

    return json.dumps({"itinerary": optimal_itinerary}, indent=2)

# Execute the function and print the result
print(calculate_meeting_schedule())