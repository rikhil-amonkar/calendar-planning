import json
from datetime import datetime, timedelta

def calculate_optimal_schedule():
    # Constants
    arrival_time = datetime.strptime("9:00", "%H:%M")
    timothy_start = datetime.strptime("20:45", "%H:%M")
    timothy_end = datetime.strptime("21:30", "%H:%M")
    min_meeting_duration = timedelta(minutes=45)
    travel_time_to_richmond = timedelta(minutes=12)
    travel_time_to_alamo = timedelta(minutes=13)

    # Calculate the latest time we can leave Alamo Square to meet Timothy for 45 minutes
    latest_leave_time = timothy_end - min_meeting_duration

    # Check if it's feasible to meet Timothy
    if latest_leave_time - arrival_time < travel_time_to_richmond:
        # Not enough time to travel to Richmond and meet Timothy for 45 minutes
        itinerary = []
    else:
        # Calculate the exact meeting times
        meeting_start_time = latest_leave_time - travel_time_to_richmond
        meeting_end_time = meeting_start_time + min_meeting_duration

        # Format times as strings
        meeting_start_str = meeting_start_time.strftime("%H:%M").lstrip('0')
        meeting_end_str = meeting_end_time.strftime("%H:%M").lstrip('0')

        # Create the itinerary
        itinerary = [
            {
                "action": "meet",
                "location": "Richmond District",
                "person": "Timothy",
                "start_time": meeting_start_str,
                "end_time": meeting_end_str
            }
        ]

    # Return the itinerary as JSON
    return json.dumps({"itinerary": itinerary})

# Execute the function and print the result
print(calculate_optimal_schedule())