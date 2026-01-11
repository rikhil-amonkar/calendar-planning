import datetime
import json

def calculate_schedule():
    # Define constants
    arrival_time = datetime.datetime.strptime("9:00", "%H:%M")
    travel_to_presidio = datetime.timedelta(minutes=17)
    travel_to_nob_hill = datetime.timedelta(minutes=18)
    robert_start = datetime.datetime.strptime("11:15", "%H:%M")
    robert_end = datetime.datetime.strptime("17:45", "%H:%M")
    min_meeting_duration = datetime.timedelta(minutes=120)

    # Calculate the earliest possible arrival time at Presidio
    earliest_arrival_at_presidio = arrival_time + travel_to_presidio

    # Calculate the latest possible start time for the meeting with Robert
    latest_possible_start = robert_end - min_meeting_duration

    # Determine the actual meeting start and end times
    meeting_start = max(earliest_arrival_at_presidio, robert_start)
    meeting_end = meeting_start + min_meeting_duration

    # Ensure the meeting end time does not exceed Robert's available time
    if meeting_end > robert_end:
        raise ValueError("It's not possible to meet Robert for the required duration given the constraints.")

    # Create the itinerary
    itinerary = [
        {
            "action": "travel",
            "location": "Presidio",
            "start_time": arrival_time.strftime("%H:%M"),
            "end_time": (arrival_time + travel_to_presidio).strftime("%H:%M")
        },
        {
            "action": "meet",
            "location": "Presidio",
            "person": "Robert",
            "start_time": meeting_start.strftime("%H:%M"),
            "end_time": meeting_end.strftime("%H:%M")
        }
    ]

    # Return the itinerary as a JSON-formatted string
    return json.dumps({"itinerary": itinerary}, indent=2)

# Execute the function and print the result
print(calculate_schedule())