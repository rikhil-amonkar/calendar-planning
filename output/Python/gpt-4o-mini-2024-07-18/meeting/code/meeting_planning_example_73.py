import json
from datetime import datetime, timedelta

# Define input parameters
arrival_time_russian_hill = datetime.strptime("09:00", "%H:%M")
barbara_availability_start = datetime.strptime("07:15", "%H:%M")
barbara_availability_end = datetime.strptime("22:00", "%H:%M")
minimum_meeting_duration = timedelta(minutes=60)
travel_time_russian_hill_to_pacific_heights = timedelta(minutes=7)
travel_time_pacific_heights_to_russian_hill = timedelta(minutes=7)

# Compute the potential meeting time window
latest_start_meeting_time = barbara_availability_end - minimum_meeting_duration
earliest_end_meeting_time = barbara_availability_start + minimum_meeting_duration

# Check if a valid meeting time is possible
if arrival_time_russian_hill >= latest_start_meeting_time or arrival_time_russian_hill >= barbara_availability_end:
    itinerary = []
else:
    # Calculate the latest possible start time from Russian Hill
    first_possible_meeting_time = arrival_time_russian_hill + travel_time_russian_hill_to_pacific_heights
    if first_possible_meeting_time < barbara_availability_start:
        first_possible_meeting_time = barbara_availability_start

    # Calculate the end time for the meeting
    meeting_end_time = first_possible_meeting_time + minimum_meeting_duration
    
    # Verify if the meeting end time is within Barbara's availability
    if meeting_end_time <= barbara_availability_end:
        itinerary = [
            {
                "action": "meet",
                "location": "Pacific Heights",
                "person": "Barbara",
                "start_time": first_possible_meeting_time.strftime("%H:%M"),
                "end_time": meeting_end_time.strftime("%H:%M")
            }
        ]
    else:
        itinerary = []

# Output the result in JSON format
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))