import json
from datetime import datetime, timedelta

def calculate_meeting_schedule():
    # Define the travel times in minutes
    travel_times = {
        ("richmond_district", "pacific_heights"): 10,
        ("richmond_district", "marina_district"): 9,
        ("pacific_heights", "richmond_district"): 12,
        ("pacific_heights", "marina_district"): 6,
        ("marina_district", "richmond_district"): 11,
        ("marina_district", "pacific_heights"): 7
    }

    # Define the meeting constraints
    constraints = {
        "jessica": {
            "location": "pacific_heights",
            "available_start": datetime.strptime("15:30", "%H:%M"),
            "available_end": datetime.strptime("16:45", "%H:%M"),
            "min_duration": timedelta(minutes=45)
        },
        "carol": {
            "location": "marina_district",
            "available_start": datetime.strptime("11:30", "%H:%M"),
            "available_end": datetime.strptime("15:00", "%H:%M"),
            "min_duration": timedelta(minutes=60)
        }
    }

    # Start time
    start_time = datetime.strptime("9:00", "%H:%M")

    # Function to convert datetime to string in H:MM format
    def time_to_str(time):
        return time.strftime("%-H:%M")

    # Function to find the best meeting time for a person
    def find_best_meeting_time(person, current_location, current_time):
        location = constraints[person]["location"]
        available_start = constraints[person]["available_start"]
        available_end = constraints[person]["available_end"]
        min_duration = constraints[person]["min_duration"]

        # Calculate travel time
        travel_time = travel_times[(current_location, location)]
        arrival_time = current_time + timedelta(minutes=travel_time)

        # If we arrive before the person's available start time, wait until they are available
        if arrival_time < available_start:
            arrival_time = available_start

        # Check if we can meet the person for the required duration
        if arrival_time + min_duration <= available_end:
            meeting_start = arrival_time
            meeting_end = meeting_start + min_duration
            return meeting_start, meeting_end, location
        else:
            return None, None, None

    # Initialize the itinerary
    itinerary = []
    current_location = "richmond_district"
    current_time = start_time

    # Try to meet Carol first
    carol_meeting_start, carol_meeting_end, carol_location = find_best_meeting_time("carol", current_location, current_time)
    if carol_meeting_start:
        itinerary.append({
            "action": "meet",
            "location": carol_location,
            "person": "carol",
            "start_time": time_to_str(carol_meeting_start),
            "end_time": time_to_str(carol_meeting_end)
        })
        current_time = carol_meeting_end
        current_location = carol_location

    # Try to meet Jessica next
    jessica_meeting_start, jessica_meeting_end, jessica_location = find_best_meeting_time("jessica", current_location, current_time)
    if jessica_meeting_start:
        itinerary.append({
            "action": "meet",
            "location": jessica_location,
            "person": "jessica",
            "start_time": time_to_str(jessica_meeting_start),
            "end_time": time_to_str(jessica_meeting_end)
        })

    # Output the result as JSON
    result = {
        "itinerary": itinerary
    }
    print(json.dumps(result))

calculate_meeting_schedule()