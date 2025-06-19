import json
from datetime import datetime, timedelta

def compute_optimal_meeting_schedule(arrival_time, departure_time, travel_time, meeting_start, meeting_end, meeting_duration):
    """
    Compute the optimal meeting schedule given the arrival and departure times, travel time, meeting start and end times, and meeting duration.

    Args:
        arrival_time (str): The arrival time in HH:MM format.
        departure_time (str): The departure time in HH:MM format.
        travel_time (int): The travel time between locations in minutes.
        meeting_start (str): The meeting start time in HH:MM format.
        meeting_end (str): The meeting end time in HH:MM format.
        meeting_duration (int): The meeting duration in minutes.

    Returns:
        str: The optimal meeting schedule in JSON format.
    """

    # Validate input parameters
    if not (0 <= travel_time <= 60):
        raise ValueError("Travel time must be between 0 and 60 minutes")
    if not (0 <= meeting_duration <= 60):
        raise ValueError("Meeting duration must be between 0 and 60 minutes")
    if not (arrival_time <= departure_time):
        raise ValueError("Arrival time must be before departure time")
    if not (meeting_start <= meeting_end):
        raise ValueError("Meeting start time must be before meeting end time")

    # Convert times to datetime objects
    arrival_time = datetime.strptime(arrival_time, "%H:%M")
    departure_time = datetime.strptime(departure_time, "%H:%M")
    meeting_start = datetime.strptime(meeting_start, "%H:%M")
    meeting_end = datetime.strptime(meeting_end, "%H:%M")

    # Compute earliest possible meeting start time
    earliest_meeting_start = max(arrival_time, meeting_start)
    earliest_meeting_end = earliest_meeting_start + timedelta(minutes=meeting_duration)

    # Initialize itinerary
    itinerary = []

    # Check if earliest meeting fits within constraints
    if earliest_meeting_end <= departure_time:
        # Schedule meeting at earliest possible time
        itinerary.append({
            "action": "meet",
            "location": "Russian Hill",
            "person": "You",
            "start_time": earliest_meeting_start.strftime("%H:%M"),
            "end_time": earliest_meeting_end.strftime("%H:%M")
        })

        # Compute latest possible meeting start time
        latest_meeting_start = earliest_meeting_start + timedelta(minutes=travel_time)
        latest_meeting_end = latest_meeting_start + timedelta(minutes=meeting_duration)

        # Check if latest meeting fits within constraints
        if latest_meeting_end <= departure_time:
            # Schedule meeting at latest possible time
            itinerary.append({
                "action": "meet",
                "location": "Pacific Heights",
                "person": "Barbara",
                "start_time": latest_meeting_start.strftime("%H:%M"),
                "end_time": latest_meeting_end.strftime("%H:%M")
            })

        # Add travel time to itinerary
        itinerary.append({
            "action": "travel",
            "location": "Pacific Heights",
            "person": "You",
            "start_time": earliest_meeting_end.strftime("%H:%M"),
            "end_time": (earliest_meeting_end + timedelta(minutes=travel_time)).strftime("%H:%M")
        })

        # Add travel time from Pacific Heights back to Russian Hill
        itinerary.append({
            "action": "travel",
            "location": "Russian Hill",
            "person": "You",
            "start_time": (earliest_meeting_end + timedelta(minutes=travel_time)).strftime("%H:%M"),
            "end_time": (earliest_meeting_end + timedelta(minutes=travel_time * 2)).strftime("%H:%M")
        })

    # Check if meeting can be scheduled at meeting start time
    if meeting_start <= arrival_time:
        itinerary.append({
            "action": "meet",
            "location": "Russian Hill",
            "person": "You",
            "start_time": meeting_start.strftime("%H:%M"),
            "end_time": (meeting_start + timedelta(minutes=meeting_duration)).strftime("%H:%M")
        })

        # Add travel time to itinerary
        itinerary.append({
            "action": "travel",
            "location": "Pacific Heights",
            "person": "You",
            "start_time": (meeting_start + timedelta(minutes=meeting_duration)).strftime("%H:%M"),
            "end_time": (meeting_start + timedelta(minutes=meeting_duration + travel_time)).strftime("%H:%M")
        })

        # Add travel time from Pacific Heights back to Russian Hill
        itinerary.append({
            "action": "travel",
            "location": "Russian Hill",
            "person": "You",
            "start_time": (meeting_start + timedelta(minutes=meeting_duration + travel_time)).strftime("%H:%M"),
            "end_time": (meeting_start + timedelta(minutes=meeting_duration + travel_time * 2)).strftime("%H:%M")
        })

    # Check if meeting can be scheduled at meeting end time
    if meeting_end >= departure_time:
        itinerary.append({
            "action": "meet",
            "location": "Russian Hill",
            "person": "You",
            "start_time": (departure_time - timedelta(minutes=meeting_duration)).strftime("%H:%M"),
            "end_time": departure_time.strftime("%H:%M")
        })

    # Return itinerary as JSON
    return json.dumps({"itinerary": itinerary})

# Input parameters
arrival_time = "09:00"
departure_time = "22:00"
travel_time = 7
meeting_start = "07:15"
meeting_end = "22:00"
meeting_duration = 60

# Compute optimal meeting schedule
optimal_schedule = compute_optimal_meeting_schedule(arrival_time, departure_time, travel_time, meeting_start, meeting_end, meeting_duration)

# Print optimal schedule
print("SOLUTION:")
print(optimal_schedule)