import json

def time_to_minutes(time_str):
    """Convert a time string 'H:MM' in 24-hour format to minutes since midnight."""
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Convert minutes since midnight to a time string 'H:MM' in 24-hour format."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Input parameters
    start_location = "Russian Hill"
    start_time_str = "9:00"
    start_time = time_to_minutes(start_time_str)

    # Travel times in minutes between locations (directed)
    travel_times = {
        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "Mission District"): 16,
        ("Russian Hill", "Embarcadero"): 8,
        ("Nob Hill", "Russian Hill"): 5,
        ("Nob Hill", "Mission District"): 13,
        ("Nob Hill", "Embarcadero"): 9,
        ("Mission District", "Russian Hill"): 15,
        ("Mission District", "Nob Hill"): 12,
        ("Mission District", "Embarcadero"): 19,
        ("Embarcadero", "Russian Hill"): 8,
        ("Embarcadero", "Nob Hill"): 10,
        ("Embarcadero", "Mission District"): 20
    }

    # Meeting constraints for each friend
    meetings = [
        {
            "person": "Timothy",
            "location": "Embarcadero",
            "available_start": "9:45",
            "available_end": "17:45",
            "min_duration": 120  # in minutes
        },
        {
            "person": "Patricia",
            "location": "Nob Hill",
            "available_start": "18:30",
            "available_end": "21:45",
            "min_duration": 90
        },
        {
            "person": "Ashley",
            "location": "Mission District",
            "available_start": "20:30",
            "available_end": "21:15",
            "min_duration": 45
        }
    ]

    itinerary = []
    current_location = start_location
    current_time = start_time

    # Process each meeting in order
    for meeting in meetings:
        # Calculate travel time to the meeting location
        travel_key = (current_location, meeting["location"])
        if travel_key not in travel_times:
            raise ValueError(f"No travel time defined from {current_location} to {meeting['location']}")
        travel_duration = travel_times[travel_key]
        arrival_time = current_time + travel_duration

        # Meeting can only start when the friend is available
        meeting_available_start = time_to_minutes(meeting["available_start"])
        scheduled_start = max(arrival_time, meeting_available_start)

        # Compute meeting end time based on the required minimum duration
        scheduled_end = scheduled_start + meeting["min_duration"]

        # Check if the meeting can be completed within the friend's available window
        meeting_available_end = time_to_minutes(meeting["available_end"])
        if scheduled_end > meeting_available_end:
            raise ValueError(f"Cannot schedule meeting with {meeting['person']} within available time.")

        # Append meeting schedule details to itinerary
        itinerary.append({
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["person"],
            "start_time": minutes_to_time(scheduled_start),
            "end_time": minutes_to_time(scheduled_end)
        })

        # Update current time and location for next scheduling step
        current_time = scheduled_end
        current_location = meeting["location"]

    # Create the output dictionary
    result = {"itinerary": itinerary}

    # Output the result as a JSON-formatted string
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()