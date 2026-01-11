import json

def time_to_minutes(t):
    """Convert 'H:MM' string to minutes since midnight."""
    if isinstance(t, str):
        hours, minutes = map(int, t.split(':'))
        return hours * 60 + minutes
    return t

def minutes_to_time(m):
    """Convert minutes since midnight to 'H:MM' string."""
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

def main():
    # Given data
    start_location = "Russian Hill"
    start_time_str = "9:00"
    barbara_location = "Pacific Heights"
    barbara_available_start_str = "7:15"
    barbara_available_end_str = "22:00"  # 10:00 PM in 24-hour
    travel_minutes = 7
    min_meeting_minutes = 60

    # Convert to minutes
    start_time_min = time_to_minutes(start_time_str)
    barbara_start_min = time_to_minutes(barbara_available_start_str)
    barbara_end_min = time_to_minutes(barbara_available_end_str)

    # Earliest we can arrive at Pacific Heights
    arrival_at_pacific = start_time_min + travel_minutes

    # Meeting must start no earlier than Barbara's start time and no earlier than our arrival
    meeting_start = max(arrival_at_pacific, barbara_start_min)

    # Meeting end time
    meeting_end = meeting_start + min_meeting_minutes

    # Check if meeting fits within Barbara's availability
    if meeting_end > barbara_end_min:
        # If not possible, adjust meeting start earlier if possible
        meeting_start = barbara_end_min - min_meeting_minutes
        if meeting_start < arrival_at_pacific:
            # Not possible to meet for 60 minutes
            meeting_start = None

    if meeting_start is None:
        itinerary = []
    else:
        # Build itinerary
        itinerary = [
            {
                "action": "travel",
                "location": barbara_location,
                "person": "",
                "start_time": minutes_to_time(start_time_min),
                "end_time": minutes_to_time(arrival_at_pacific)
            },
            {
                "action": "meet",
                "location": barbara_location,
                "person": "Barbara",
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            },
            {
                "action": "travel",
                "location": start_location,
                "person": "",
                "start_time": minutes_to_time(meeting_end),
                "end_time": minutes_to_time(meeting_end + travel_minutes)
            }
        ]

    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()