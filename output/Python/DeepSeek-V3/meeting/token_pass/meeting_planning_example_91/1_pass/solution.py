import json

def time_to_minutes(t):
    """Convert 'H:MM' or 'HH:MM' string to minutes since midnight."""
    if isinstance(t, str):
        h, m = map(int, t.split(':'))
        return h * 60 + m
    return t

def minutes_to_time(m):
    """Convert minutes since midnight to 'H:MM' or 'HH:MM' string."""
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def main():
    # Given data
    start_location = "Russian Hill"
    start_time_str = "9:00"
    daniel_location = "Richmond District"
    daniel_window_start_str = "19:00"
    daniel_window_end_str = "20:15"
    travel_to_daniel = 14  # minutes
    min_meeting_duration = 75  # minutes

    # Convert to minutes
    start_time = time_to_minutes(start_time_str)
    daniel_start = time_to_minutes(daniel_window_start_str)
    daniel_end = time_to_minutes(daniel_window_end_str)

    # Daniel's available duration
    daniel_available_duration = daniel_end - daniel_start

    # Check if available duration meets minimum requirement
    if daniel_available_duration < min_meeting_duration:
        meeting_duration = daniel_available_duration
    else:
        meeting_duration = min_meeting_duration

    # We must arrive at daniel_start to maximize time with him
    # (since window is exactly 75 minutes, we take the whole window)
    meeting_start = daniel_start
    meeting_end = daniel_start + meeting_duration

    # Ensure meeting_end does not exceed daniel_end
    if meeting_end > daniel_end:
        meeting_end = daniel_end

    # Travel must be accounted for: we leave start_location at meeting_start - travel_to_daniel
    depart_to_daniel = meeting_start - travel_to_daniel

    # Check if depart_to_daniel is feasible (not before start_time)
    if depart_to_daniel < start_time:
        # If not feasible, we must shift meeting later? But Daniel's window is fixed.
        # In this case, it's feasible because 19:00 - 14 min = 18:46, which is after 9:00.
        pass

    # Build itinerary (only meetings, per example output format)
    itinerary = [
        {
            "action": "meet",
            "location": daniel_location,
            "person": "Daniel",
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        }
    ]

    # Output as JSON
    result = {
        "itinerary": itinerary
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()