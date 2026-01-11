import json

def time_to_minutes(t):
    """Convert 'H:MM' or 'HH:MM' string to minutes since midnight."""
    hours, minutes = map(int, t.split(':'))
    return hours * 60 + minutes

def minutes_to_time(m):
    """Convert minutes since midnight to 'H:MM' or 'HH:MM' string."""
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

def main():
    # Given travel times in minutes
    travel_to_park = 11   # Sunset to Golden Gate Park
    travel_from_park = 10 # Golden Gate Park to Sunset

    # Start time at Sunset District
    start_time_str = "9:00"
    start_time = time_to_minutes(start_time_str)

    # Joshua's availability at Golden Gate Park
    joshua_start = time_to_minutes("20:45")
    joshua_end = time_to_minutes("21:45")
    min_meeting_duration = 15

    # We want to meet Joshua for at least 15 minutes within his window
    # We can leave Sunset early enough to arrive at start of his window
    # Or we can arrive later, but let's pick earliest possible meeting to be safe.

    # Earliest arrival at Golden Gate Park if we leave now: start_time + travel_to_park
    earliest_arrival = start_time + travel_to_park

    # If earliest_arrival is before Joshua's window, we can wait until his window starts
    meeting_start = max(earliest_arrival, joshua_start)
    # But meeting must end by joshua_end
    meeting_end = meeting_start + min_meeting_duration

    if meeting_end > joshua_end:
        # Try starting earlier within window
        meeting_start = joshua_end - min_meeting_duration
        meeting_end = joshua_end
        if meeting_start < joshua_start:
            # Not possible
            meeting_start = None

    if meeting_start is None or meeting_start < joshua_start:
        print("No feasible meeting with Joshua.")
        return

    # Departure from Sunset to arrive at meeting_start
    depart_sunset = meeting_start - travel_to_park
    if depart_sunset < start_time:
        # We can't leave before we arrive at Sunset, so adjust meeting_start
        meeting_start = start_time + travel_to_park
        meeting_end = meeting_start + min_meeting_duration
        if meeting_end > joshua_end:
            # Still impossible
            print("No feasible meeting with Joshua.")
            return

    # Build itinerary
    itinerary = [
        {
            "action": "meet",
            "location": "Golden Gate Park",
            "person": "Joshua",
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        }
    ]

    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()