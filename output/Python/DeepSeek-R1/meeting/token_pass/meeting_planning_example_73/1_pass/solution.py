import json

def time_to_minutes(time_str):
    time_part, period = time_str[:-2], time_str[-2:]
    hours, minutes = map(int, time_part.split(':'))
    if period == 'PM' and hours != 12:
        hours += 12
    elif period == 'AM' and hours == 12:
        hours = 0
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Input parameters
    start_location = "Russian Hill"
    start_time_str = "9:00AM"
    travel_time = 7  # minutes
    barbara_location = "Pacific Heights"
    barbara_start_str = "7:15AM"
    barbara_end_str = "10:00PM"
    min_meeting_duration = 60  # minutes

    # Convert times to minutes
    start_time_min = time_to_minutes(start_time_str)
    barbara_start_min = time_to_minutes(barbara_start_str)
    barbara_end_min = time_to_minutes(barbara_end_str)

    # Calculate arrival time at Pacific Heights
    arrival_time_min = start_time_min + travel_time

    # Determine meeting start and end times
    meeting_start_min = max(arrival_time_min, barbara_start_min)
    meeting_end_min = barbara_end_min

    # Ensure minimum meeting duration
    if meeting_end_min - meeting_start_min < min_meeting_duration:
        meeting_start_min = meeting_end_min - min_meeting_duration
        if meeting_start_min < barbara_start_min:
            meeting_start_min = barbara_start_min
            meeting_end_min = meeting_start_min + min_meeting_duration

    # Convert back to time strings
    meeting_start_str = minutes_to_time(meeting_start_min)
    meeting_end_str = minutes_to_time(meeting_end_min)

    # Create itinerary
    itinerary = [
        {
            "action": "meet",
            "location": barbara_location,
            "person": "Barbara",
            "start_time": meeting_start_str,
            "end_time": meeting_end_str
        }
    ]

    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()