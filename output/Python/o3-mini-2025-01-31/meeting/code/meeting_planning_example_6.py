#!/usr/bin/env python3
import json
from datetime import datetime, timedelta

def minutes_to_time_str(total_minutes):
    hours = total_minutes // 60
    minutes = total_minutes % 60
    # Format as H:MM with hour as non-padded and minute always 2-digit
    return f"{hours}:{minutes:02d}"

def add_minutes(time_str, minutes_to_add):
    # Parse time_str in H:MM format
    parts = time_str.split(":")
    hours = int(parts[0])
    minutes = int(parts[1])
    total = hours * 60 + minutes + minutes_to_add
    return minutes_to_time_str(total)

def compute_optimal_schedule():
    # Input parameters
    arrival_at_fishermans_wharf = "9:00"
    # Convert arrival time into minutes from midnight
    arrival_parts = arrival_at_fishermans_wharf.split(":")
    arrival_time = int(arrival_parts[0]) * 60 + int(arrival_parts[1])
    
    # Kenneth constraints at Nob Hill (in minutes from midnight)
    kenneth_start = 14 * 60 + 15  # 14:15 is 855 minutes
    kenneth_end = 19 * 60 + 45    # 19:45 is 1185 minutes
    minimum_meet_duration = 90    # in minutes

    # Travel distances (in minutes)
    travel_fwh_to_nh = 11

    # Compute the earliest arrival at Nob Hill
    earliest_arrival_nh = arrival_time + travel_fwh_to_nh
    # Meeting with Kenneth can only start at or after his available time.
    meeting_start_time = max(earliest_arrival_nh, kenneth_start)
    
    # Compute meeting end time (minimum required meeting duration)
    meeting_end_time = meeting_start_time + minimum_meet_duration

    # Ensure meeting_end_time does not exceed Kenneth's available window
    if meeting_end_time > kenneth_end:
        raise Exception("Unable to schedule a meeting that satisfies the constraints.")

    # Format times as strings in H:MM format.
    meeting_start_str = minutes_to_time_str(meeting_start_time)
    meeting_end_str = minutes_to_time_str(meeting_end_time)

    itinerary = [
        {
            "action": "meet",
            "location": "Nob Hill",
            "person": "Kenneth",
            "start_time": meeting_start_str,
            "end_time": meeting_end_str
        }
    ]

    return {"itinerary": itinerary}

if __name__ == "__main__":
    schedule = compute_optimal_schedule()
    # Output as JSON-formatted dictionary
    print(json.dumps(schedule, indent=2))