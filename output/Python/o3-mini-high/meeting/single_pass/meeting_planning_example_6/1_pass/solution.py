#!/usr/bin/env python3
import json
from datetime import datetime, timedelta

def format_time(dt):
    # Formats the datetime object in "H:MM" format (no leading zero for hour)
    return f"{dt.hour}:{dt.minute:02d}"

def main():
    # Input parameters
    arrival_fw_str = "9:00"               # Arrival time at Fisherman's Wharf
    kenneth_start_str = "14:15"           # Kenneth available from 14:15 (2:15PM)
    kenneth_end_str = "19:45"             # Kenneth available until 19:45 (7:45PM)
    
    travel_fw_to_nh = 11                  # Travel time from Fisherman's Wharf to Nob Hill in minutes
    min_meeting_duration = 90             # Minimum meeting duration in minutes

    # Convert time strings to datetime objects (using an arbitrary common date)
    time_format = "%H:%M"
    arrival_fw = datetime.strptime(arrival_fw_str, time_format)
    kenneth_start = datetime.strptime(kenneth_start_str, time_format)
    kenneth_end = datetime.strptime(kenneth_end_str, time_format)

    # Compute earliest arrival at Nob Hill from Fisherman's Wharf
    arrival_nh = arrival_fw + timedelta(minutes=travel_fw_to_nh)

    # Determine the meeting start time at Nob Hill.
    # Must be no earlier than Kenneth's available start time.
    meeting_start = max(kenneth_start, arrival_nh)

    # Compute meeting end time based on the minimum required duration
    meeting_end = meeting_start + timedelta(minutes=min_meeting_duration)

    # Check if the meeting can be held within Kenneth's available window
    if meeting_end > kenneth_end:
        # If not possible, output an empty itinerary or appropriate message.
        schedule = { "itinerary": [] }
    else:
        schedule = {
            "itinerary": [
                {
                    "action": "meet",
                    "location": "Nob Hill",
                    "person": "Kenneth",
                    "start_time": format_time(meeting_start),
                    "end_time": format_time(meeting_end)
                }
            ]
        }
    
    # Output the schedule as a JSON-formatted dictionary
    print(json.dumps(schedule, indent=2))

if __name__ == "__main__":
    main()