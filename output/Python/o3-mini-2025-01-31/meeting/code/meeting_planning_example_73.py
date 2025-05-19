#!/usr/bin/env python3
import json
from datetime import datetime, timedelta

def format_time(dt):
    # Format time in H:MM 24-hour format (no leading zero for the hour)
    return dt.strftime('%-H:%M') if dt.strftime('%-H') != '' else dt.strftime('%H:%M')

def main():
    # Input parameters and constraints
    # Arrival time at Russian Hill: 9:00 AM
    arrival_str = "9:00"
    arrival = datetime.strptime(arrival_str, "%H:%M")
    
    # Barbara's availability at Pacific Heights:
    barbara_avail_start = datetime.strptime("7:15", "%H:%M")
    barbara_avail_end = datetime.strptime("22:00", "%H:%M")
    
    # Travel times (in minutes)
    travel_RH_to_PH = 7
    travel_PH_to_RH = 7  # (not used in meeting time calculation, but provided)
    
    # Minimum meeting duration with Barbara is 60 minutes.
    min_meeting_duration = timedelta(minutes=60)
    
    # Since Barbara is at Pacific Heights and you are at Russian Hill,
    # the earliest you can reach her is after traveling.
    meeting_start = arrival + timedelta(minutes=travel_RH_to_PH)
    
    # Ensure that the meeting starts within Barbara's available window.
    if meeting_start < barbara_avail_start:
        meeting_start = barbara_avail_start

    meeting_end = meeting_start + min_meeting_duration
    
    # Check if meeting end is within Barbara's available window.
    if meeting_end > barbara_avail_end:
        raise ValueError("Cannot schedule a meeting with Barbara that satisfies the constraints.")
    
    # Prepare the itinerary as a list of meeting events.
    itinerary = []
    # Create a meeting entry for Barbara at Pacific Heights.
    meeting_event = {
        "action": "meet",
        "location": "Pacific Heights",
        "person": "Barbara",
        "start_time": format_time(meeting_start),
        "end_time": format_time(meeting_end)
    }
    itinerary.append(meeting_event)
    
    # Output result as a JSON-formatted dictionary.
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
    
if __name__ == "__main__":
    main()