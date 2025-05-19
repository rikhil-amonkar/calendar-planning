#!/usr/bin/env python3
import json
from datetime import datetime, timedelta

def format_time(dt):
    # Format time as H:MM in 24-hour format with no leading zero for hour.
    return f"{dt.hour}:{dt.minute:02d}"

def main():
    # Input Variables
    # Arrival at North Beach at 9:00AM (using any arbitrary date, here Jan 1, 2023)
    arrival_location = "North Beach"
    arrival_time = datetime(2023, 1, 1, 9, 0)
    
    # Travel times in minutes between locations
    travel_times = {
        ("North Beach", "Mission District"): 18,
        ("North Beach", "The Castro"): 22,
        ("Mission District", "North Beach"): 17,
        ("Mission District", "The Castro"): 7,
        ("The Castro", "North Beach"): 20,
        ("The Castro", "Mission District"): 7
    }
    
    # James's meeting details: available at Mission District from 12:45 to 14:00 with a minimum meeting duration of 75 minutes.
    james_location = "Mission District"
    james_avail_start = datetime(2023, 1, 1, 12, 45)
    james_avail_end = datetime(2023, 1, 1, 14, 0)
    james_min_duration = timedelta(minutes=75)
    
    # Robert's meeting details: available at The Castro from 12:45 to 15:15 with a minimum meeting duration of 30 minutes.
    robert_location = "The Castro"
    robert_avail_start = datetime(2023, 1, 1, 12, 45)
    robert_avail_end = datetime(2023, 1, 1, 15, 15)
    robert_min_duration = timedelta(minutes=30)
    
    # The optimal plan is to meet James first then Robert.
    # Compute departure from North Beach to arrive at Mission District exactly at James's available start.
    travel_NB_to_Mission = timedelta(minutes=travel_times[(arrival_location, james_location)])
    departure_from_NB = james_avail_start - travel_NB_to_Mission
    # (Assume waiting at North Beach until departure_from_NB if arrival_time is earlier)
    
    # Schedule meeting with James
    james_meeting_start = james_avail_start
    james_meeting_end = james_meeting_start + james_min_duration
    # Ensure meeting ends within his available window
    if james_meeting_end > james_avail_end:
        james_meeting_end = james_avail_end
    
    # After meeting James, travel from Mission District to The Castro
    travel_Mission_to_Castro = timedelta(minutes=travel_times[(james_location, robert_location)])
    arrival_at_robert = james_meeting_end + travel_Mission_to_Castro
    
    # Schedule meeting with Robert, starting at the later of arrival time or his available start time.
    robert_meeting_start = max(arrival_at_robert, robert_avail_start)
    robert_meeting_end = robert_meeting_start + robert_min_duration
    if robert_meeting_end > robert_avail_end:
        robert_meeting_end = robert_avail_end
    
    # Build itinerary as required output structure.
    itinerary = [
        {
            "action": "meet",
            "location": james_location,
            "person": "James",
            "start_time": format_time(james_meeting_start),
            "end_time": format_time(james_meeting_end)
        },
        {
            "action": "meet",
            "location": robert_location,
            "person": "Robert",
            "start_time": format_time(robert_meeting_start),
            "end_time": format_time(robert_meeting_end)
        }
    ]
    
    schedule = {"itinerary": itinerary}
    # Output the schedule in JSON format.
    print(json.dumps(schedule, indent=2))

if __name__ == "__main__":
    main()