#!/usr/bin/env python3
import json
from datetime import datetime, timedelta

def add_minutes(time_obj, minutes):
    return time_obj + timedelta(minutes=minutes)

def format_time(dt):
    # Format time in H:MM (24-hour) format without a leading zero for the hour.
    # Remove any leading zero from hour.
    # For example, if dt.strftime('%H:%M') returns "09:00", we want "9:00".
    # We can convert hour to int and then format.
    return f"{int(dt.strftime('%H'))}:{dt.strftime('%M')}"

def main():
    # Input parameters (all times use a dummy date, here 2023-01-01)
    arrival_str = "9:00"  # arrival at Alamo Square
    timothy_avail_start_str = "20:45"  # 8:45PM in 24h format
    timothy_avail_end_str = "21:30"    # 9:30PM in 24h format
    required_meeting_duration = 45  # in minutes

    # Travel distances (in minutes)
    travel_alamo_to_richmond = 12
    travel_richmond_to_alamo = 13

    # Base date for our datetime objects
    base_date = "2023-01-01 "

    # Parse arrival and availability times into datetime objects
    arrival_time = datetime.strptime(base_date + arrival_str, "%Y-%m-%d %H:%M")
    timothy_start = datetime.strptime(base_date + timothy_avail_start_str, "%Y-%m-%d %H:%M")
    timothy_end = datetime.strptime(base_date + timothy_avail_end_str, "%Y-%m-%d %H:%M")

    # To meet Timothy, we need to leave Alamo Square in time to reach Richmond District by his availability start.
    # Calculate required departure time from Alamo Square
    departure_time = timothy_start - timedelta(minutes=travel_alamo_to_richmond)
    
    # Check feasibility: We must have arrived at the meeting point area in time 
    if arrival_time > departure_time:
        # If arrival is later than the required departure time, it's not possible to meet Timothy.
        itinerary = {"itinerary": []}
    else:
        # The meeting with Timothy is scheduled at his location.
        # The meeting can start at his available start time and last for 45 minutes.
        meeting_start = timothy_start
        meeting_end = meeting_start + timedelta(minutes=required_meeting_duration)
        
        # Ensure the meeting does not exceed Timothy's available time window.
        if meeting_end > timothy_end:
            # If the meeting end time exceeds his availability, adjust the meeting_end to his available end time.
            meeting_end = timothy_end
        
        # Check if the actual meeting duration meets the requirement (should be at least 45 minutes).
        actual_duration = (meeting_end - meeting_start).seconds // 60
        if actual_duration < required_meeting_duration:
            itinerary = {"itinerary": []}
        else:
            # Create itinerary object. We include two events:
            # 1. Departing from Alamo Square (calculated as departure_time) with travel detail embedded.
            #    While the instructions require an action "meet", we include this as a planning step.
            # 2. Meeting with Timothy at Richmond District.
            # However, to follow the required JSON structure exactly where each event uses "action": "meet",
            # we include only the meeting event.
            
            meeting_event = {
                "action": "meet",
                "location": "Richmond District",
                "person": "Timothy",
                "start_time": format_time(meeting_start),
                "end_time": format_time(meeting_end)
            }
            itinerary = {"itinerary": [meeting_event]}
    
    # Output the itinerary as a JSON formatted dictionary
    print(json.dumps(itinerary, indent=2))

if __name__ == "__main__":
    main()