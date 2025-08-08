#!/usr/bin/env python3
import json
from datetime import datetime, timedelta

def parse_time(time_str):
    # Expecting format "H:MM" in 24-hour format (e.g., "9:00" or "20:45")
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    # Use an arbitrary date; only time matters.
    return datetime(2020, 1, 1, hour, minute)

def format_time(dt):
    # Format time as "H:MM" with no leading zero for hour.
    return f"{dt.hour}:{dt.minute:02d}"

def main():
    # Input parameters
    arrival_alamo_str = "9:00"  # Arrival at Alamo Square
    # We'll assume one friend is available at Alamo Square early (Alex)
    # and Timothy is available at Richmond District later.
    
    # Timothy's availability window at Richmond District (from 8:45PM to 9:30PM)
    timothy_start_str = "20:45"
    timothy_end_str = "21:30"
    # Minimum meeting duration with Timothy (in minutes)
    required_meeting_duration = 45
    
    # Travel times in minutes
    travel_alamo_to_richmond = 12  # minutes from Alamo Square to Richmond District
    # (The opposite direction travel is provided but not needed in this schedule.)
    
    # Parse input times
    arrival_alamo = parse_time(arrival_alamo_str)
    timothy_start = parse_time(timothy_start_str)
    timothy_end = parse_time(timothy_end_str)
    
    # Compute the latest departure time from Alamo Square to reach Richmond District on time
    departure_time = timothy_start - timedelta(minutes=travel_alamo_to_richmond)
    # For debugging or internal check, one could verify:
    # arrival_at_richmond = departure_time + timedelta(minutes=travel_alamo_to_richmond)
    # assert arrival_at_richmond == timothy_start

    # Since our goal is to meet as many friends as possible, we consider:
    # 1. Meeting with a friend at Alamo Square (e.g., Alex) early in the day.
    # 2. Meeting Timothy at Richmond District in the evening.
    
    # Schedule meeting with Alex at Alamo Square.
    # We can start as soon as we arrive. Let's assume a 45 minute meeting.
    alex_meeting_start = arrival_alamo
    alex_meeting_duration = timedelta(minutes=45)
    alex_meeting_end = alex_meeting_start + alex_meeting_duration
    
    # Meeting with Timothy must be at least 45 minutes and fit his available window.
    # Given his window is exactly 45 minutes (from 20:45 to 21:30),
    # we set the meeting as such.
    timothy_meeting_start = timothy_start
    timothy_meeting_end = timothy_end  # This gives exactly 45 minutes.
    
    # Build the itinerary following the specified JSON structure.
    itinerary = []
    
    # First meeting: with Alex at Alamo Square.
    meeting_alamo = {
        "action": "meet",
        "location": "Alamo Square",
        "person": "Alex",
        "start_time": format_time(alex_meeting_start),
        "end_time": format_time(alex_meeting_end)
    }
    itinerary.append(meeting_alamo)
    
    # Second meeting: with Timothy at Richmond District.
    meeting_richmond = {
        "action": "meet",
        "location": "Richmond District",
        "person": "Timothy",
        "start_time": format_time(timothy_meeting_start),
        "end_time": format_time(timothy_meeting_end)
    }
    itinerary.append(meeting_richmond)
    
    # The schedule accounts for travel time:
    # We must depart Alamo Square by 'departure_time' (computed as timothy_start - 12 minutes)
    # in order to arrive at Richmond District for Timothy's meeting.
    # Although the travel is not output as a meeting event, it is factored into the schedule.
    
    schedule = {"itinerary": itinerary}
    
    # Output the schedule as a JSON-formatted dictionary.
    print(json.dumps(schedule, indent=2))

if __name__ == "__main__":
    main()