#!/usr/bin/env python3
import json

def format_time(total_minutes):
    hour = total_minutes // 60
    minute = total_minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    # Input variables (in minutes since midnight)
    # You arrive at Golden Gate Park at 9:00AM
    golden_gate_park_arrival = 9 * 60  # 9:00AM -> 540 minutes past midnight
    
    # David's availability at Chinatown: from 16:00 (960 minutes) to 21:45 (1305 minutes)
    david_start = 16 * 60              # 960 minutes
    david_end = 21 * 60 + 45           # 1305 minutes
    
    # Travel times (in minutes)
    travel_g2c = 23  # Golden Gate Park to Chinatown
    travel_c2g = 23  # Chinatown to Golden Gate Park
    
    # Minimum meeting duration with David in minutes
    min_meeting_duration = 105  # 105 minutes
    
    # Compute the departure time from Golden Gate Park such that you arrive at Chinatown
    # as close as possible to the start of David's availability at 16:00.
    # departure_time + travel_g2c should equal David's available start time.
    departure_time = david_start - travel_g2c  # 960 - 23 = 937 minutes (15:37)
    
    # Arrival at Chinatown after travel
    arrival_at_chinatown = departure_time + travel_g2c  # should be 960 minutes (16:00)
    
    # The meeting can only start when David is available.
    meeting_start = max(arrival_at_chinatown, david_start)  # 960 minutes (16:00)
    meeting_end = meeting_start + min_meeting_duration       # 960 + 105 = 1065 minutes (17:45)
    
    # Ensure the meeting end does not exceed David's end availability.
    if meeting_end > david_end:
        meeting_end = david_end
    
    itinerary = [
        {
            "action": "meet",
            "location": "Chinatown",
            "person": "David",
            "start_time": format_time(meeting_start),
            "end_time": format_time(meeting_end)
        }
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()