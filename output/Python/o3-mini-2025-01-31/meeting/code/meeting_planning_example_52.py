#!/usr/bin/env python3
import json

def minutes_to_time(minutes):
    # Convert minutes since midnight to H:MM format (24-hour)
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    # Input parameters (in minutes since midnight)
    # Arrival at Russian Hill at 9:00 AM
    arrival_rh = 9 * 60  # 9:00 AM => 540 minutes
    
    # Barbara's availability at Richmond District:
    barbara_start = 13 * 60 + 15   # 13:15 => 795 minutes
    barbara_end = 18 * 60 + 15     # 18:15 => 1095 minutes
    meeting_min_duration = 45      # minimum meeting duration in minutes
    
    # Travel times in minutes
    travel_rh_to_rd = 14   # Russian Hill to Richmond District
    travel_rd_to_rh = 13   # Richmond District to Russian Hill (not used here but provided)
    
    # Calculate the departure time from Russian Hill so as to arrive at Barbara's location at exactly her available start time.
    # We assume travel must be completed before meeting can begin.
    departure_from_rh = barbara_start - travel_rh_to_rd  # this is the latest we can leave RH to hit 13:15 exactly.
    
    # Check if departure is possible given arrival time.
    if departure_from_rh < arrival_rh:
        raise ValueError("Not enough time to travel from Russian Hill to Richmond District before Barbara arrives.")
    
    # The meeting with Barbara can start when she becomes available.
    meeting_start = barbara_start
    meeting_end = meeting_start + meeting_min_duration
    
    # Ensure that the meeting_end does not exceed Barbara's availability.
    if meeting_end > barbara_end:
        raise ValueError("Barbara's available time is not long enough for the minimum meeting duration.")
    
    # We have computed an optimal schedule to meet Barbara:
    # Depart Russian Hill at departure_from_rh (though not an itinerary meeting event)
    # Arrive at Richmond District at barbara_start and meet her from barbara_start to meeting_end.
    
    itinerary = []
    # Add meeting with Barbara as our itinerary event.
    itinerary.append({
        "action": "meet",
        "location": "Richmond District",
        "person": "Barbara",
        "start_time": minutes_to_time(meeting_start),
        "end_time": minutes_to_time(meeting_end)
    })
    
    # Result dictionary
    result = {
        "itinerary": itinerary
    }
    
    # Print output as JSON formatted string.
    print(json.dumps(result, indent=2))
    
if __name__ == "__main__":
    main()