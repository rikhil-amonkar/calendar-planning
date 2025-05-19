#!/usr/bin/env python3
import json
from datetime import datetime, timedelta

def format_time(dt):
    # Format time as H:MM (no leading zeros for hour)
    return f"{dt.hour}:{dt.minute:02d}"

def main():
    # Input parameters and travel times (in minutes)
    arrival_castro_str = "9:00"
    travel_times = {
        ("The Castro", "Mission District"): 7,
        ("The Castro", "Financial District"): 20,
        ("Mission District", "The Castro"): 7,
        ("Mission District", "Financial District"): 17,
        ("Financial District", "The Castro"): 23,
        ("Financial District", "Mission District"): 17
    }
    
    # Constraints for Laura and Anthony:
    # Laura: available at Mission District from 12:15 to 19:45, minimum meeting duration 75 minutes.
    laura_available_start = datetime.strptime("12:15", "%H:%M")
    laura_available_end = datetime.strptime("19:45", "%H:%M")
    laura_min_duration = timedelta(minutes=75)
    
    # Anthony: available at Financial District from 12:30 to 14:45, minimum meeting duration 30 minutes.
    anthony_available_start = datetime.strptime("12:30", "%H:%M")
    anthony_available_end = datetime.strptime("14:45", "%H:%M")
    anthony_min_duration = timedelta(minutes=30)
    
    # Start time at The Castro
    start_time_castro = datetime.strptime(arrival_castro_str, "%H:%M")
    
    # We will compute the schedule that maximizes the number of friends.
    # Option considered: First meet Laura at Mission District, then meet Anthony at Financial District.
    
    # Travel: The Castro -> Mission District
    travel_castro_to_mission = timedelta(minutes= travel_times[("The Castro", "Mission District")] )
    arrival_mission = start_time_castro + travel_castro_to_mission
    
    # We can only start meeting Laura when she is available.
    meeting_laura_start = max(arrival_mission, laura_available_start)
    meeting_laura_end = meeting_laura_start + laura_min_duration
    
    # Check if meeting Laura finishes within her availability window.
    if meeting_laura_end > laura_available_end:
        raise ValueError("Cannot schedule a sufficient meeting with Laura within her available time.")
    
    # Travel: Mission District -> Financial District for Anthony meeting
    travel_mission_to_financial = timedelta(minutes= travel_times[("Mission District", "Financial District")] )
    arrival_financial = meeting_laura_end + travel_mission_to_financial
    
    # Start meeting Anthony when he is available.
    meeting_anthony_start = max(arrival_financial, anthony_available_start)
    meeting_anthony_end = anthony_available_end  # We use his availability end as end time, ensuring meeting is as long as possible
    
    # Check if there's enough time for Anthony meeting
    if meeting_anthony_end - meeting_anthony_start < anthony_min_duration:
        raise ValueError("Cannot schedule a sufficient meeting with Anthony within his available time.")
    
    # Build the itinerary
    itinerary = []
    
    # Add Laura meeting entry
    itinerary.append({
        "action": "meet",
        "location": "Mission District",
        "person": "Laura",
        "start_time": format_time(meeting_laura_start),
        "end_time": format_time(meeting_laura_end)
    })
    
    # Add Anthony meeting entry
    itinerary.append({
        "action": "meet",
        "location": "Financial District",
        "person": "Anthony",
        "start_time": format_time(meeting_anthony_start),
        "end_time": format_time(meeting_anthony_end)
    })
    
    result = {"itinerary": itinerary}
    
    # Output JSON formatted itinerary
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()