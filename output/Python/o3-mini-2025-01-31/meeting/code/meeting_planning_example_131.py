#!/usr/bin/env python3
import json
from datetime import datetime, timedelta

def time_to_minutes(time_str):
    """Convert a time string in H:MM format to minutes after midnight."""
    t = datetime.strptime(time_str, "%H:%M")
    return t.hour * 60 + t.minute

def minutes_to_time(minutes):
    """Convert minutes after midnight to a time string in H:MM format (24-hour)."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Input parameters and constraints (in minutes)
    # Travel times (in minutes)
    travel = {
        ("Pacific Heights", "Presidio"): 11,
        ("Pacific Heights", "Marina District"): 6,
        ("Presidio", "Pacific Heights"): 11,
        ("Presidio", "Marina District"): 10,
        ("Marina District", "Pacific Heights"): 7,
        ("Marina District", "Presidio"): 10
    }
    
    # Meeting constraints and availability times (in minutes after midnight)
    start_location = "Pacific Heights"
    arrival_time = time_to_minutes("9:00")
    
    # Jason's availability at Presidio
    jason_location = "Presidio"
    jason_available_start = time_to_minutes("10:00")
    jason_available_end = time_to_minutes("16:15")
    jason_min_duration = 90  # minutes
    
    # Kenneth's availability at Marina District
    kenneth_location = "Marina District"
    kenneth_available_start = time_to_minutes("15:30")
    kenneth_available_end = time_to_minutes("16:45")
    kenneth_min_duration = 45  # minutes

    # Compute the optimal schedule:
    # Our goal is to meet both Jason and Kenneth.
    # Step 1: Travel from Pacific Heights (starting point) to Presidio to meet Jason.
    time_depart_PH_for_Presidio = arrival_time
    travel_time_PH_to_Presidio = travel[(start_location, jason_location)]
    arrival_Presidio = time_depart_PH_for_Presidio + travel_time_PH_to_Presidio
    # Wait until Jason is available (if needed)
    meeting_jason_start = max(arrival_Presidio, jason_available_start)
    
    # Step 2: Schedule meeting with Jason.
    # Before meeting Kenneth, we need to be at Marina District by kenneth_available_start.
    # We are meeting Jason at Presidio and travel from Presidio to Marina District takes:
    travel_time_Presidio_to_Marina = travel[(jason_location, kenneth_location)]
    # To start Kenneth's meeting at kenneth_available_start, we must depart Presidio by:
    depart_Presidio_for_Marina = kenneth_available_start - travel_time_Presidio_to_Marina
    
    # Ensure the meeting with Jason is at least his minimum required duration.
    # We can extend the meeting until depart_Presidio_for_Marina if possible respecting Jason's availability end.
    meeting_jason_end = min(depart_Presidio_for_Marina, jason_available_end)
    duration_jason = meeting_jason_end - meeting_jason_start
    
    if duration_jason < jason_min_duration:
        # Not enough time for Jason meeting given travel constraints.
        raise ValueError("Cannot schedule Jason's meeting with the required duration given travel constraints.")
    
    # Step 3: Travel from Presidio to Marina District for Kenneth's meeting.
    arrival_Marina = depart_Presidio_for_Marina + travel_time_Presidio_to_Marina
    
    # Step 4: Schedule meeting with Kenneth.
    # Kenneth is available from kenneth_available_start, so meeting starts at the later of arrival or availability.
    meeting_kenneth_start = max(arrival_Marina, kenneth_available_start)
    # We want to meet him for at least kenneth_min_duration and within his available time.
    meeting_kenneth_end = meeting_kenneth_start + kenneth_min_duration
    if meeting_kenneth_end > kenneth_available_end:
        raise ValueError("Cannot schedule Kenneth's meeting with the required duration within his availability.")
    
    itinerary = [
        {
            "action": "meet",
            "location": jason_location,
            "person": "Jason",
            "start_time": minutes_to_time(meeting_jason_start),
            "end_time": minutes_to_time(meeting_jason_end)
        },
        {
            "action": "meet",
            "location": kenneth_location,
            "person": "Kenneth",
            "start_time": minutes_to_time(meeting_kenneth_start),
            "end_time": minutes_to_time(meeting_kenneth_end)
        }
    ]
    
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()