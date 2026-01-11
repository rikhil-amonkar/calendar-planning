import json

def minutes_to_time(minutes):
    """Convert minutes since 9:00 to HH:MM 24-hour format"""
    total_minutes = 9 * 60 + minutes
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h}:{m:02d}"

def time_to_minutes(time_str):
    """Convert HH:MM to minutes since midnight"""
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def main():
    # Travel times in minutes
    travel = {
        ("Nob Hill", "Pacific Heights"): 8,
        ("Nob Hill", "Mission District"): 13,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "Mission District"): 15,
        ("Mission District", "Nob Hill"): 12,
        ("Mission District", "Pacific Heights"): 16,
    }
    
    # Convert all times to minutes since 9:00
    start_time = time_to_minutes("9:00")  # 540 minutes since midnight
    zero_offset = start_time  # we'll subtract this to get minutes since 9:00
    
    # Friend constraints in minutes since midnight
    thomas_start = time_to_minutes("15:30")
    thomas_end = time_to_minutes("19:15")
    kenneth_start = time_to_minutes("12:00")
    kenneth_end = time_to_minutes("15:45")
    
    # Minimum meeting durations in minutes
    min_thomas = 75
    min_kenneth = 45
    
    # Convert to minutes since 9:00
    thomas_start -= zero_offset
    thomas_end -= zero_offset
    kenneth_start -= zero_offset
    kenneth_end -= zero_offset
    
    # We start at Nob Hill at time 0 (minutes since 9:00)
    current_location = "Nob Hill"
    current_time = 0
    
    itinerary = []
    
    # --- Meet Kenneth first (only feasible order) ---
    # Travel to Mission District
    travel_time = travel[(current_location, "Mission District")]
    current_time += travel_time
    current_location = "Mission District"
    
    # Wait until Kenneth's start time if needed
    if current_time < kenneth_start:
        current_time = kenneth_start
    
    # Meet Kenneth as long as possible
    # We can meet until kenneth_end, but must leave time to travel to Thomas
    # and meet Thomas for at least 75 min before thomas_end
    
    # Latest we can leave Mission to meet Thomas:
    # Thomas needs min_thomas minutes, so we must start meeting Thomas by thomas_end - min_thomas
    latest_thomas_start = thomas_end - min_thomas
    # Travel to Pacific Heights takes 16 min
    latest_leave_mission = latest_thomas_start - travel[("Mission District", "Pacific Heights")]
    
    # Kenneth meeting must end by min(kenneth_end, latest_leave_mission)
    kenneth_meeting_end = min(kenneth_end, latest_leave_mission)
    kenneth_meeting_start = current_time
    kenneth_duration = kenneth_meeting_end - kenneth_meeting_start
    
    # Ensure minimum duration
    if kenneth_duration < min_kenneth:
        # Shift start earlier if possible
        kenneth_meeting_start = kenneth_meeting_end - min_kenneth
        if kenneth_meeting_start < kenneth_start:
            kenneth_meeting_start = kenneth_start
            kenneth_meeting_end = kenneth_meeting_start + min_kenneth
    
    # Add Kenneth meeting
    itinerary.append({
        "action": "meet",
        "location": "Mission District",
        "person": "Kenneth",
        "start_time": minutes_to_time(kenneth_meeting_start),
        "end_time": minutes_to_time(kenneth_meeting_end)
    })
    
    # Travel to Pacific Heights for Thomas
    current_time = kenneth_meeting_end
    travel_time = travel[("Mission District", "Pacific Heights")]
    current_time += travel_time
    current_location = "Pacific Heights"
    
    # Wait until Thomas's start time if needed
    if current_time < thomas_start:
        current_time = thomas_start
    
    # Meet Thomas as long as possible, but at least 75 min
    thomas_meeting_start = current_time
    thomas_meeting_end = min(thomas_start + (thomas_end - thomas_start), thomas_meeting_start + min_thomas)
    # Actually, let's just meet for exactly min_thomas to maximize Kenneth time
    thomas_meeting_end = thomas_meeting_start + min_thomas
    if thomas_meeting_end > thomas_end:
        thomas_meeting_end = thomas_end
        thomas_meeting_start = thomas_meeting_end - min_thomas
    
    # Add Thomas meeting
    itinerary.append({
        "action": "meet",
        "location": "Pacific Heights",
        "person": "Thomas",
        "start_time": minutes_to_time(thomas_meeting_start),
        "end_time": minutes_to_time(thomas_meeting_end)
    })
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()