import json

def time_to_minutes(timestr):
    """Convert 'H:MM' to minutes since midnight."""
    hours, minutes = map(int, timestr.split(':'))
    return hours * 60 + minutes

def minutes_to_time(m):
    """Convert minutes since midnight to 'H:MM' format."""
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

def main():
    # Travel times in minutes: from_index to to_index
    # Locations: 0=North Beach, 1=Pacific Heights, 2=Embarcadero
    travel = [
        [0, 8, 6],   # from North Beach
        [9, 0, 10],  # from Pacific Heights
        [5, 11, 0]   # from Embarcadero
    ]
    
    # Start
    current_location = 0  # North Beach
    current_time = time_to_minutes("9:00")
    
    # Karen: Pacific Heights (index 1)
    karen_start = time_to_minutes("18:45")
    karen_end = time_to_minutes("20:15")
    karen_duration = 90  # minutes
    
    # Mark: Embarcadero (index 2)
    mark_start = time_to_minutes("13:00")
    mark_end = time_to_minutes("17:45")
    mark_duration = 120  # minutes
    
    # We'll try meeting Mark first, then Karen
    # Possible start times for Mark (in 15-minute increments)
    possible_mark_starts = []
    start = mark_start
    while start + mark_duration <= mark_end:
        possible_mark_starts.append(start)
        start += 15  # check every 15 minutes
    
    valid_schedules = []
    
    for m_start in possible_mark_starts:
        m_end = m_start + mark_duration
        
        # Travel from current_location (North Beach) to Embarcadero for Mark
        travel_to_mark = travel[current_location][2]  # to Embarcadero
        arrival_at_mark = current_time + travel_to_mark
        
        # We can arrive earlier and wait until m_start
        if arrival_at_mark > m_start:
            # Can't arrive after meeting start; invalid
            continue
        
        # After Mark, travel to Pacific Heights for Karen
        travel_to_karen = travel[2][1]  # from Embarcadero to Pacific Heights
        arrival_at_karen = m_end + travel_to_karen
        
        if arrival_at_karen > karen_start:
            # Too late for Karen's start; need to be there by karen_start
            # Actually, we can wait if we arrive earlier, but if later, invalid
            # We must be ready to start meeting at karen_start exactly
            # So arrival_at_karen must be <= karen_start
            continue
        
        # Karen's meeting is fixed 18:45-20:15
        k_meeting_start = karen_start
        k_meeting_end = karen_start + karen_duration
        
        if k_meeting_end > karen_end:
            continue  # shouldn't happen given inputs
        
        # Valid schedule found
        valid_schedules.append({
            "mark_start": m_start,
            "mark_end": m_end,
            "karen_start": k_meeting_start,
            "karen_end": k_meeting_end,
            "arrival_at_karen": arrival_at_karen,
            "idle_before_karen": karen_start - arrival_at_karen
        })
    
    # Pick first valid schedule (earliest Mark meeting)
    if not valid_schedules:
        print("No valid schedule found")
        return
    
    chosen = valid_schedules[0]
    
    # Build itinerary
    itinerary = []
    
    # Meeting Mark
    itinerary.append({
        "action": "meet",
        "location": "Embarcadero",
        "person": "Mark",
        "start_time": minutes_to_time(chosen["mark_start"]),
        "end_time": minutes_to_time(chosen["mark_end"])
    })
    
    # Travel to Pacific Heights is not an "action" in output, just implied
    
    # Meeting Karen
    itinerary.append({
        "action": "meet",
        "location": "Pacific Heights",
        "person": "Karen",
        "start_time": minutes_to_time(chosen["karen_start"]),
        "end_time": minutes_to_time(chosen["karen_end"])
    })
    
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()