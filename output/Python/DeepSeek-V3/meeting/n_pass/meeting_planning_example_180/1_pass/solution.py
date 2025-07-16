import json
from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(dt):
    return dt.strftime("%-H:%M")

def calculate_schedule():
    # Input parameters
    travel_times = {
        ("North Beach", "Mission District"): 18,
        ("North Beach", "The Castro"): 22,
        ("Mission District", "North Beach"): 17,
        ("Mission District", "The Castro"): 7,
        ("The Castro", "North Beach"): 20,
        ("The Castro", "Mission District"): 7,
    }
    
    current_location = "North Beach"
    current_time = parse_time("9:00")
    
    james_available_start = parse_time("12:45")
    james_available_end = parse_time("14:00")
    james_min_duration = 75  # minutes
    
    robert_available_start = parse_time("12:45")
    robert_available_end = parse_time("15:15")
    robert_min_duration = 30  # minutes
    
    itinerary = []
    
    # We have two options: meet James first or Robert first
    
    # Option 1: Meet James first
    option1 = []
    time = current_time
    location = current_location
    
    # Travel to Mission District to meet James
    travel_time = travel_times[(location, "Mission District")]
    arrival_time = time + timedelta(minutes=travel_time)
    
    # Determine meeting time with James
    meeting_start = max(arrival_time, james_available_start)
    meeting_end = meeting_start + timedelta(minutes=james_min_duration)
    
    if meeting_end > james_available_end:
        option1 = None  # Not feasible
    else:
        option1.append({
            "action": "meet",
            "location": "Mission District",
            "person": "James",
            "start_time": format_time(meeting_start),
            "end_time": format_time(meeting_end)
        })
        
        # Travel to The Castro to meet Robert
        travel_time = travel_times[("Mission District", "The Castro")]
        arrival_time = meeting_end + timedelta(minutes=travel_time)
        
        # Determine meeting time with Robert
        meeting_start = max(arrival_time, robert_available_start)
        meeting_end = meeting_start + timedelta(minutes=robert_min_duration)
        
        if meeting_end > robert_available_end:
            option1 = None  # Not feasible
        else:
            option1.append({
                "action": "meet",
                "location": "The Castro",
                "person": "Robert",
                "start_time": format_time(meeting_start),
                "end_time": format_time(meeting_end)
            })
    
    # Option 2: Meet Robert first
    option2 = []
    time = current_time
    location = current_location
    
    # Travel to The Castro to meet Robert
    travel_time = travel_times[(location, "The Castro")]
    arrival_time = time + timedelta(minutes=travel_time)
    
    # Determine meeting time with Robert
    meeting_start = max(arrival_time, robert_available_start)
    meeting_end = meeting_start + timedelta(minutes=robert_min_duration)
    
    if meeting_end > robert_available_end:
        option2 = None  # Not feasible
    else:
        option2.append({
            "action": "meet",
            "location": "The Castro",
            "person": "Robert",
            "start_time": format_time(meeting_start),
            "end_time": format_time(meeting_end)
        })
        
        # Travel to Mission District to meet James
        travel_time = travel_times[("The Castro", "Mission District")]
        arrival_time = meeting_end + timedelta(minutes=travel_time)
        
        # Determine meeting time with James
        meeting_start = max(arrival_time, james_available_start)
        meeting_end = meeting_start + timedelta(minutes=james_min_duration)
        
        if meeting_end > james_available_end:
            option2 = None  # Not feasible
        else:
            option2.append({
                "action": "meet",
                "location": "Mission District",
                "person": "James",
                "start_time": format_time(meeting_start),
                "end_time": format_time(meeting_end)
            })
    
    # Determine which option is better (both meetings possible)
    best_option = None
    if option1 is not None and option2 is not None:
        # Both options work, choose the one that finishes earlier
        option1_end = parse_time(option1[-1]["end_time"])
        option2_end = parse_time(option2[-1]["end_time"])
        best_option = option1 if option1_end < option2_end else option2
    elif option1 is not None:
        best_option = option1
    elif option2 is not None:
        best_option = option2
    
    if best_option is None:
        # Try to meet at least one person
        # Try meeting James only
        time = current_time
        location = current_location
        travel_time = travel_times[(location, "Mission District")]
        arrival_time = time + timedelta(minutes=travel_time)
        meeting_start = max(arrival_time, james_available_start)
        meeting_end = meeting_start + timedelta(minutes=james_min_duration)
        if meeting_end <= james_available_end:
            best_option = [{
                "action": "meet",
                "location": "Mission District",
                "person": "James",
                "start_time": format_time(meeting_start),
                "end_time": format_time(meeting_end)
            }]
        else:
            # Try meeting Robert only
            time = current_time
            location = current_location
            travel_time = travel_times[(location, "The Castro")]
            arrival_time = time + timedelta(minutes=travel_time)
            meeting_start = max(arrival_time, robert_available_start)
            meeting_end = meeting_start + timedelta(minutes=robert_min_duration)
            if meeting_end <= robert_available_end:
                best_option = [{
                    "action": "meet",
                    "location": "The Castro",
                    "person": "Robert",
                    "start_time": format_time(meeting_start),
                    "end_time": format_time(meeting_end)
                }]
            else:
                best_option = []
    
    return {"itinerary": best_option}

if __name__ == "__main__":
    schedule = calculate_schedule()
    print(json.dumps(schedule, indent=2))