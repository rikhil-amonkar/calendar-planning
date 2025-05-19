import json
from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(dt):
    return dt.strftime("%-H:%M")

def calculate_schedule():
    # Input parameters
    arrival_time = parse_time("9:00")
    james_available_start = parse_time("12:45")
    james_available_end = parse_time("14:00")
    james_min_duration = timedelta(minutes=75)
    robert_available_start = parse_time("12:45")
    robert_available_end = parse_time("15:15")
    robert_min_duration = timedelta(minutes=30)
    
    # Travel times in minutes
    travel_times = {
        ("North Beach", "Mission District"): 18,
        ("North Beach", "The Castro"): 22,
        ("Mission District", "North Beach"): 17,
        ("Mission District", "The Castro"): 7,
        ("The Castro", "North Beach"): 20,
        ("The Castro", "Mission District"): 7,
    }
    
    # Possible schedules
    best_schedule = []
    max_meetings = 0
    
    # Option 1: Meet James only
    current_location = "North Beach"
    current_time = arrival_time
    
    # Travel to Mission District to meet James
    travel_time = travel_times[(current_location, "Mission District")]
    arrival_at_james = current_time + timedelta(minutes=travel_time)
    
    if arrival_at_james <= james_available_end - james_min_duration:
        meet_james_start = max(arrival_at_james, james_available_start)
        meet_james_end = meet_james_start + james_min_duration
        if meet_james_end <= james_available_end:
            schedule = [
                {"action": "meet", "location": "Mission District", "person": "James", 
                 "start_time": format_time(meet_james_start), "end_time": format_time(meet_james_end)}
            ]
            if len(schedule) > max_meetings:
                best_schedule = schedule
                max_meetings = len(schedule)
    
    # Option 2: Meet Robert only
    current_location = "North Beach"
    current_time = arrival_time
    
    # Travel to The Castro to meet Robert
    travel_time = travel_times[(current_location, "The Castro")]
    arrival_at_robert = current_time + timedelta(minutes=travel_time)
    
    if arrival_at_robert <= robert_available_end - robert_min_duration:
        meet_robert_start = max(arrival_at_robert, robert_available_start)
        meet_robert_end = meet_robert_start + robert_min_duration
        if meet_robert_end <= robert_available_end:
            schedule = [
                {"action": "meet", "location": "The Castro", "person": "Robert", 
                 "start_time": format_time(meet_robert_start), "end_time": format_time(meet_robert_end)}
            ]
            if len(schedule) > max_meetings:
                best_schedule = schedule
                max_meetings = len(schedule)
    
    # Option 3: Meet both (James first)
    current_location = "North Beach"
    current_time = arrival_time
    
    # Travel to Mission District to meet James
    travel_time = travel_times[(current_location, "Mission District")]
    arrival_at_james = current_time + timedelta(minutes=travel_time)
    
    if arrival_at_james <= james_available_end - james_min_duration:
        meet_james_start = max(arrival_at_james, james_available_start)
        meet_james_end = meet_james_start + james_min_duration
        if meet_james_end <= james_available_end:
            # Travel to The Castro to meet Robert
            travel_time = travel_times[("Mission District", "The Castro")]
            arrival_at_robert = meet_james_end + timedelta(minutes=travel_time)
            
            if arrival_at_robert <= robert_available_end - robert_min_duration:
                meet_robert_start = max(arrival_at_robert, robert_available_start)
                meet_robert_end = meet_robert_start + robert_min_duration
                if meet_robert_end <= robert_available_end:
                    schedule = [
                        {"action": "meet", "location": "Mission District", "person": "James", 
                         "start_time": format_time(meet_james_start), "end_time": format_time(meet_james_end)},
                        {"action": "meet", "location": "The Castro", "person": "Robert", 
                         "start_time": format_time(meet_robert_start), "end_time": format_time(meet_robert_end)}
                    ]
                    if len(schedule) > max_meetings:
                        best_schedule = schedule
                        max_meetings = len(schedule)
    
    # Option 4: Meet both (Robert first)
    current_location = "North Beach"
    current_time = arrival_time
    
    # Travel to The Castro to meet Robert
    travel_time = travel_times[(current_location, "The Castro")]
    arrival_at_robert = current_time + timedelta(minutes=travel_time)
    
    if arrival_at_robert <= robert_available_end - robert_min_duration:
        meet_robert_start = max(arrival_at_robert, robert_available_start)
        meet_robert_end = meet_robert_start + robert_min_duration
        if meet_robert_end <= robert_available_end:
            # Travel to Mission District to meet James
            travel_time = travel_times[("The Castro", "Mission District")]
            arrival_at_james = meet_robert_end + timedelta(minutes=travel_time)
            
            if arrival_at_james <= james_available_end - james_min_duration:
                meet_james_start = max(arrival_at_james, james_available_start)
                meet_james_end = meet_james_start + james_min_duration
                if meet_james_end <= james_available_end:
                    schedule = [
                        {"action": "meet", "location": "The Castro", "person": "Robert", 
                         "start_time": format_time(meet_robert_start), "end_time": format_time(meet_robert_end)},
                        {"action": "meet", "location": "Mission District", "person": "James", 
                         "start_time": format_time(meet_james_start), "end_time": format_time(meet_james_end)}
                    ]
                    if len(schedule) > max_meetings:
                        best_schedule = schedule
                        max_meetings = len(schedule)
    
    return {"itinerary": best_schedule}

if __name__ == "__main__":
    schedule = calculate_schedule()
    print(json.dumps(schedule, indent=2))