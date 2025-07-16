import json
from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(dt):
    return dt.strftime("%-H:%M")

def main():
    # Input parameters
    arrival_time = parse_time("9:00")
    current_location = "Nob Hill"
    
    # Friend constraints
    thomas_available_start = parse_time("15:30")
    thomas_available_end = parse_time("19:15")
    thomas_min_duration = timedelta(minutes=75)
    thomas_location = "Pacific Heights"
    
    kenneth_available_start = parse_time("12:00")
    kenneth_available_end = parse_time("15:45")
    kenneth_min_duration = timedelta(minutes=45)
    kenneth_location = "Mission District"
    
    # Travel times in minutes
    travel_times = {
        ("Nob Hill", "Pacific Heights"): 8,
        ("Nob Hill", "Mission District"): 13,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "Mission District"): 15,
        ("Mission District", "Nob Hill"): 12,
        ("Mission District", "Pacific Heights"): 16,
    }
    
    # Possible meeting orders
    possible_orders = [
        ["Kenneth", "Thomas"],
        ["Thomas", "Kenneth"],
    ]
    
    best_schedule = None
    max_meetings = 0
    
    for order in possible_orders:
        current_time = arrival_time
        location = current_location
        schedule = []
        meetings = 0
        
        for person in order:
            if person == "Kenneth":
                available_start = kenneth_available_start
                available_end = kenneth_available_end
                min_duration = kenneth_min_duration
                target_location = kenneth_location
            else:
                available_start = thomas_available_start
                available_end = thomas_available_end
                min_duration = thomas_min_duration
                target_location = thomas_location
            
            # Travel to the location
            travel_key = (location, target_location)
            travel_duration = timedelta(minutes=travel_times[travel_key])
            arrival_at_target = current_time + travel_duration
            
            # Calculate meeting window
            meeting_start = max(arrival_at_target, available_start)
            meeting_end = min(meeting_start + min_duration, available_end)
            
            if meeting_end > meeting_start:
                # Add meeting to schedule
                schedule.append({
                    "action": "meet",
                    "location": target_location,
                    "person": person,
                    "start_time": format_time(meeting_start),
                    "end_time": format_time(meeting_end)
                })
                meetings += 1
                current_time = meeting_end
                location = target_location
        
        if meetings > max_meetings or (meetings == max_meetings and best_schedule is None):
            max_meetings = meetings
            best_schedule = schedule
    
    # Output the best schedule
    output = {
        "itinerary": best_schedule
    }
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()