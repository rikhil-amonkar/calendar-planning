import json
from itertools import permutations
from datetime import datetime, timedelta

def parse_time(t_str):
    """Convert 'H:MM' or 'HH:MM' to datetime today for easy arithmetic."""
    return datetime.strptime(t_str, "%H:%M")

def format_time(dt):
    """Convert datetime to 'H:MM' or 'HH:MM' without leading zero on hour."""
    return dt.strftime("%-H:%M")

def add_minutes(dt, minutes):
    return dt + timedelta(minutes=minutes)

# Travel times matrix (in minutes)
travel_times = {
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Mission District"): 24,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Mission District"): 10,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Mission District"): 16,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Alamo Square"): 10,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Mission District"): 17,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Golden Gate Park"): 17,
}

# Friend data: name, location, available_start, available_end, min_duration (minutes)
friends = [
    ("Charles", "Alamo Square", parse_time("18:00"), parse_time("20:45"), 90),
    ("Margaret", "Russian Hill", parse_time("9:00"), parse_time("16:00"), 30),
    ("Daniel", "Golden Gate Park", parse_time("8:00"), parse_time("13:30"), 15),
    ("Stephanie", "Mission District", parse_time("20:30"), parse_time("22:00"), 90),
]

def schedule_meetings(order, start_time, start_loc):
    """Try to schedule meetings in given order, return (num_met, itinerary)."""
    current_time = start_time
    current_loc = start_loc
    itinerary = []
    met_count = 0
    
    for name, location, avail_start, avail_end, min_dur in order:
        # Travel to friend's location
        travel_key = (current_loc, location)
        if travel_key in travel_times:
            travel = travel_times[travel_key]
        else:
            travel = travel_times.get((current_loc, location), 0)
        current_time = add_minutes(current_time, travel)
        
        # Try to start meeting as soon as possible after arrival, but within window
        start_meeting = max(current_time, avail_start)
        if start_meeting > avail_end:
            # Cannot meet at all
            return 0, []
        end_meeting = add_minutes(start_meeting, min_dur)
        if end_meeting > avail_end:
            # Not enough time in window
            return 0, []
        
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": name,
            "start_time": format_time(start_meeting),
            "end_time": format_time(end_meeting)
        })
        met_count += 1
        current_time = end_meeting
        current_loc = location
    
    return met_count, itinerary

def main():
    start_time = parse_time("9:00")
    start_loc = "Sunset District"
    
    best_met = 0
    best_itinerary = []
    
    # Try all permutations of friends
    for perm in permutations(friends):
        met, itinerary = schedule_meetings(perm, start_time, start_loc)
        if met > best_met:
            best_met = met
            best_itinerary = itinerary
    
    # Output result
    result = {
        "itinerary": best_itinerary
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()