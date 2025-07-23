import json

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input data (same as before)
locations = [
    "The Castro", "North Beach", "Golden Gate Park", "Embarcadero", "Haight-Ashbury",
    "Richmond District", "Nob Hill", "Marina District", "Presidio", "Union Square", "Financial District"
]

travel_times = {
    # (same travel times dictionary as before)
}

friends = [
    # (same friends list as before)
]

def get_travel_time(from_loc, to_loc):
    return travel_times.get((from_loc, to_loc), float('inf'))

def find_feasible_schedule():
    # Sort friends by their end time (earlier first)
    sorted_friends = sorted(friends, key=lambda x: time_to_minutes(x["end"]))
    
    schedule = []
    current_time = time_to_minutes("9:00")
    current_location = "The Castro"
    
    for friend in sorted_friends:
        location = friend["location"]
        start_time = time_to_minutes(friend["start"])
        end_time = time_to_minutes(friend["end"])
        duration = friend["duration"]
        
        # Calculate travel time
        travel_time = get_travel_time(current_location, location)
        arrival_time = current_time + travel_time
        
        # Check if we can meet this friend
        if arrival_time <= end_time:
            meeting_start = max(arrival_time, start_time)
            meeting_end = meeting_start + duration
            
            if meeting_end <= end_time:
                schedule.append({
                    "person": friend["name"],
                    "location": location,
                    "start": friend["start"],
                    "end": friend["end"],
                    "duration": duration
                })
                current_time = meeting_end
                current_location = location
    
    return schedule

def schedule_to_itinerary(schedule):
    itinerary = []
    current_time = time_to_minutes("9:00")
    current_location = "The Castro"
    
    for meeting in schedule:
        travel_time = get_travel_time(current_location, meeting["location"])
        arrival_time = current_time + travel_time
        start_time = time_to_minutes(meeting["start"])
        end_time = time_to_minutes(meeting["end"])
        duration = meeting["duration"]
        
        meeting_start = max(arrival_time, start_time)
        meeting_end = meeting_start + duration
        
        itinerary.append({
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["person"],
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        
        current_time = meeting_end
        current_location = meeting["location"]
    
    return itinerary

# Find a feasible schedule
feasible_schedule = find_feasible_schedule()

if feasible_schedule:
    itinerary = schedule_to_itinerary(feasible_schedule)
    result = {"itinerary": itinerary}
else:
    result = {"itinerary": []}

print(json.dumps(result, indent=2))