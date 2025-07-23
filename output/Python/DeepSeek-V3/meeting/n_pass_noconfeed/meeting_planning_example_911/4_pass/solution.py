import json

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input data
locations = [
    "The Castro", "North Beach", "Golden Gate Park", "Embarcadero", "Haight-Ashbury",
    "Richmond District", "Nob Hill", "Marina District", "Presidio", "Union Square", "Financial District"
]

travel_times = {
    ("The Castro", "North Beach"): 25,
    ("The Castro", "Golden Gate Park"): 20,
    ("The Castro", "Embarcadero"): 15,
    ("The Castro", "Haight-Ashbury"): 10,
    ("The Castro", "Richmond District"): 30,
    ("The Castro", "Nob Hill"): 20,
    ("The Castro", "Marina District"): 25,
    ("The Castro", "Presidio"): 35,
    ("The Castro", "Union Square"): 15,
    ("The Castro", "Financial District"): 20,
    # Add reverse directions and other connections as needed
    ("North Beach", "The Castro"): 25,
    ("Golden Gate Park", "The Castro"): 20,
    ("Embarcadero", "The Castro"): 15,
    ("Haight-Ashbury", "The Castro"): 10,
    # Add more connections to make the graph complete
    ("North Beach", "Embarcadero"): 10,
    ("Embarcadero", "North Beach"): 10,
    ("Union Square", "Financial District"): 5,
    ("Financial District", "Union Square"): 5,
    # Add more connections as needed
}

friends = [
    {"name": "Alice", "location": "North Beach", "start": "9:30", "end": "10:30", "duration": 30},
    {"name": "Bob", "location": "Golden Gate Park", "start": "10:00", "end": "11:30", "duration": 45},
    {"name": "Charlie", "location": "Embarcadero", "start": "11:00", "end": "12:30", "duration": 30},
    {"name": "Dana", "location": "Haight-Ashbury", "start": "10:30", "end": "11:30", "duration": 20},
    {"name": "Eve", "location": "Union Square", "start": "11:30", "end": "12:30", "duration": 30},
]

def get_travel_time(from_loc, to_loc):
    if from_loc == to_loc:
        return 0
    return travel_times.get((from_loc, to_loc), float('inf'))

def find_feasible_schedule():
    # Sort friends by their end time (earlier first) as primary key, then by start time
    sorted_friends = sorted(friends, key=lambda x: (time_to_minutes(x["end"]), time_to_minutes(x["start"])))
    
    schedule = []
    current_time = time_to_minutes("9:00")
    current_location = "The Castro"
    
    for friend in sorted_friends:
        location = friend["location"]
        start_window = time_to_minutes(friend["start"])
        end_window = time_to_minutes(friend["end"])
        duration = friend["duration"]
        
        # Calculate travel time
        travel_time = get_travel_time(current_location, location)
        arrival_time = current_time + travel_time
        
        # Calculate possible meeting start time
        meeting_start = max(arrival_time, start_window)
        meeting_end = meeting_start + duration
        
        # Check if we can meet this friend within their window
        if meeting_end <= end_window:
            # Add to schedule
            schedule.append({
                "person": friend["name"],
                "location": location,
                "start": minutes_to_time(meeting_start),
                "end": minutes_to_time(meeting_end),
                "duration": duration
            })
            current_time = meeting_end
            current_location = location
        else:
            # Try to see if we can arrive earlier by adjusting previous meetings
            # This is a simple backtracking attempt
            if schedule:
                # Try removing the last meeting to see if we can fit this one
                last_meeting = schedule[-1]
                if (time_to_minutes(last_meeting["end"]) - last_meeting["duration"] + 
                    get_travel_time(schedule[-2]["location"] if len(schedule) > 1 else "The Castro", location) <= end_window - duration):
                    # We can potentially rearrange, but for simplicity, we'll just skip
                    continue
    
    return schedule

def schedule_to_itinerary(schedule):
    itinerary = []
    current_time = time_to_minutes("9:00")
    current_location = "The Castro"
    
    for meeting in schedule:
        location = meeting["location"]
        travel_time = get_travel_time(current_location, location)
        
        # Add travel step
        if travel_time > 0:
            itinerary.append({
                "action": "travel",
                "from": current_location,
                "to": location,
                "start_time": minutes_to_time(current_time),
                "end_time": minutes_to_time(current_time + travel_time)
            })
            current_time += travel_time
        
        # Add meeting step
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": meeting["person"],
            "start_time": meeting["start"],
            "end_time": meeting["end"]
        })
        current_time = time_to_minutes(meeting["end"])
        current_location = location
    
    return itinerary

# Find a feasible schedule
feasible_schedule = find_feasible_schedule()

if feasible_schedule:
    itinerary = schedule_to_itinerary(feasible_schedule)
    result = {"itinerary": itinerary}
else:
    result = {"itinerary": []}

print(json.dumps(result, indent=2))