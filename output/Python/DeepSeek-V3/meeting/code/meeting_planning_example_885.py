import json
from itertools import permutations

# Travel times dictionary (from -> to -> minutes)
travel_times = {
    "Russian Hill": {
        "Marina District": 7,
        "Financial District": 11,
        "Alamo Square": 15,
        "Golden Gate Park": 21,
        "The Castro": 21,
        "Bayview": 23,
        "Sunset District": 23,
        "Haight-Ashbury": 17,
        "Nob Hill": 5
    },
    "Marina District": {
        "Russian Hill": 8,
        "Financial District": 17,
        "Alamo Square": 15,
        "Golden Gate Park": 18,
        "The Castro": 22,
        "Bayview": 27,
        "Sunset District": 19,
        "Haight-Ashbury": 16,
        "Nob Hill": 12
    },
    "Financial District": {
        "Russian Hill": 11,
        "Marina District": 15,
        "Alamo Square": 17,
        "Golden Gate Park": 23,
        "The Castro": 20,
        "Bayview": 19,
        "Sunset District": 30,
        "Haight-Ashbury": 19,
        "Nob Hill": 8
    },
    "Alamo Square": {
        "Russian Hill": 13,
        "Marina District": 15,
        "Financial District": 17,
        "Golden Gate Park": 9,
        "The Castro": 8,
        "Bayview": 16,
        "Sunset District": 16,
        "Haight-Ashbury": 5,
        "Nob Hill": 11
    },
    "Golden Gate Park": {
        "Russian Hill": 19,
        "Marina District": 16,
        "Financial District": 26,
        "Alamo Square": 9,
        "The Castro": 13,
        "Bayview": 23,
        "Sunset District": 10,
        "Haight-Ashbury": 7,
        "Nob Hill": 20
    },
    "The Castro": {
        "Russian Hill": 18,
        "Marina District": 21,
        "Financial District": 21,
        "Alamo Square": 8,
        "Golden Gate Park": 11,
        "Bayview": 19,
        "Sunset District": 17,
        "Haight-Ashbury": 6,
        "Nob Hill": 16
    },
    "Bayview": {
        "Russian Hill": 23,
        "Marina District": 27,
        "Financial District": 19,
        "Alamo Square": 16,
        "Golden Gate Park": 22,
        "The Castro": 19,
        "Sunset District": 23,
        "Haight-Ashbury": 19,
        "Nob Hill": 20
    },
    "Sunset District": {
        "Russian Hill": 24,
        "Marina District": 21,
        "Financial District": 30,
        "Alamo Square": 17,
        "Golden Gate Park": 11,
        "The Castro": 17,
        "Bayview": 22,
        "Haight-Ashbury": 15,
        "Nob Hill": 27
    },
    "Haight-Ashbury": {
        "Russian Hill": 17,
        "Marina District": 17,
        "Financial District": 21,
        "Alamo Square": 5,
        "Golden Gate Park": 7,
        "The Castro": 6,
        "Bayview": 18,
        "Sunset District": 15,
        "Nob Hill": 15
    },
    "Nob Hill": {
        "Russian Hill": 5,
        "Marina District": 11,
        "Financial District": 9,
        "Alamo Square": 11,
        "Golden Gate Park": 17,
        "The Castro": 17,
        "Bayview": 19,
        "Sunset District": 24,
        "Haight-Ashbury": 13
    }
}

# Friend availability
friends = {
    "Mark": {
        "location": "Marina District",
        "start": 18.75,  # 6:45 PM
        "end": 21.0,     # 9:00 PM
        "duration": 1.5  # 90 minutes
    },
    "Karen": {
        "location": "Financial District",
        "start": 9.5,    # 9:30 AM
        "end": 12.75,    # 12:45 PM
        "duration": 1.5
    },
    "Barbara": {
        "location": "Alamo Square",
        "start": 10.0,  # 10:00 AM
        "end": 19.5,     # 7:30 PM
        "duration": 1.5
    },
    "Nancy": {
        "location": "Golden Gate Park",
        "start": 16.75,  # 4:45 PM
        "end": 20.0,     # 8:00 PM
        "duration": 1.75 # 105 minutes
    },
    "David": {
        "location": "The Castro",
        "start": 9.0,    # 9:00 AM
        "end": 18.0,     # 6:00 PM
        "duration": 2.0  # 120 minutes
    },
    "Linda": {
        "location": "Bayview",
        "start": 18.25,  # 6:15 PM
        "end": 19.75,    # 7:45 PM
        "duration": 0.75 # 45 minutes
    },
    "Kevin": {
        "location": "Sunset District",
        "start": 10.0,  # 10:00 AM
        "end": 17.75,    # 5:45 PM
        "duration": 2.0
    },
    "Matthew": {
        "location": "Haight-Ashbury",
        "start": 10.25,  # 10:15 AM
        "end": 15.5,     # 3:30 PM
        "duration": 0.75
    },
    "Andrew": {
        "location": "Nob Hill",
        "start": 11.75, # 11:45 AM
        "end": 16.75,    # 4:45 PM
        "duration": 1.75
    }
}

def time_to_float(time_str):
    """Convert time string (H:MM) to float (H.MM)"""
    h, m = map(int, time_str.split(':'))
    return h + m / 60.0

def float_to_time(time_float):
    """Convert float (H.MM) to time string (H:MM)"""
    h = int(time_float)
    m = int(round((time_float - h) * 60))
    if m == 60:
        h += 1
        m = 0
    return f"{h}:{m:02d}"

def get_travel_time(from_loc, to_loc):
    """Get travel time between two locations"""
    return travel_times[from_loc][to_loc] / 60.0  # Convert to hours

def is_schedule_valid(schedule):
    """Check if a schedule meets all constraints"""
    current_time = 9.0  # Start at Russian Hill at 9:00 AM
    current_loc = "Russian Hill"
    
    for meeting in schedule:
        # Travel to meeting location
        travel_time = get_travel_time(current_loc, meeting["location"])
        arrival_time = current_time + travel_time
        
        # Check if we can meet during their availability
        friend = friends[meeting["person"]]
        meeting_start = max(arrival_time, friend["start"])
        meeting_end = meeting_start + friend["duration"]
        
        if meeting_end > friend["end"]:
            return False  # Can't meet for required duration
        
        # Update current time and location
        current_time = meeting_end
        current_loc = meeting["location"]
        
        # Store meeting times
        meeting["start_time"] = meeting_start
        meeting["end_time"] = meeting_end
    
    return True

def evaluate_schedule(schedule):
    """Evaluate a schedule by counting meetings and total meeting time"""
    if not is_schedule_valid(schedule):
        return -1, -1
    
    total_meetings = len(schedule)
    total_time = sum(friends[m["person"]]["duration"] for m in schedule)
    return total_meetings, total_time

def generate_possible_schedules():
    """Generate possible schedules by trying different permutations"""
    friend_names = list(friends.keys())
    best_schedule = []
    best_meetings = 0
    best_time = 0
    
    # Try permutations of different lengths
    for r in range(1, len(friend_names) + 1):
        for perm in permutations(friend_names, r):
            # Create schedule in order of permutation
            schedule = [{"action": "meet", "location": friends[name]["location"], 
                         "person": name} for name in perm]
            
            # Evaluate schedule
            meetings, time = evaluate_schedule(schedule)
            
            # Update best schedule if better
            if meetings > best_meetings or (meetings == best_meetings and time > best_time):
                best_schedule = schedule
                best_meetings = meetings
                best_time = time
    
    return best_schedule

def main():
    # Generate the best possible schedule
    best_schedule = generate_possible_schedules()
    
    # Convert to output format
    itinerary = []
    for meeting in best_schedule:
        itinerary.append({
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["person"],
            "start_time": float_to_time(meeting["start_time"]),
            "end_time": float_to_time(meeting["end_time"])
        })
    
    # Output as JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    main()