import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Travel times dictionary: travel_times[from][to] = minutes
travel_times = {
    "Haight-Ashbury": {
        "Mission District": 11,
        "Union Square": 19,
        "Pacific Heights": 12,
        "Bayview": 18,
        "Fisherman's Wharf": 23,
        "Marina District": 17,
        "Richmond District": 10,
        "Sunset District": 15,
        "Golden Gate Park": 7
    },
    "Mission District": {
        "Haight-Ashbury": 12,
        "Union Square": 15,
        "Pacific Heights": 16,
        "Bayview": 14,
        "Fisherman's Wharf": 22,
        "Marina District": 19,
        "Richmond District": 20,
        "Sunset District": 24,
        "Golden Gate Park": 17
    },
    "Union Square": {
        "Haight-Ashbury": 18,
        "Mission District": 14,
        "Pacific Heights": 15,
        "Bayview": 15,
        "Fisherman's Wharf": 15,
        "Marina District": 18,
        "Richmond District": 20,
        "Sunset District": 27,
        "Golden Gate Park": 22
    },
    "Pacific Heights": {
        "Haight-Ashbury": 11,
        "Mission District": 15,
        "Union Square": 12,
        "Bayview": 22,
        "Fisherman's Wharf": 13,
        "Marina District": 6,
        "Richmond District": 12,
        "Sunset District": 21,
        "Golden Gate Park": 15
    },
    "Bayview": {
        "Haight-Ashbury": 19,
        "Mission District": 13,
        "Union Square": 18,
        "Pacific Heights": 23,
        "Fisherman's Wharf": 25,
        "Marina District": 27,
        "Richmond District": 25,
        "Sunset District": 23,
        "Golden Gate Park": 22
    },
    "Fisherman's Wharf": {
        "Haight-Ashbury": 22,
        "Mission District": 22,
        "Union Square": 13,
        "Pacific Heights": 12,
        "Bayview": 26,
        "Marina District": 9,
        "Richmond District": 18,
        "Sunset District": 27,
        "Golden Gate Park": 25
    },
    "Marina District": {
        "Haight-Ashbury": 16,
        "Mission District": 20,
        "Union Square": 16,
        "Pacific Heights": 7,
        "Bayview": 27,
        "Fisherman's Wharf": 10,
        "Richmond District": 11,
        "Sunset District": 19,
        "Golden Gate Park": 18
    },
    "Richmond District": {
        "Haight-Ashbury": 10,
        "Mission District": 20,
        "Union Square": 21,
        "Pacific Heights": 10,
        "Bayview": 27,
        "Fisherman's Wharf": 18,
        "Marina District": 9,
        "Sunset District": 11,
        "Golden Gate Park": 9
    },
    "Sunset District": {
        "Haight-Ashbury": 15,
        "Mission District": 25,
        "Union Square": 30,
        "Pacific Heights": 21,
        "Bayview": 22,
        "Fisherman's Wharf": 29,
        "Marina District": 21,
        "Richmond District": 12,
        "Golden Gate Park": 11
    },
    "Golden Gate Park": {
        "Haight-Ashbury": 7,
        "Mission District": 17,
        "Union Square": 22,
        "Pacific Heights": 16,
        "Bayview": 23,
        "Fisherman's Wharf": 24,
        "Marina District": 16,
        "Richmond District": 7,
        "Sunset District": 10
    }
}

# Friends data: name: [location, available_start, available_end, min_duration]
friends = {
    "Elizabeth": ["Mission District", "10:30", "20:00", 90],
    "David": ["Union Square", "15:15", "19:00", 45],
    "Sandra": ["Pacific Heights", "7:00", "20:00", 120],
    "Thomas": ["Bayview", "19:30", "20:30", 30],
    "Robert": ["Fisherman's Wharf", "10:00", "15:00", 15],
    "Kenneth": ["Marina District", "10:45", "13:00", 45],
    "Melissa": ["Richmond District", "18:15", "20:00", 30],
    "Kimberly": ["Sunset District", "10:15", "18:15", 105],
    "Amanda": ["Golden Gate Park", "7:45", "18:45", 30]
}

def calculate_schedule(order):
    current_location = "Haight-Ashbury"
    current_time = time_to_minutes("9:00")
    schedule = []
    
    for friend in order:
        location = friends[friend][0]
        available_start = time_to_minutes(friends[friend][1])
        available_end = time_to_minutes(friends[friend][2])
        min_duration = friends[friend][3]
        
        # Travel time
        travel_time = travel_times[current_location].get(location, 0)
        arrival_time = current_time + travel_time
        
        # Calculate meeting window
        meeting_start = max(arrival_time, available_start)
        meeting_end = meeting_start + min_duration
        
        if meeting_end > available_end:
            continue  # Skip this friend if we can't meet them
        
        # Ensure at least 5 minutes between meetings for buffer
        if schedule and (meeting_start - time_to_minutes(schedule[-1]["end_time"]) < 5):
            continue
            
        schedule.append({
            "action": "meet",
            "location": location,
            "person": friend,
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        
        current_time = meeting_end
        current_location = location
    
    return schedule

def evaluate_schedule(schedule):
    if not schedule:
        return 0
    
    # Count number of friends met
    num_friends = len(schedule)
    
    # Calculate total time used (earlier is better)
    last_meeting_end = time_to_minutes(schedule[-1]["end_time"])
    time_score = 1440 - last_meeting_end  # Higher is better
    
    return num_friends * 1000 + time_score  # Prioritize number of friends met

def generate_best_schedule():
    best_schedule = []
    best_score = 0
    
    # Try all possible orders (but limit to reasonable permutations)
    for order in permutations(friends.keys()):
        schedule = calculate_schedule(order)
        score = evaluate_schedule(schedule)
        
        if score > best_score:
            best_score = score
            best_schedule = schedule
            if len(best_schedule) == len(friends):
                break  # Found optimal solution
    
    return best_schedule

best_schedule = generate_best_schedule()

result = {
    "itinerary": best_schedule
}

print(json.dumps(result, indent=2))