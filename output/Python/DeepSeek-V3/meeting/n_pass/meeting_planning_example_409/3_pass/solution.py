import json
from itertools import permutations

# Travel times dictionary (from -> to -> minutes)
travel_times = {
    "Fisherman's Wharf": {
        "Bayview": 26,
        "Golden Gate Park": 25,
        "Nob Hill": 11,
        "Marina District": 9,
        "Embarcadero": 8
    },
    "Bayview": {
        "Fisherman's Wharf": 25,
        "Golden Gate Park": 22,
        "Nob Hill": 20,
        "Marina District": 25,
        "Embarcadero": 19
    },
    "Golden Gate Park": {
        "Fisherman's Wharf": 24,
        "Bayview": 23,
        "Nob Hill": 20,
        "Marina District": 16,
        "Embarcadero": 25
    },
    "Nob Hill": {
        "Fisherman's Wharf": 11,
        "Bayview": 19,
        "Golden Gate Park": 17,
        "Marina District": 11,
        "Embarcadero": 9
    },
    "Marina District": {
        "Fisherman's Wharf": 10,
        "Bayview": 27,
        "Golden Gate Park": 18,
        "Nob Hill": 12,
        "Embarcadero": 14
    },
    "Embarcadero": {
        "Fisherman's Wharf": 6,
        "Bayview": 21,
        "Golden Gate Park": 25,
        "Nob Hill": 10,
        "Marina District": 12
    }
}

# Friend availability
friends = {
    "Thomas": {
        "location": "Bayview",
        "start": 15.5,  # 3:30 PM
        "end": 18.5,    # 6:30 PM
        "min_duration": 2.0  # hours
    },
    "Stephanie": {
        "location": "Golden Gate Park",
        "start": 18.5,  # 6:30 PM
        "end": 21.75,   # 9:45 PM
        "min_duration": 0.5  # hours
    },
    "Laura": {
        "location": "Nob Hill",
        "start": 8.75,   # 8:45 AM
        "end": 16.25,    # 4:15 PM
        "min_duration": 0.5  # hours
    },
    "Betty": {
        "location": "Marina District",
        "start": 18.75,  # 6:45 PM
        "end": 21.75,    # 9:45 PM
        "min_duration": 0.75  # hours
    },
    "Patricia": {
        "location": "Embarcadero",
        "start": 17.5,   # 5:30 PM
        "end": 22.0,     # 10:00 PM
        "min_duration": 0.75  # hours
    }
}

def time_to_float(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours + minutes / 60.0

def float_to_time(time_float):
    hours = int(time_float)
    minutes = int((time_float - hours) * 60)
    return f"{hours}:{minutes:02d}"

def calculate_schedule(order):
    current_location = "Fisherman's Wharf"
    current_time = 9.0  # 9:00 AM
    schedule = []
    
    for friend_name in order:
        friend = friends[friend_name]
        location = friend["location"]
        
        # Calculate travel time
        travel_time = travel_times[current_location].get(location, float('inf')) / 60.0
        arrival_time = current_time + travel_time
        
        # Check if we can meet this friend
        meeting_start = max(arrival_time, friend["start"])
        meeting_end = meeting_start + friend["min_duration"]
        
        if meeting_end > friend["end"]:
            return None  # Can't meet this friend
        
        # Add travel action if needed
        if current_location != location:
            schedule.append({
                "action": "travel",
                "location": location,
                "start_time": float_to_time(current_time),
                "end_time": float_to_time(arrival_time)
            })
        
        # Add meeting action
        schedule.append({
            "action": "meet",
            "location": location,
            "person": friend_name,
            "start_time": float_to_time(meeting_start),
            "end_time": float_to_time(meeting_end)
        })
        
        current_time = meeting_end
        current_location = location
    
    return schedule

def evaluate_schedule(schedule):
    if not schedule:
        return -1
    # Count number of unique friends met
    friends_met = set()
    for item in schedule:
        if item["action"] == "meet":
            friends_met.add(item["person"])
    return len(friends_met)

def main():
    best_schedule = None
    best_score = -1
    
    # Try all possible orders of meeting friends
    for order in permutations(friends.keys()):
        schedule = calculate_schedule(order)
        score = evaluate_schedule(schedule)
        if score > best_score:
            best_score = score
            best_schedule = schedule
    
    # Prepare output
    output = {
        "itinerary": best_schedule if best_schedule else []
    }
    
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()