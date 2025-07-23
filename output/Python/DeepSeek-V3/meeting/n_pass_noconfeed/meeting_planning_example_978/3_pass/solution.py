import json
from itertools import permutations

# Define travel times between locations in minutes
travel_times = {
    "Embarcadero": {
        "Embarcadero": 0,
        "Union Square": 10,
        "China Town": 15,
        "Mission District": 20,
        "Twitch HQ": 25,
        "Dogpatch": 30
    },
    "Union Square": {
        "Embarcadero": 10,
        "Union Square": 0,
        "China Town": 8,
        "Mission District": 15,
        "Twitch HQ": 20,
        "Dogpatch": 25
    },
    "China Town": {
        "Embarcadero": 15,
        "Union Square": 8,
        "China Town": 0,
        "Mission District": 10,
        "Twitch HQ": 15,
        "Dogpatch": 20
    },
    "Mission District": {
        "Embarcadero": 20,
        "Union Square": 15,
        "China Town": 10,
        "Mission District": 0,
        "Twitch HQ": 8,
        "Dogpatch": 12
    },
    "Twitch HQ": {
        "Embarcadero": 25,
        "Union Square": 20,
        "China Town": 15,
        "Mission District": 8,
        "Twitch HQ": 0,
        "Dogpatch": 6
    },
    "Dogpatch": {
        "Embarcadero": 30,
        "Union Square": 25,
        "China Town": 20,
        "Mission District": 12,
        "Twitch HQ": 6,
        "Dogpatch": 0
    }
}

# Define friends with their availability and meeting duration
friends = [
    {"name": "Alice", "location": "Union Square", "start": 9.5, "end": 11.0, "duration": 0.5},
    {"name": "Bob", "location": "China Town", "start": 10.0, "end": 12.0, "duration": 0.5},
    {"name": "Charlie", "location": "Mission District", "start": 11.0, "end": 13.0, "duration": 1.0},
    {"name": "Dana", "location": "Twitch HQ", "start": 11.5, "end": 14.0, "duration": 0.5},
    {"name": "Eve", "location": "Dogpatch", "start": 12.0, "end": 15.0, "duration": 1.0}
]

def time_to_float(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours + minutes / 60.0

def float_to_time(time_float):
    hours = int(time_float)
    minutes = int((time_float - hours) * 60)
    return f"{hours}:{minutes:02d}"

def get_travel_time(from_loc, to_loc):
    return travel_times[from_loc][to_loc] / 60.0

def is_schedule_valid(schedule):
    current_time = 9.0  # Start at Embarcadero at 9:00
    current_location = "Embarcadero"
    
    for meeting in schedule:
        # Travel to meeting location
        travel_time = get_travel_time(current_location, meeting["location"])
        arrival_time = current_time + travel_time
        
        # Check if we arrive before meeting window closes
        if arrival_time > meeting["end"]:
            return False
        
        # Calculate meeting start time (can't be before friend's availability)
        meeting_start = max(arrival_time, meeting["start"])
        
        # Check if we have enough time for the meeting
        meeting_end = meeting_start + meeting["duration"]
        if meeting_end > meeting["end"]:
            return False
        
        # Update current time and location
        current_time = meeting_end
        current_location = meeting["location"]
    
    return True

def calculate_score(schedule):
    # Score based on number of friends met and total meeting time
    total_duration = sum(m["duration"] for m in schedule)
    return len(schedule) * 100 + total_duration * 10

def generate_best_schedule():
    best_score = -1
    best_schedule = []
    
    # Try all possible orders (limited to 5 friends to keep computation feasible)
    for friend_subset in permutations(friends, 5):
        current_schedule = []
        current_time = 9.0
        current_location = "Embarcadero"
        valid = True
        
        for friend in friend_subset:
            travel_time = get_travel_time(current_location, friend["location"])
            arrival_time = current_time + travel_time
            
            if arrival_time > friend["end"]:
                valid = False
                break
                
            meeting_start = max(arrival_time, friend["start"])
            meeting_end = meeting_start + friend["duration"]
            
            if meeting_end > friend["end"]:
                valid = False
                break
                
            current_schedule.append({
                "name": friend["name"],
                "location": friend["location"],
                "start": meeting_start,
                "end": meeting_end,
                "duration": friend["duration"]
            })
            
            current_time = meeting_end
            current_location = friend["location"]
        
        if valid:
            score = calculate_score(current_schedule)
            if score > best_score:
                best_score = score
                best_schedule = current_schedule
    
    return best_schedule

def main():
    best_schedule = generate_best_schedule()
    
    itinerary = []
    for meeting in best_schedule:
        itinerary.append({
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["name"],
            "start_time": float_to_time(meeting["start"]),
            "end_time": float_to_time(meeting["end"])
        })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()