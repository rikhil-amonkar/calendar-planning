import json
from itertools import permutations

# Travel times dictionary
travel_times = {
    "Embarcadero": {
        "Fisherman's Wharf": 6,
        "Financial District": 5,
        "Russian Hill": 8,
        "Marina District": 12,
        "Richmond District": 21,
        "Pacific Heights": 11,
        "Haight-Ashbury": 21,
        "Presidio": 20,
        "Nob Hill": 10,
        "The Castro": 25
    },
    "Fisherman's Wharf": {
        "Embarcadero": 8,
        "Financial District": 11,
        "Russian Hill": 7,
        "Marina District": 9,
        "Richmond District": 18,
        "Pacific Heights": 12,
        "Haight-Ashbury": 22,
        "Presidio": 17,
        "Nob Hill": 11,
        "The Castro": 27
    },
    "Financial District": {
        "Embarcadero": 4,
        "Fisherman's Wharf": 10,
        "Russian Hill": 11,
        "Marina District": 15,
        "Richmond District": 21,
        "Pacific Heights": 13,
        "Haight-Ashbury": 19,
        "Presidio": 22,
        "Nob Hill": 8,
        "The Castro": 20
    },
    "Russian Hill": {
        "Embarcadero": 8,
        "Fisherman's Wharf": 7,
        "Financial District": 11,
        "Marina District": 7,
        "Richmond District": 14,
        "Pacific Heights": 7,
        "Haight-Ashbury": 17,
        "Presidio": 14,
        "Nob Hill": 5,
        "The Castro": 21
    },
    "Marina District": {
        "Embarcadero": 14,
        "Fisherman's Wharf": 10,
        "Financial District": 17,
        "Russian Hill": 8,
        "Richmond District": 11,
        "Pacific Heights": 7,
        "Haight-Ashbury": 16,
        "Presidio": 10,
        "Nob Hill": 12,
        "The Castro": 22
    },
    "Richmond District": {
        "Embarcadero": 19,
        "Fisherman's Wharf": 18,
        "Financial District": 22,
        "Russian Hill": 13,
        "Marina District": 9,
        "Pacific Heights": 10,
        "Haight-Ashbury": 10,
        "Presidio": 7,
        "Nob Hill": 17,
        "The Castro": 16
    },
    "Pacific Heights": {
        "Embarcadero": 10,
        "Fisherman's Wharf": 13,
        "Financial District": 13,
        "Russian Hill": 7,
        "Marina District": 6,
        "Richmond District": 12,
        "Haight-Ashbury": 11,
        "Presidio": 11,
        "Nob Hill": 8,
        "The Castro": 16
    },
    "Haight-Ashbury": {
        "Embarcadero": 20,
        "Fisherman's Wharf": 23,
        "Financial District": 21,
        "Russian Hill": 17,
        "Marina District": 17,
        "Richmond District": 10,
        "Pacific Heights": 12,
        "Presidio": 15,
        "Nob Hill": 15,
        "The Castro": 6
    },
    "Presidio": {
        "Embarcadero": 20,
        "Fisherman's Wharf": 19,
        "Financial District": 23,
        "Russian Hill": 14,
        "Marina District": 11,
        "Richmond District": 7,
        "Pacific Heights": 11,
        "Haight-Ashbury": 15,
        "Nob Hill": 18,
        "The Castro": 21
    },
    "Nob Hill": {
        "Embarcadero": 9,
        "Fisherman's Wharf": 10,
        "Financial District": 9,
        "Russian Hill": 5,
        "Marina District": 11,
        "Richmond District": 14,
        "Pacific Heights": 8,
        "Haight-Ashbury": 13,
        "Presidio": 17,
        "The Castro": 16
    },
    "The Castro": {
        "Embarcadero": 22,
        "Fisherman's Wharf": 24,
        "Financial District": 21,
        "Russian Hill": 18,
        "Marina District": 21,
        "Richmond District": 16,
        "Pacific Heights": 16,
        "Haight-Ashbury": 6,
        "Presidio": 20,
        "Nob Hill": 16
    }
}

# Friend constraints
friends = [
    {"name": "Stephanie", "location": "Fisherman's Wharf", "start": 15.5, "end": 22.0, "duration": 0.5},
    {"name": "Lisa", "location": "Financial District", "start": 10.75, "end": 17.25, "duration": 0.25},
    {"name": "Melissa", "location": "Russian Hill", "start": 17.0, "end": 21.75, "duration": 2.0},
    {"name": "Betty", "location": "Marina District", "start": 10.75, "end": 14.25, "duration": 1.0},
    {"name": "Sarah", "location": "Richmond District", "start": 16.25, "end": 19.5, "duration": 1.75},
    {"name": "Daniel", "location": "Pacific Heights", "start": 18.5, "end": 21.75, "duration": 1.0},
    {"name": "Joshua", "location": "Haight-Ashbury", "start": 9.0, "end": 15.5, "duration": 0.25},
    {"name": "Joseph", "location": "Presidio", "start": 7.0, "end": 13.0, "duration": 0.75},
    {"name": "Andrew", "location": "Nob Hill", "start": 19.75, "end": 22.0, "duration": 1.75},
    {"name": "John", "location": "The Castro", "start": 13.25, "end": 19.75, "duration": 0.75}
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
                "end": meeting_end
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