import json
from itertools import permutations

# [Previous travel_times and friends definitions remain exactly the same...]

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
                "duration": friend["duration"]  # Added this line to include duration
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