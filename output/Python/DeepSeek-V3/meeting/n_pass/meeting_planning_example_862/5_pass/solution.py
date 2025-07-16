import json
from itertools import permutations

# (Travel times and friends data remain the same as in the original code)

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def get_travel_time(from_loc, to_loc):
    if from_loc == to_loc:
        return 0
    return travel_times.get(from_loc, {}).get(to_loc, float('inf'))

def generate_optimal_schedule():
    best_schedule = []
    best_score = 0
    
    # We'll use a greedy approach with backtracking for better performance
    def backtrack(current_schedule, remaining_friends, current_time, current_location):
        nonlocal best_schedule, best_score
        
        # Calculate current score
        current_score = len(current_schedule) * 1000 + sum(m['min_duration'] for m in current_schedule)
        if current_score > best_score:
            best_score = current_score
            best_schedule = current_schedule.copy()
        
        # Try to add each remaining friend
        for i, friend in enumerate(remaining_friends):
            # Calculate travel time
            travel_time = get_travel_time(current_location, friend['location'])
            arrival_time = current_time + travel_time
            
            # Calculate possible meeting window
            meeting_start = time_to_minutes(friend['start'])
            meeting_end = time_to_minutes(friend['end'])
            min_duration = friend['min_duration']
            
            latest_start = meeting_end - min_duration
            if arrival_time > latest_start:
                continue  # Can't make this meeting
            
            start_time = max(arrival_time, meeting_start)
            end_time = start_time + min_duration
            
            # Add to schedule and recurse
            new_schedule = current_schedule.copy()
            new_schedule.append({
                'name': friend['name'],
                'location': friend['location'],
                'start': minutes_to_time(start_time),
                'end': minutes_to_time(end_time),
                'min_duration': min_duration
            })
            
            new_remaining = remaining_friends[:i] + remaining_friends[i+1:]
            backtrack(new_schedule, new_remaining, end_time, friend['location'])
    
    # Start with empty schedule at 9:00 from Mission District
    backtrack([], friends, time_to_minutes('9:00'), 'Mission District')
    return best_schedule

def format_schedule(schedule):
    itinerary = []
    current_time = time_to_minutes('9:00')
    current_location = 'Mission District'
    
    for meeting in schedule:
        # Travel to meeting location
        travel_time = get_travel_time(current_location, meeting['location'])
        arrival_time = current_time + travel_time
        meeting_start = time_to_minutes(meeting['start'])
        meeting_end = time_to_minutes(meeting['end'])
        min_duration = meeting['min_duration']
        
        # Calculate meeting time
        start_time = max(arrival_time, meeting_start)
        end_time = start_time + min_duration
        
        itinerary.append({
            "action": "meet",
            "location": meeting['location'],
            "person": meeting['name'],
            "start_time": minutes_to_time(start_time),
            "end_time": minutes_to_time(end_time)
        })
        
        current_time = end_time
        current_location = meeting['location']
    
    return {"itinerary": itinerary}

# Generate and output the schedule
schedule = generate_optimal_schedule()
result = format_schedule(schedule)
print(json.dumps(result, indent=2))