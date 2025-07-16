import json
from itertools import permutations

# [Previous travel_times and friends data remains the same...]

def calculate_schedule(permutation):
    current_time = 9.0  # Start at Embarcadero at 9:00
    current_location = 'Embarcadero'
    schedule = []
    total_meetings = 0
    
    for friend in permutation:
        # Calculate travel time
        travel_time = travel_times[current_location][friend['location']] / 60.0
        arrival_time = current_time + travel_time
        
        # Calculate meeting window
        meeting_start = max(arrival_time, friend['start'])
        meeting_end = meeting_start + friend['duration']
        
        # Check if meeting fits in friend's availability and we can arrive on time
        if meeting_end <= friend['end']:
            # Add to schedule
            schedule.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': float_to_time(meeting_start),
                'end_time': float_to_time(meeting_end)
            })
            current_time = meeting_end
            current_location = friend['location']
            total_meetings += 1
    
    return schedule, total_meetings

def find_optimal_schedule():
    best_schedule = []
    max_meetings = 0
    
    # Try all permutations of friends (limited to 5 for performance)
    for perm in permutations(friends, 5):
        schedule, count = calculate_schedule(perm)
        if count > max_meetings:
            max_meetings = count
            best_schedule = schedule
            # Early exit if we found the maximum possible meetings
            if max_meetings == 5:
                break
    
    return best_schedule

# Generate the optimal schedule
optimal_schedule = find_optimal_schedule()

# Output as JSON
output = {
    "itinerary": optimal_schedule
}

print(json.dumps(output, indent=2))