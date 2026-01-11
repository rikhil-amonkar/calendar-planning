import heapq
import json
from datetime import datetime, timedelta

# Define travel times as a dictionary of dictionaries
travel_times = {
    'Union Square': {'Nob Hill': 9, 'Haight-Ashbury': 18, 'Chinatown': 7, 'Marina District': 18},
    'Nob Hill': {'Union Square': 7, 'Haight-Ashbury': 13, 'Chinatown': 6, 'Marina District': 11},
    'Haight-Ashbury': {'Union Square': 17, 'Nob Hill': 15, 'Chinatown': 19, 'Marina District': 17},
    'Chinatown': {'Union Square': 7, 'Nob Hill': 8, 'Haight-Ashbury': 19, 'Marina District': 12},
    'Marina District': {'Union Square': 16, 'Nob Hill': 12, 'Haight-Ashbury': 16, 'Chinatown': 16}
}

# Define meeting constraints
constraints = {
    'Karen': {'location': 'Nob Hill', 'start': '21:15', 'end': '21:45', 'min_duration': 30},
    'Joseph': {'location': 'Haight-Ashbury', 'start': '12:30', 'end': '19:45', 'min_duration': 90},
    'Sandra': {'location': 'Chinatown', 'start': '7:15', 'end': '19:15', 'min_duration': 75},
    'Nancy': {'location': 'Marina District', 'start': '11:00', 'end': '20:15', 'min_duration': 105}
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def format_time(time_obj):
    return time_obj.strftime('%H:%M')

def get_possible_meetings(constraints):
    possible_meetings = []
    for name, details in constraints.items():
        start = parse_time(details['start'])
        end = parse_time(details['end'])
        min_duration = timedelta(minutes=details['min_duration'])
        location = details['location']
        
        current_time = start
        while current_time + min_duration <= end:
            possible_meetings.append((current_time, current_time + min_duration, location, name))
            current_time += timedelta(minutes=1)
    
    # Sort meetings by start time
    possible_meetings.sort()
    return possible_meetings

def find_optimal_schedule(possible_meetings, travel_times):
    schedule = []
    last_location = 'Union Square'
    last_end_time = parse_time('9:00')
    
    # Priority queue to store meetings that can be scheduled next
    pq = []
    
    for meeting in possible_meetings:
        start, end, location, person = meeting
        
        # Calculate travel time to the meeting location
        travel_time = travel_times[last_location][location]
        travel_end_time = last_end_time + timedelta(minutes=travel_time)
        
        # If we can reach the meeting on time and it starts after our travel ends
        if travel_end_time <= start:
            # Push the meeting into the priority queue with its end time as priority
            heapq.heappush(pq, (end, start, location, person))
        
        # Try to schedule the meeting with the earliest end time
        while pq and pq[0][0] <= last_end_time:
            _, start, location, person = heapq.heappop(pq)
            travel_time = travel_times[last_location][location]
            travel_end_time = last_end_time + timedelta(minutes=travel_time)
            
            if travel_end_time <= start:
                # Schedule the meeting
                schedule.append({
                    "action": "meet",
                    "location": location,
                    "person": person,
                    "start_time": format_time(start),
                    "end_time": format_time(end)
                })
                last_location = location
                last_end_time = end
                break
    
    return schedule

# Get possible meetings
possible_meetings = get_possible_meetings(constraints)

# Find the optimal schedule
optimal_schedule = find_optimal_schedule(possible_meetings, travel_times)

# Output the result as JSON
result = {
    "itinerary": optimal_schedule
}

print(json.dumps(result, indent=2))