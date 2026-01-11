import heapq
from datetime import datetime, timedelta

# Constants
START_TIME = 9 * 60  # 9:00 AM in minutes
END_TIME = 21 * 60   # 9:00 PM in minutes

# Travel times between locations (in minutes)
travel_times = {
    ('Russian Hill', 'Marina District'): 7,
    ('Russian Hill', 'Financial District'): 11,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Bayview'): 23,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Marina District', 'Russian Hill'): 8,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Alamo Square'): 15,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Nob Hill'): 12,
    ('Financial District', 'Russian Hill'): 11,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'The Castro'): 20,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Sunset District'): 30,
    ('Financial District', 'Haight-Ashbury'): 19,
    ('Financial District', 'Nob Hill'): 8,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'Marina District'): 15,
    ('Alamo Square', 'Financial District'): 17,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Bayview'): 16,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'Haight-Ashbury'): 5,
    ('Alamo Square', 'Nob Hill'): 11,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Alamo Square'): 9,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Nob Hill'): 20,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'Financial District'): 21,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Golden Gate Park'): 11,
    ('The Castro', 'Bayview'): 19,
    ('The Castro', 'Sunset District'): 17,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('The Castro', 'Nob Hill'): 16,
    ('Bayview', 'Russian Hill'): 23,
    ('Bayview', 'Marina District'): 27,
    ('Bayview', 'Financial District'): 19,
    ('Bayview', 'Alamo Square'): 16,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Bayview', 'The Castro'): 19,
    ('Bayview', 'Sunset District'): 23,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Nob Hill'): 20,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Financial District'): 30,
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Bayview'): 22,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Nob Hill'): 27,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Haight-Ashbury', 'Alamo Square'): 5,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'Financial District'): 9,
    ('Nob Hill', 'Alamo Square'): 11,
    ('Nob Hill', 'Golden Gate Park'): 17,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'Bayview'): 19,
    ('Nob Hill', 'Sunset District'): 24,
    ('Nob Hill', 'Haight-Ashbury'): 13,
}

# Friends' availability (start_time, end_time, min_duration in minutes)
friends_availability = {
    'Mark': (1845, 2100, 90),
    'Karen': (930, 1245, 90),
    'Barbara': (1000, 1930, 90),
    'Nancy': (1665, 2000, 105),
    'David': (900, 1800, 120),
    'Linda': (1815, 1965, 45),
    'Kevin': (1000, 1545, 120),
    'Matthew': (1015, 210, 45),
    'Andrew': (1145, 1485, 105),
}

def convert_to_minutes(time_str):
    """Convert time in HHMM format to minutes since midnight."""
    hours, minutes = divmod(time_str, 100)
    return hours * 60 + minutes

def convert_to_hhmm(minutes):
    """Convert minutes since midnight to HHMM format."""
    hours, minutes = divmod(minutes, 60)
    return f"{hours}:{minutes:02}"

def find_optimal_schedule():
    # Priority queue for exploring the schedule
    pq = []
    # Initial state: start at Russian Hill at 9:00 AM
    heapq.heappush(pq, (0, START_TIME, 'Russian Hill', []))
    
    # Visited set to avoid revisiting locations unnecessarily
    visited = set()
    
    while pq:
        current_time, last_location, _, itinerary = heapq.heappop(pq)
        
        # If we've already processed this state, skip it
        if (last_location, current_time) in visited:
            continue
        visited.add((last_location, current_time))
        
        # Check if we can meet any friends at the current location
        for friend, (start_time, end_time, min_duration) in friends_availability.items():
            if friend in [meeting['person'] for meeting in itinerary]:
                continue  # Skip if we've already met this friend
            
            # Check if we can meet this friend within their availability
            if current_time >= start_time and current_time + min_duration <= end_time:
                # Calculate the end time of the meeting
                meeting_end_time = current_time + min_duration
                
                # Add the meeting to the itinerary
                new_itinerary = itinerary + [{
                    'action': 'meet',
                    'location': last_location,
                    'person': friend,
                    'start_time': convert_to_hhmm(current_time),
                    'end_time': convert_to_hhmm(meeting_end_time)
                }]
                
                # Push the next state into the priority queue
                heapq.heappush(pq, (len(new_itinerary), meeting_end_time, last_location, new_itinerary))
        
        # Try moving to other locations
        for next_location, travel_time in travel_times.items():
            if next_location == last_location:
                continue
            
            # Calculate the arrival time at the next location
            arrival_time = current_time + travel_time
            
            # Only consider this move if we can still meet someone after traveling
            if arrival_time < END_TIME:
                heapq.heappush(pq, (len(itinerary), arrival_time, next_location, itinerary))
    
    # Find the itinerary with the maximum number of meetings
    best_itinerary = []
    for _, _, _, itinerary in pq:
        if len(itinerary) > len(best_itinerary):
            best_itinerary = itinerary
    
    return best_itinerary

# Generate the optimal schedule
optimal_schedule = find_optimal_schedule()

# Output the result as a JSON-formatted dictionary
import json
result = {
    "itinerary": optimal_schedule
}

print(json.dumps(result, indent=2))