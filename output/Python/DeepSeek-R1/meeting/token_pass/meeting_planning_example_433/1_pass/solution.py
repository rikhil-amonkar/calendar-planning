import itertools
import json

def main():
    # Define travel times as a dictionary with (from, to) keys
    travel_times = {
        ('Nob Hill', 'Richmond District'): 14,
        ('Nob Hill', 'Financial District'): 9,
        ('Nob Hill', 'North Beach'): 8,
        ('Nob Hill', 'The Castro'): 17,
        ('Nob Hill', 'Golden Gate Park'): 17,
        ('Richmond District', 'Nob Hill'): 17,
        ('Richmond District', 'Financial District'): 22,
        ('Richmond District', 'North Beach'): 17,
        ('Richmond District', 'The Castro'): 16,
        ('Richmond District', 'Golden Gate Park'): 9,
        ('Financial District', 'Nob Hill'): 8,
        ('Financial District', 'Richmond District'): 21,
        ('Financial District', 'North Beach'): 7,
        ('Financial District', 'The Castro'): 23,
        ('Financial District', 'Golden Gate Park'): 23,
        ('North Beach', 'Nob Hill'): 7,
        ('North Beach', 'Richmond District'): 18,
        ('North Beach', 'Financial District'): 8,
        ('North Beach', 'The Castro'): 22,
        ('North Beach', 'Golden Gate Park'): 22,
        ('The Castro', 'Nob Hill'): 16,
        ('The Castro', 'Richmond District'): 16,
        ('The Castro', 'Financial District'): 20,
        ('The Castro', 'North Beach'): 20,
        ('The Castro', 'Golden Gate Park'): 11,
        ('Golden Gate Park', 'Nob Hill'): 20,
        ('Golden Gate Park', 'Richmond District'): 7,
        ('Golden Gate Park', 'Financial District'): 26,
        ('Golden Gate Park', 'North Beach'): 24,
        ('Golden Gate Park', 'The Castro'): 13
    }
    
    # Define friends with their constraints (times in minutes from 9:00)
    friends = [
        {'name': 'Emily', 'location': 'Richmond District', 'window_start': 600, 'window_end': 720, 'min_duration': 15},
        {'name': 'Margaret', 'location': 'Financial District', 'window_start': 450, 'window_end': 675, 'min_duration': 75},
        {'name': 'Ronald', 'location': 'North Beach', 'window_start': 570, 'window_end': 630, 'min_duration': 45},
        {'name': 'Deborah', 'location': 'The Castro', 'window_start': 285, 'window_end': 735, 'min_duration': 90},
        {'name': 'Jeffrey', 'location': 'Golden Gate Park', 'window_start': 135, 'window_end': 330, 'min_duration': 120}
    ]
    
    # Helper function to convert minutes to time string
    def min_to_time(m):
        hours = 9 + m // 60
        minutes = m % 60
        return f"{hours}:{minutes:02d}"
    
    best_count = 0
    best_itinerary = []
    
    # Generate all permutations of the friends
    for perm in itertools.permutations(friends):
        current_time = 0
        current_location = 'Nob Hill'
        itinerary = []
        
        for friend in perm:
            # Get travel time
            if current_location == friend['location']:
                travel_time = 0
            else:
                travel_time = travel_times.get((current_location, friend['location']), 1000)
            
            arrival_time = current_time + travel_time
            meeting_start = max(arrival_time, friend['window_start'])
            meeting_end = meeting_start + friend['min_duration']
            
            # Check if meeting is feasible
            if meeting_end <= friend['window_end']:
                itinerary.append({
                    'action': 'meet',
                    'location': friend['location'],
                    'person': friend['name'],
                    'start_time': meeting_start,
                    'end_time': meeting_end
                })
                current_time = meeting_end
                current_location = friend['location']
        
        # Update best itinerary if this permutation has more meetings
        if len(itinerary) > best_count:
            best_count = len(itinerary)
            best_itinerary = itinerary
    
    # Convert best itinerary to output format
    output_itinerary = []
    for meeting in best_itinerary:
        output_itinerary.append({
            'action': 'meet',
            'location': meeting['location'],
            'person': meeting['person'],
            'start_time': min_to_time(meeting['start_time']),
            'end_time': min_to_time(meeting['end_time'])
        })
    
    # Output as JSON
    result = {'itinerary': output_itinerary}
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()