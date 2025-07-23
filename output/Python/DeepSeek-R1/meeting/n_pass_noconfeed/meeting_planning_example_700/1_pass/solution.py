import itertools
import json

def main():
    # Travel times dictionary (from, to) -> minutes
    travel_times = {
        ('Presidio', 'Pacific Heights'): 11,
        ('Presidio', 'Golden Gate Park'): 12,
        ('Presidio', 'Fisherman\'s Wharf'): 19,
        ('Presidio', 'Marina District'): 11,
        ('Presidio', 'Alamo Square'): 19,
        ('Presidio', 'Sunset District'): 15,
        ('Presidio', 'Nob Hill'): 18,
        ('Presidio', 'North Beach'): 18,
        ('Pacific Heights', 'Presidio'): 11,
        ('Pacific Heights', 'Golden Gate Park'): 15,
        ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
        ('Pacific Heights', 'Marina District'): 6,
        ('Pacific Heights', 'Alamo Square'): 10,
        ('Pacific Heights', 'Sunset District'): 21,
        ('Pacific Heights', 'Nob Hill'): 8,
        ('Pacific Heights', 'North Beach'): 9,
        ('Golden Gate Park', 'Presidio'): 11,
        ('Golden Gate Park', 'Pacific Heights'): 16,
        ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
        ('Golden Gate Park', 'Marina District'): 16,
        ('Golden Gate Park', 'Alamo Square'): 9,
        ('Golden Gate Park', 'Sunset District'): 10,
        ('Golden Gate Park', 'Nob Hill'): 20,
        ('Golden Gate Park', 'North Beach'): 23,
        ('Fisherman\'s Wharf', 'Presidio'): 17,
        ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
        ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
        ('Fisherman\'s Wharf', 'Marina District'): 9,
        ('Fisherman\'s Wharf', 'Alamo Square'): 21,
        ('Fisherman\'s Wharf', 'Sunset District'): 27,
        ('Fisherman\'s Wharf', 'Nob Hill'): 11,
        ('Fisherman\'s Wharf', 'North Beach'): 6,
        ('Marina District', 'Presidio'): 10,
        ('Marina District', 'Pacific Heights'): 7,
        ('Marina District', 'Golden Gate Park'): 18,
        ('Marina District', 'Fisherman\'s Wharf'): 10,
        ('Marina District', 'Alamo Square'): 15,
        ('Marina District', 'Sunset District'): 19,
        ('Marina District', 'Nob Hill'): 12,
        ('Marina District', 'North Beach'): 11,
        ('Alamo Square', 'Presidio'): 17,
        ('Alamo Square', 'Pacific Heights'): 10,
        ('Alamo Square', 'Golden Gate Park'): 9,
        ('Alamo Square', 'Fisherman\'s Wharf'): 19,
        ('Alamo Square', 'Marina District'): 15,
        ('Alamo Square', 'Sunset District'): 16,
        ('Alamo Square', 'Nob Hill'): 11,
        ('Alamo Square', 'North Beach'): 15,
        ('Sunset District', 'Presidio'): 16,
        ('Sunset District', 'Pacific Heights'): 21,
        ('Sunset District', 'Golden Gate Park'): 11,
        ('Sunset District', 'Fisherman\'s Wharf'): 29,
        ('Sunset District', 'Marina District'): 21,
        ('Sunset District', 'Alamo Square'): 17,
        ('Sunset District', 'Nob Hill'): 27,
        ('Sunset District', 'North Beach'): 28,
        ('Nob Hill', 'Presidio'): 17,
        ('Nob Hill', 'Pacific Heights'): 8,
        ('Nob Hill', 'Golden Gate Park'): 17,
        ('Nob Hill', 'Fisherman\'s Wharf'): 10,
        ('Nob Hill', 'Marina District'): 11,
        ('Nob Hill', 'Alamo Square'): 11,
        ('Nob Hill', 'Sunset District'): 24,
        ('Nob Hill', 'North Beach'): 8,
        ('North Beach', 'Presidio'): 17,
        ('North Beach', 'Pacific Heights'): 8,
        ('North Beach', 'Golden Gate Park'): 22,
        ('North Beach', 'Fisherman\'s Wharf'): 5,
        ('North Beach', 'Marina District'): 9,
        ('North Beach', 'Alamo Square'): 16,
        ('North Beach', 'Sunset District'): 27,
        ('North Beach', 'Nob Hill'): 7
    }
    
    # Friends data (excluding Kevin because we cannot meet him)
    friends = [
        {'name': 'Michelle', 'location': 'Golden Gate Park', 'start': 20*60, 'end': 21*60, 'min_dur': 15},
        {'name': 'Emily', 'location': 'Fisherman\'s Wharf', 'start': 16*60+15, 'end': 19*60, 'min_dur': 30},
        {'name': 'Mark', 'location': 'Marina District', 'start': 18*60+15, 'end': 19*60+45, 'min_dur': 75},
        {'name': 'Barbara', 'location': 'Alamo Square', 'start': 17*60, 'end': 19*60, 'min_dur': 120},
        {'name': 'Laura', 'location': 'Sunset District', 'start': 19*60, 'end': 21*60+15, 'min_dur': 75},
        {'name': 'Mary', 'location': 'Nob Hill', 'start': 17*60+30, 'end': 19*60, 'min_dur': 45},
        {'name': 'Helen', 'location': 'North Beach', 'start': 11*60, 'end': 12*60+15, 'min_dur': 45}
    ]
    
    start_time = 9 * 60  # 9:00 AM in minutes
    start_loc = 'Presidio'
    best_count = 0
    best_schedule = []
    
    # Generate all permutations of friends
    for perm in itertools.permutations(friends):
        current_time = start_time
        current_loc = start_loc
        schedule = []
        count = 0
        
        for friend in perm:
            key = (current_loc, friend['location'])
            if key not in travel_times:
                continue
            travel_duration = travel_times[key]
            arrival_time = current_time + travel_duration
            
            # Skip if arrival is after the friend's window ends
            if arrival_time > friend['end']:
                continue
                
            # Calculate meeting start and end
            meeting_start = max(arrival_time, friend['start'])
            meeting_end = meeting_start + friend['min_dur']
            
            # Check if meeting fits in the window
            if meeting_end > friend['end']:
                continue
                
            # Schedule the meeting
            schedule.append({
                'name': friend['name'],
                'location': friend['location'],
                'start_meeting': meeting_start,
                'end_meeting': meeting_end
            })
            count += 1
            current_time = meeting_end
            current_loc = friend['location']
        
        # Update best schedule if this permutation has more meetings
        if count > best_count:
            best_count = count
            best_schedule = schedule
    
    # Format the itinerary
    itinerary = []
    for meeting in best_schedule:
        def format_time(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h}:{m:02d}"
        
        itinerary.append({
            "action": "meet",
            "location": meeting['location'],
            "person": meeting['name'],
            "start_time": format_time(meeting['start_meeting']),
            "end_time": format_time(meeting['end_meeting'])
        })
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()