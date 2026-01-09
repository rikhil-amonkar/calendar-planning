from datetime import datetime, timedelta
import json

def time_to_minutes(time_str):
    """Convert time string (H:MM) to minutes since midnight"""
    dt = datetime.strptime(time_str, "%H:%M")
    return dt.hour * 60 + dt.minute

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string (H:MM)"""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Travel times in minutes between locations
    travel_times = {
        ('North Beach', 'Pacific Heights'): 8,
        ('North Beach', 'Chinatown'): 6,
        ('North Beach', 'Union Square'): 7,
        ('North Beach', 'Mission District'): 18,
        ('North Beach', 'Golden Gate Park'): 22,
        ('North Beach', 'Nob Hill'): 7,
        ('Pacific Heights', 'North Beach'): 9,
        ('Pacific Heights', 'Chinatown'): 11,
        ('Pacific Heights', 'Union Square'): 12,
        ('Pacific Heights', 'Mission District'): 15,
        ('Pacific Heights', 'Golden Gate Park'): 15,
        ('Pacific Heights', 'Nob Hill'): 8,
        ('Chinatown', 'North Beach'): 3,
        ('Chinatown', 'Pacific Heights'): 10,
        ('Chinatown', 'Union Square'): 7,
        ('Chinatown', 'Mission District'): 18,
        ('Chinatown', 'Golden Gate Park'): 23,
        ('Chinatown', 'Nob Hill'): 8,
        ('Union Square', 'North Beach'): 10,
        ('Union Square', 'Pacific Heights'): 15,
        ('Union Square', 'Chinatown'): 7,
        ('Union Square', 'Mission District'): 14,
        ('Union Square', 'Golden Gate Park'): 22,
        ('Union Square', 'Nob Hill'): 9,
        ('Mission District', 'North Beach'): 17,
        ('Mission District', 'Pacific Heights'): 16,
        ('Mission District', 'Chinatown'): 16,
        ('Mission District', 'Union Square'): 15,
        ('Mission District', 'Golden Gate Park'): 17,
        ('Mission District', 'Nob Hill'): 12,
        ('Golden Gate Park', 'North Beach'): 24,
        ('Golden Gate Park', 'Pacific Heights'): 16,
        ('Golden Gate Park', 'Chinatown'): 23,
        ('Golden Gate Park', 'Union Square'): 22,
        ('Golden Gate Park', 'Mission District'): 17,
        ('Golden Gate Park', 'Nob Hill'): 20,
        ('Nob Hill', 'North Beach'): 8,
        ('Nob Hill', 'Pacific Heights'): 8,
        ('Nob Hill', 'Chinatown'): 6,
        ('Nob Hill', 'Union Square'): 7,
        ('Nob Hill', 'Mission District'): 13,
        ('Nob Hill', 'Golden Gate Park'): 17,
    }
    
    # Friend constraints
    friends = [
        {
            'name': 'James',
            'location': 'Pacific Heights',
            'available_start': '20:00',
            'available_end': '22:00',
            'min_duration': 120
        },
        {
            'name': 'Robert',
            'location': 'Chinatown',
            'available_start': '12:15',
            'available_end': '16:45',
            'min_duration': 90
        },
        {
            'name': 'Jeffrey',
            'location': 'Union Square',
            'available_start': '9:30',
            'available_end': '15:30',
            'min_duration': 120
        },
        {
            'name': 'Carol',
            'location': 'Mission District',
            'available_start': '18:15',
            'available_end': '21:15',
            'min_duration': 15
        },
        {
            'name': 'Mark',
            'location': 'Golden Gate Park',
            'available_start': '11:30',
            'available_end': '17:45',
            'min_duration': 15
        },
        {
            'name': 'Sandra',
            'location': 'Nob Hill',
            'available_start': '8:00',
            'available_end': '15:30',
            'min_duration': 15
        }
    ]
    
    # Convert friend availability to minutes
    for friend in friends:
        friend['available_start_min'] = time_to_minutes(friend['available_start'])
        friend['available_end_min'] = time_to_minutes(friend['available_end'])
    
    # Start from North Beach at 9:00
    current_time = time_to_minutes('9:00')
    current_location = 'North Beach'
    
    def find_best_itinerary(remaining_friends, current_time, current_location, current_itinerary):
        if not remaining_friends:
            return current_itinerary[:]
        
        best_itinerary = current_itinerary[:]
        
        for i, friend in enumerate(remaining_friends):
            # Calculate travel time
            travel_time = travel_times.get((current_location, friend['location']), 999)
            
            # Calculate earliest possible start time
            earliest_start = max(current_time + travel_time, friend['available_start_min'])
            
            # Check if meeting is possible
            if earliest_start + friend['min_duration'] <= friend['available_end_min']:
                # Create meeting
                meeting = {
                    "action": "meet",
                    "location": friend['location'],
                    "person": friend['name'],
                    "start_time": minutes_to_time(earliest_start),
                    "end_time": minutes_to_time(earliest_start + friend['min_duration'])
                }
                
                # Update for next iteration
                new_itinerary = current_itinerary + [meeting]
                new_time = earliest_start + friend['min_duration']
                new_location = friend['location']
                new_remaining = remaining_friends[:i] + remaining_friends[i+1:]
                
                # Recursively find best itinerary
                candidate = find_best_itinerary(new_remaining, new_time, new_location, new_itinerary)
                
                # Keep the itinerary with most meetings
                if len(candidate) > len(best_itinerary):
                    best_itinerary = candidate
        
        return best_itinerary
    
    # Try different orderings to maximize number of meetings
    best_overall_itinerary = []
    
    # Try multiple starting orders based on proximity and availability
    for attempt in range(3):
        if attempt == 0:
            # Sort by availability start time
            sorted_friends = sorted(friends, key=lambda x: x['available_start_min'])
        elif attempt == 1:
            # Sort by minimum duration (shorter meetings first)
            sorted_friends = sorted(friends, key=lambda x: x['min_duration'])
        else:
            # Sort by location proximity from starting point
            def proximity_score(friend):
                return travel_times.get((current_location, friend['location']), 999)
            sorted_friends = sorted(friends, key=proximity_score)
        
        itinerary = find_best_itinerary(sorted_friends, current_time, current_location, [])
        
        if len(itinerary) > len(best_overall_itinerary):
            best_overall_itinerary = itinerary
    
    # If no meetings found with backtracking, use simple greedy approach
    if not best_overall_itinerary:
        itinerary = []
        current_time = time_to_minutes('9:00')
        current_location = 'North Beach'
        
        # Simple greedy approach
        remaining_friends = friends.copy()
        while remaining_friends:
            best_next = None
            best_end_time = float('inf')
            
            for friend in remaining_friends:
                travel_time = travel_times.get((current_location, friend['location']), 999)
                earliest_start = max(current_time + travel_time, friend['available_start_min'])
                
                if earliest_start + friend['min_duration'] <= friend['available_end_min']:
                    end_time = earliest_start + friend['min_duration']
                    if end_time < best_end_time:
                        best_end_time = end_time
                        best_next = friend
            
            if best_next:
                travel_time = travel_times.get((current_location, best_next['location']), 999)
                start_time = max(current_time + travel_time, best_next['available_start_min'])
                
                itinerary.append({
                    "action": "meet",
                    "location": best_next['location'],
                    "person": best_next['name'],
                    "start_time": minutes_to_time(start_time),
                    "end_time": minutes_to_time(start_time + best_next['min_duration'])
                })
                
                current_time = start_time + best_next['min_duration']
                current_location = best_next['location']
                remaining_friends.remove(best_next)
            else:
                break
        
        best_overall_itinerary = itinerary
    
    result = {"itinerary": best_overall_itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()