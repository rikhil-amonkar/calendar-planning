import json
from datetime import datetime, timedelta

def main():
    # Travel times in minutes between locations
    travel_times = {
        ('Embarcadero', 'Bayview'): 21,
        ('Embarcadero', 'Chinatown'): 7,
        ('Embarcadero', 'Alamo Square'): 19,
        ('Embarcadero', 'Nob Hill'): 10,
        ('Embarcadero', 'Presidio'): 20,
        ('Embarcadero', 'Union Square'): 10,
        ('Embarcadero', 'The Castro'): 25,
        ('Embarcadero', 'North Beach'): 5,
        ('Embarcadero', 'Fisherman\'s Wharf'): 6,
        ('Embarcadero', 'Marina District'): 12,
        ('Bayview', 'Embarcadero'): 19,
        ('Bayview', 'Chinatown'): 19,
        ('Bayview', 'Alamo Square'): 16,
        ('Bayview', 'Nob Hill'): 20,
        ('Bayview', 'Presidio'): 32,
        ('Bayview', 'Union Square'): 18,
        ('Bayview', 'The Castro'): 19,
        ('Bayview', 'North Beach'): 22,
        ('Bayview', 'Fisherman\'s Wharf'): 25,
        ('Bayview', 'Marina District'): 27,
        ('Chinatown', 'Embarcadero'): 5,
        ('Chinatown', 'Bayview'): 20,
        ('Chinatown', 'Alamo Square'): 17,
        ('Chinatown', 'Nob Hill'): 9,
        ('Chinatown', 'Presidio'): 19,
        ('Chinatown', 'Union Square'): 7,
        ('Chinatown', 'The Castro'): 22,
        ('Chinatown', 'North Beach'): 3,
        ('Chinatown', 'Fisherman\'s Wharf'): 8,
        ('Chinatown', 'Marina District'): 12,
        ('Alamo Square', 'Embarcadero'): 16,
        ('Alamo Square', 'Bayview'): 16,
        ('Alamo Square', 'Chinatown'): 15,
        ('Alamo Square', 'Nob Hill'): 11,
        ('Alamo Square', 'Presidio'): 17,
        ('Alamo Square', 'Union Square'): 14,
        ('Alamo Square', 'The Castro'): 8,
        ('Alamo Square', 'North Beach'): 15,
        ('Alamo Square', 'Fisherman\'s Wharf'): 19,
        ('Alamo Square', 'Marina District'): 15,
        ('Nob Hill', 'Embarcadero'): 9,
        ('Nob Hill', 'Bayview'): 19,
        ('Nob Hill', 'Chinatown'): 6,
        ('Nob Hill', 'Alamo Square'): 11,
        ('Nob Hill', 'Presidio'): 17,
        ('Nob Hill', 'Union Square'): 7,
        ('Nob Hill', 'The Castro'): 17,
        ('Nob Hill', 'North Beach'): 8,
        ('Nob Hill', 'Fisherman\'s Wharf'): 10,
        ('Nob Hill', 'Marina District'): 11,
        ('Presidio', 'Embarcadero'): 20,
        ('Presidio', 'Bayview'): 31,
        ('Presidio', 'Chinatown'): 21,
        ('Presidio', 'Alamo Square'): 19,
        ('Presidio', 'Nob Hill'): 18,
        ('Presidio', 'Union Square'): 22,
        ('Presidio', 'The Castro'): 21,
        ('Presidio', 'North Beach'): 18,
        ('Presidio', 'Fisherman\'s Wharf'): 19,
        ('Presidio', 'Marina District'): 11,
        ('Union Square', 'Embarcadero'): 11,
        ('Union Square', 'Bayview'): 15,
        ('Union Square', 'Chinatown'): 7,
        ('Union Square', 'Alamo Square'): 15,
        ('Union Square', 'Nob Hill'): 9,
        ('Union Square', 'Presidio'): 24,
        ('Union Square', 'The Castro'): 17,
        ('Union Square', 'North Beach'): 10,
        ('Union Square', 'Fisherman\'s Wharf'): 15,
        ('Union Square', 'Marina District'): 18,
        ('The Castro', 'Embarcadero'): 22,
        ('The Castro', 'Bayview'): 19,
        ('The Castro', 'Chinatown'): 22,
        ('The Castro', 'Alamo Square'): 8,
        ('The Castro', 'Nob Hill'): 16,
        ('The Castro', 'Presidio'): 20,
        ('The Castro', 'Union Square'): 19,
        ('The Castro', 'North Beach'): 20,
        ('The Castro', 'Fisherman\'s Wharf'): 24,
        ('The Castro', 'Marina District'): 21,
        ('North Beach', 'Embarcadero'): 6,
        ('North Beach', 'Bayview'): 25,
        ('North Beach', 'Chinatown'): 6,
        ('North Beach', 'Alamo Square'): 16,
        ('North Beach', 'Nob Hill'): 7,
        ('North Beach', 'Presidio'): 17,
        ('North Beach', 'Union Square'): 7,
        ('North Beach', 'The Castro'): 23,
        ('North Beach', 'Fisherman\'s Wharf'): 5,
        ('North Beach', 'Marina District'): 9,
        ('Fisherman\'s Wharf', 'Embarcadero'): 8,
        ('Fisherman\'s Wharf', 'Bayview'): 26,
        ('Fisherman\'s Wharf', 'Chinatown'): 12,
        ('Fisherman\'s Wharf', 'Alamo Square'): 21,
        ('Fisherman\'s Wharf', 'Nob Hill'): 11,
        ('Fisherman\'s Wharf', 'Presidio'): 17,
        ('Fisherman\'s Wharf', 'Union Square'): 13,
        ('Fisherman\'s Wharf', 'The Castro'): 27,
        ('Fisherman\'s Wharf', 'North Beach'): 6,
        ('Fisherman\'s Wharf', 'Marina District'): 9,
        ('Marina District', 'Embarcadero'): 14,
        ('Marina District', 'Bayview'): 27,
        ('Marina District', 'Chinatown'): 15,
        ('Marina District', 'Alamo Square'): 15,
        ('Marina District', 'Nob Hill'): 12,
        ('Marina District', 'Presidio'): 10,
        ('Marina District', 'Union Square'): 16,
        ('Marina District', 'The Castro'): 22,
        ('Marina District', 'North Beach'): 11,
        ('Marina District', 'Fisherman\'s Wharf'): 10
    }

    # Friend constraints
    friends = [
        {'name': 'Matthew', 'location': 'Bayview', 'start': '19:15', 'end': '22:00', 'min_duration': 120},
        {'name': 'Karen', 'location': 'Chinatown', 'start': '19:15', 'end': '21:15', 'min_duration': 90},
        {'name': 'Sarah', 'location': 'Alamo Square', 'start': '20:00', 'end': '21:45', 'min_duration': 105},
        {'name': 'Jessica', 'location': 'Nob Hill', 'start': '16:30', 'end': '18:45', 'min_duration': 120},
        {'name': 'Stephanie', 'location': 'Presidio', 'start': '7:30', 'end': '10:15', 'min_duration': 60},
        {'name': 'Mary', 'location': 'Union Square', 'start': '16:45', 'end': '21:30', 'min_duration': 60},
        {'name': 'Charles', 'location': 'The Castro', 'start': '16:30', 'end': '22:00', 'min_duration': 105},
        {'name': 'Nancy', 'location': 'North Beach', 'start': '14:45', 'end': '20:00', 'min_duration': 15},
        {'name': 'Thomas', 'location': 'Fisherman\'s Wharf', 'start': '13:30', 'end': '19:00', 'min_duration': 30},
        {'name': 'Brian', 'location': 'Marina District', 'start': '12:15', 'end': '18:00', 'min_duration': 60}
    ]

    # Convert time strings to minutes since 9:00
    def time_to_minutes(time_str):
        time_obj = datetime.strptime(time_str, '%H:%M')
        base_time = datetime.strptime('9:00', '%H:%M')
        delta = time_obj - base_time
        return int(delta.total_seconds() / 60)

    # Convert minutes since 9:00 back to time string
    def minutes_to_time(minutes):
        base_time = datetime.strptime('9:00', '%H:%M')
        result_time = base_time + timedelta(minutes=minutes)
        return result_time.strftime('%H:%M').lstrip('0')

    # Get travel time between two locations
    def get_travel_time(loc1, loc2):
        if loc1 == loc2:
            return 0
        key = (loc1, loc2)
        if key in travel_times:
            return travel_times[key]
        # Try reverse
        key = (loc2, loc1)
        if key in travel_times:
            return travel_times[key]
        return float('inf')  # No connection

    # Convert friend data to minutes
    for friend in friends:
        friend['start_min'] = time_to_minutes(friend['start'])
        friend['end_min'] = time_to_minutes(friend['end'])

    # Sort friends by end time (earlier first)
    friends_sorted = sorted(friends, key=lambda x: x['end_min'])

    def find_best_schedule():
        best_schedule = []
        max_meetings = 0
        
        def backtrack(current_schedule, current_time, current_location, used):
            nonlocal best_schedule, max_meetings
            
            if len(current_schedule) > max_meetings:
                best_schedule = current_schedule.copy()
                max_meetings = len(current_schedule)
            
            for i, friend in enumerate(friends_sorted):
                if used[i]:
                    continue
                
                # Calculate earliest possible start time
                travel_time = get_travel_time(current_location, friend['location'])
                earliest_start = current_time + travel_time if current_time > 0 else friend['start_min']
                
                # Check if we can meet this friend
                if earliest_start <= friend['end_min'] - friend['min_duration']:
                    # Use the maximum possible duration within constraints
                    actual_start = max(earliest_start, friend['start_min'])
                    actual_end = min(actual_start + friend['min_duration'], friend['end_min'])
                    
                    if actual_end <= friend['end_min']:
                        used[i] = True
                        current_schedule.append({
                            'friend': friend,
                            'start': actual_start,
                            'end': actual_end,
                            'location': friend['location']
                        })
                        
                        backtrack(current_schedule, actual_end, friend['location'], used)
                        
                        current_schedule.pop()
                        used[i] = False
        
        used = [False] * len(friends_sorted)
        backtrack([], 0, 'Embarcadero', used)
        return best_schedule

    # Find the best schedule
    best_schedule = find_best_schedule()

    # Build itinerary
    itinerary = []
    for meeting in best_schedule:
        itinerary.append({
            "action": "meet",
            "location": meeting['friend']['location'],
            "person": meeting['friend']['name'],
            "start_time": minutes_to_time(meeting['start']),
            "end_time": minutes_to_time(meeting['end'])
        })

    # Sort itinerary by start time
    itinerary.sort(key=lambda x: datetime.strptime(x['start_time'], '%H:%M'))

    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    main()