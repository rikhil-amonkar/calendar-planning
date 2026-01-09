import json
from datetime import datetime, timedelta
from itertools import permutations

def main():
    # Travel times dictionary (in minutes)
    travel_times = {
        ('Embarcadero', 'Richmond District'): 21,
        ('Embarcadero', 'Union Square'): 10,
        ('Embarcadero', 'Financial District'): 5,
        ('Embarcadero', 'Pacific Heights'): 11,
        ('Embarcadero', 'Nob Hill'): 10,
        ('Embarcadero', 'Bayview'): 21,
        ('Richmond District', 'Embarcadero'): 19,
        ('Richmond District', 'Union Square'): 21,
        ('Richmond District', 'Financial District'): 22,
        ('Richmond District', 'Pacific Heights'): 10,
        ('Richmond District', 'Nob Hill'): 17,
        ('Richmond District', 'Bayview'): 26,
        ('Union Square', 'Embarcadero'): 11,
        ('Union Square', 'Richmond District'): 20,
        ('Union Square', 'Financial District'): 9,
        ('Union Square', 'Pacific Heights'): 15,
        ('Union Square', 'Nob Hill'): 9,
        ('Union Square', 'Bayview'): 15,
        ('Financial District', 'Embarcadero'): 4,
        ('Financial District', 'Richmond District'): 21,
        ('Financial District', 'Union Square'): 9,
        ('Financial District', 'Pacific Heights'): 13,
        ('Financial District', 'Nob Hill'): 8,
        ('Financial District', 'Bayview'): 19,
        ('Pacific Heights', 'Embarcadero'): 10,
        ('Pacific Heights', 'Richmond District'): 12,
        ('Pacific Heights', 'Union Square'): 12,
        ('Pacific Heights', 'Financial District'): 13,
        ('Pacific Heights', 'Nob Hill'): 8,
        ('Pacific Heights', 'Bayview'): 22,
        ('Nob Hill', 'Embarcadero'): 9,
        ('Nob Hill', 'Richmond District'): 14,
        ('Nob Hill', 'Union Square'): 7,
        ('Nob Hill', 'Financial District'): 9,
        ('Nob Hill', 'Pacific Heights'): 8,
        ('Nob Hill', 'Bayview'): 19,
        ('Bayview', 'Embarcadero'): 19,
        ('Bayview', 'Richmond District'): 25,
        ('Bayview', 'Union Square'): 17,
        ('Bayview', 'Financial District'): 19,
        ('Bayview', 'Pacific Heights'): 23,
        ('Bayview', 'Nob Hill'): 20
    }

    # Friend constraints
    friends = {
        'Kenneth': {
            'location': 'Richmond District',
            'available_start': datetime.strptime('21:15', '%H:%M'),  # 9:15 PM
            'available_end': datetime.strptime('22:00', '%H:%M'),    # 10:00 PM
            'min_duration': 30  # minutes
        },
        'Lisa': {
            'location': 'Union Square',
            'available_start': datetime.strptime('9:00', '%H:%M'),
            'available_end': datetime.strptime('16:30', '%H:%M'),
            'min_duration': 45
        },
        'Joshua': {
            'location': 'Financial District',
            'available_start': datetime.strptime('12:00', '%H:%M'),
            'available_end': datetime.strptime('15:15', '%H:%M'),
            'min_duration': 15
        },
        'Nancy': {
            'location': 'Pacific Heights',
            'available_start': datetime.strptime('8:00', '%H:%M'),
            'available_end': datetime.strptime('11:30', '%H:%M'),
            'min_duration': 90
        },
        'Andrew': {
            'location': 'Nob Hill',
            'available_start': datetime.strptime('11:30', '%H:%M'),
            'available_end': datetime.strptime('20:15', '%H:%M'),
            'min_duration': 60
        },
        'John': {
            'location': 'Bayview',
            'available_start': datetime.strptime('16:45', '%H:%M'),
            'available_end': datetime.strptime('21:30', '%H:%M'),
            'min_duration': 75
        }
    }

    # Convert times to minutes since 9:00 AM for easier computation
    base_time = datetime.strptime('9:00', '%H:%M')
    
    def time_to_minutes(t):
        return int((t - base_time).total_seconds() / 60)
    
    def minutes_to_time_str(minutes):
        time_obj = base_time + timedelta(minutes=minutes)
        return time_obj.strftime('%H:%M').lstrip('0') if time_obj.strftime('%H:%M').startswith('0') else time_obj.strftime('%H:%M')

    # Greedy approach with backtracking for optimization
    def find_optimal_schedule():
        best_schedule = []
        max_friends = 0
        
        # Try different starting points and orders
        for start_friend in friends.keys():
            current_schedule = []
            visited = set()
            current_time = 0  # 9:00 AM
            current_location = 'Embarcadero'
            
            # Start with this friend
            if can_visit_friend(start_friend, current_time, current_location, visited):
                schedule_friend(start_friend, current_schedule, visited, current_time, current_location)
                
                # Try to add remaining friends
                remaining_friends = [f for f in friends.keys() if f not in visited]
                
                while remaining_friends:
                    next_friend = find_best_next_friend(remaining_friends, current_time, current_location)
                    if next_friend and can_visit_friend(next_friend, current_time, current_location, visited):
                        schedule_friend(next_friend, current_schedule, visited, current_time, current_location)
                        remaining_friends = [f for f in friends.keys() if f not in visited]
                    else:
                        break
            
            if len(current_schedule) > max_friends:
                max_friends = len(current_schedule)
                best_schedule = current_schedule.copy()
        
        return best_schedule

    def can_visit_friend(friend, current_time, current_location, visited):
        if friend in visited:
            return False
            
        info = friends[friend]
        travel_time = travel_times.get((current_location, info['location']), 999)
        arrival_time = current_time + travel_time
        available_start = time_to_minutes(info['available_start'])
        available_end = time_to_minutes(info['available_end'])
        
        # Check if we can arrive and complete the minimum duration
        meeting_start = max(arrival_time, available_start)
        meeting_end = meeting_start + info['min_duration']
        
        return meeting_end <= available_end

    def schedule_friend(friend, schedule, visited, current_time, current_location):
        info = friends[friend]
        travel_time = travel_times.get((current_location, info['location']), 999)
        arrival_time = current_time + travel_time
        available_start = time_to_minutes(info['available_start'])
        available_end = time_to_minutes(info['available_end'])
        
        # Start meeting as early as possible
        meeting_start = max(arrival_time, available_start)
        meeting_end = meeting_start + info['min_duration']
        
        schedule.append({
            'action': 'meet',
            'location': info['location'],
            'person': friend,
            'start_time': minutes_to_time_str(meeting_start),
            'end_time': minutes_to_time_str(meeting_end)
        })
        
        visited.add(friend)
        current_time = meeting_end
        current_location = info['location']
        
        return current_time, current_location

    def find_best_next_friend(remaining_friends, current_time, current_location):
        # Prioritize friends who are easier to reach and have tighter time windows
        best_friend = None
        best_score = float('inf')
        
        for friend in remaining_friends:
            info = friends[friend]
            travel_time = travel_times.get((current_location, info['location']), 999)
            arrival_time = current_time + travel_time
            available_start = time_to_minutes(info['available_start'])
            available_end = time_to_minutes(info['available_end'])
            
            if arrival_time <= available_end - info['min_duration']:
                # Score based on travel time and urgency of time window
                urgency = (available_end - current_time) / 60  # Convert to hours
                score = travel_time + (urgency * 10)  # Weight urgency
                
                if score < best_score:
                    best_score = score
                    best_friend = friend
        
        return best_friend

    # Find schedule using optimized approach
    schedule = find_optimal_schedule()
    
    # If no schedule found with greedy approach, try a simpler approach
    if not schedule:
        schedule = []
        current_time = 0
        current_location = 'Embarcadero'
        visited = set()
        
        # Sort friends by their availability start time
        sorted_friends = sorted(friends.keys(), 
                              key=lambda f: time_to_minutes(friends[f]['available_start']))
        
        for friend in sorted_friends:
            if friend not in visited and can_visit_friend(friend, current_time, current_location, visited):
                current_time, current_location = schedule_friend(friend, schedule, visited, current_time, current_location)

    output = {'itinerary': schedule}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()