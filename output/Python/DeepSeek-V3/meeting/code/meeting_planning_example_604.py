import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input data
travel_times = {
    'Fisherman\'s Wharf': {
        'The Castro': 26,
        'Golden Gate Park': 25,
        'Embarcadero': 8,
        'Russian Hill': 7,
        'Nob Hill': 11,
        'Alamo Square': 20,
        'North Beach': 6
    },
    'The Castro': {
        'Fisherman\'s Wharf': 24,
        'Golden Gate Park': 11,
        'Embarcadero': 22,
        'Russian Hill': 18,
        'Nob Hill': 16,
        'Alamo Square': 8,
        'North Beach': 20
    },
    'Golden Gate Park': {
        'Fisherman\'s Wharf': 24,
        'The Castro': 13,
        'Embarcadero': 25,
        'Russian Hill': 19,
        'Nob Hill': 20,
        'Alamo Square': 10,
        'North Beach': 24
    },
    'Embarcadero': {
        'Fisherman\'s Wharf': 6,
        'The Castro': 25,
        'Golden Gate Park': 25,
        'Russian Hill': 8,
        'Nob Hill': 10,
        'Alamo Square': 19,
        'North Beach': 5
    },
    'Russian Hill': {
        'Fisherman\'s Wharf': 7,
        'The Castro': 21,
        'Golden Gate Park': 21,
        'Embarcadero': 8,
        'Nob Hill': 5,
        'Alamo Square': 15,
        'North Beach': 5
    },
    'Nob Hill': {
        'Fisherman\'s Wharf': 11,
        'The Castro': 17,
        'Golden Gate Park': 17,
        'Embarcadero': 9,
        'Russian Hill': 5,
        'Alamo Square': 11,
        'North Beach': 8
    },
    'Alamo Square': {
        'Fisherman\'s Wharf': 19,
        'The Castro': 8,
        'Golden Gate Park': 9,
        'Embarcadero': 17,
        'Russian Hill': 13,
        'Nob Hill': 11,
        'North Beach': 15
    },
    'North Beach': {
        'Fisherman\'s Wharf': 5,
        'The Castro': 22,
        'Golden Gate Park': 22,
        'Embarcadero': 6,
        'Russian Hill': 4,
        'Nob Hill': 7,
        'Alamo Square': 16
    }
}

friends = [
    {
        'name': 'Laura',
        'location': 'The Castro',
        'start': '19:45',
        'end': '21:30',
        'duration': 105
    },
    {
        'name': 'Daniel',
        'location': 'Golden Gate Park',
        'start': '21:15',
        'end': '21:45',
        'duration': 15
    },
    {
        'name': 'William',
        'location': 'Embarcadero',
        'start': '7:00',
        'end': '9:00',
        'duration': 90
    },
    {
        'name': 'Karen',
        'location': 'Russian Hill',
        'start': '14:30',
        'end': '19:45',
        'duration': 30
    },
    {
        'name': 'Stephanie',
        'location': 'Nob Hill',
        'start': '7:30',
        'end': '9:30',
        'duration': 45
    },
    {
        'name': 'Joseph',
        'location': 'Alamo Square',
        'start': '11:30',
        'end': '12:45',
        'duration': 15
    },
    {
        'name': 'Kimberly',
        'location': 'North Beach',
        'start': '15:45',
        'end': '19:15',
        'duration': 30
    }
]

def get_possible_meetings(current_time, current_location, remaining_friends, visited):
    possible = []
    for friend in remaining_friends:
        if friend['name'] in visited:
            continue
        
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel_time
        
        start_window = time_to_minutes(friend['start'])
        end_window = time_to_minutes(friend['end'])
        
        meeting_start = max(arrival_time, start_window)
        meeting_end = meeting_start + friend['duration']
        
        if meeting_end <= end_window:
            possible.append((friend, meeting_start, meeting_end))
    
    return possible

def find_best_schedule(current_time, current_location, remaining_friends, visited, schedule):
    if not remaining_friends or len(visited) == len(remaining_friends):
        return schedule
    
    best_schedule = schedule.copy()
    max_meetings = len(schedule)
    
    possible_meetings = get_possible_meetings(current_time, current_location, remaining_friends, visited)
    
    for meeting in possible_meetings:
        friend, meeting_start, meeting_end = meeting
        new_visited = visited.copy()
        new_visited.add(friend['name'])
        new_schedule = schedule.copy()
        new_schedule.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
        })
        
        updated_schedule = find_best_schedule(
            meeting_end,
            friend['location'],
            remaining_friends,
            new_visited,
            new_schedule
        )
        
        if len(updated_schedule) > max_meetings:
            best_schedule = updated_schedule
            max_meetings = len(updated_schedule)
    
    return best_schedule

def main():
    start_time = time_to_minutes('9:00')
    start_location = 'Fisherman\'s Wharf'
    
    # Filter out friends that can't be met due to time constraints
    possible_friends = []
    for friend in friends:
        travel_time = travel_times[start_location][friend['location']]
        arrival_time = start_time + travel_time
        start_window = time_to_minutes(friend['start'])
        end_window = time_to_minutes(friend['end'])
        
        if arrival_time <= end_window and (arrival_time + friend['duration']) <= end_window:
            possible_friends.append(friend)
    
    best_schedule = find_best_schedule(start_time, start_location, possible_friends, set(), [])
    
    result = {
        "itinerary": best_schedule
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()