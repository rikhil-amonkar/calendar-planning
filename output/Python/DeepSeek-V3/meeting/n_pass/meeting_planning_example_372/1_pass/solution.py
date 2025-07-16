import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Travel times in minutes (from -> to)
travel_times = {
    'Sunset District': {
        'Alamo Square': 17,
        'Russian Hill': 24,
        'Golden Gate Park': 11,
        'Mission District': 24
    },
    'Alamo Square': {
        'Sunset District': 16,
        'Russian Hill': 13,
        'Golden Gate Park': 9,
        'Mission District': 10
    },
    'Russian Hill': {
        'Sunset District': 23,
        'Alamo Square': 15,
        'Golden Gate Park': 21,
        'Mission District': 16
    },
    'Golden Gate Park': {
        'Sunset District': 10,
        'Alamo Square': 10,
        'Russian Hill': 19,
        'Mission District': 17
    },
    'Mission District': {
        'Sunset District': 24,
        'Alamo Square': 11,
        'Russian Hill': 15,
        'Golden Gate Park': 17
    }
}

# Constraints
friends = [
    {
        'name': 'Charles',
        'location': 'Alamo Square',
        'available_start': '18:00',
        'available_end': '20:45',
        'min_duration': 90
    },
    {
        'name': 'Margaret',
        'location': 'Russian Hill',
        'available_start': '9:00',
        'available_end': '16:00',
        'min_duration': 30
    },
    {
        'name': 'Daniel',
        'location': 'Golden Gate Park',
        'available_start': '8:00',
        'available_end': '13:30',
        'min_duration': 15
    },
    {
        'name': 'Stephanie',
        'location': 'Mission District',
        'available_start': '20:30',
        'available_end': '22:00',
        'min_duration': 90
    }
]

def generate_schedules():
    # Generate all possible orders to meet friends
    friend_indices = [0, 1, 2, 3]
    possible_orders = permutations(friend_indices)
    
    valid_schedules = []
    
    for order in possible_orders:
        current_location = 'Sunset District'
        current_time = time_to_minutes('9:00')
        schedule = []
        valid = True
        
        for idx in order:
            friend = friends[idx]
            location = friend['location']
            travel_time = travel_times[current_location][location]
            
            arrival_time = current_time + travel_time
            available_start = time_to_minutes(friend['available_start'])
            available_end = time_to_minutes(friend['available_end'])
            min_duration = friend['min_duration']
            
            # Calculate meeting window
            meeting_start = max(arrival_time, available_start)
            meeting_end = min(meeting_start + min_duration, available_end)
            
            if meeting_end - meeting_start < min_duration:
                valid = False
                break
            
            schedule.append({
                'action': 'meet',
                'location': location,
                'person': friend['name'],
                'start_time': minutes_to_time(meeting_start),
                'end_time': minutes_to_time(meeting_end)
            })
            
            current_time = meeting_end
            current_location = location
        
        if valid:
            valid_schedules.append(schedule)
    
    return valid_schedules

def find_best_schedule(schedules):
    # The best schedule is the one that meets the most friends
    # Since all schedules meet all friends, we pick the first one
    # (all permutations are valid in this case)
    return schedules[0]

def main():
    schedules = generate_schedules()
    if not schedules:
        print(json.dumps({"itinerary": []}))
        return
    
    best_schedule = find_best_schedule(schedules)
    result = {
        "itinerary": best_schedule
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()