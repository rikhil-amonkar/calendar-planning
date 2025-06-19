import json
import itertools

def time_to_minutes(time_str):
    parts = time_str.split(':')
    hours = int(parts[0])
    minutes = int(parts[1])
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def generate_schedule(order, friends_info, travel_times, start_time_minutes, start_location):
    current_time = start_time_minutes
    current_location = start_location
    itinerary = []
    
    for idx, friend_name in enumerate(order):
        friend = friends_info[friend_name]
        travel_key = (current_location, friend['location'])
        travel_duration = travel_times[travel_key]
        current_time += travel_duration
        
        available_start = friend['available_start_minutes']
        if current_time < available_start:
            current_time = available_start
            
        available_end = friend['available_end_minutes']
        
        if current_time + friend['min_duration'] > available_end:
            return None
        
        if idx == len(order) - 1:
            meeting_end = available_end
        else:
            strategy = friend.get('strategy', 'minimize_first')
            if strategy == 'minimize_first':
                desired_end = current_time + friend['min_duration']
                meeting_end = min(desired_end, available_end)
            else:
                next_friend_name = order[idx+1]
                next_friend = friends_info[next_friend_name]
                next_travel_key = (friend['location'], next_friend['location'])
                next_travel_duration = travel_times[next_travel_key]
                next_available_end = next_friend['available_end_minutes']
                desired_leave_time = (next_available_end - next_friend['min_duration']) - next_travel_duration
                meeting_end = min(available_end, desired_leave_time)
        
        meeting_end = max(meeting_end, current_time + friend['min_duration'])
        
        meeting = {
            'action': 'meet',
            'location': friend['location'],
            'person': friend_name,
            'start_time': minutes_to_time(current_time),
            'end_time': minutes_to_time(meeting_end)
        }
        itinerary.append(meeting)
        
        current_time = meeting_end
        current_location = friend['location']
    
    return itinerary

def compute_travel_time(order, travel_times, start_location, friends_info):
    total = 0
    if not order:
        return 0
    first_friend = order[0]
    total += travel_times[(start_location, friends_info[first_friend]['location'])]
    for i in range(len(order)-1):
        loc1 = friends_info[order[i]]['location']
        loc2 = friends_info[order[i+1]]['location']
        total += travel_times[(loc1, loc2)]
    return total

def evaluate_schedule(itinerary, friends_info):
    num_min_met = 0
    total_meeting_time = 0
    for meeting in itinerary:
        person = meeting['person']
        min_required = friends_info[person]['min_duration']
        start_min = time_to_minutes(meeting['start_time'])
        end_min = time_to_minutes(meeting['end_time'])
        duration = end_min - start_min
        total_meeting_time += duration
        if duration >= min_required:
            num_min_met += 1
    return num_min_met, total_meeting_time

def main():
    travel_times = {
        ('Bayview', 'Union Square'): 17,
        ('Bayview', 'Presidio'): 31,
        ('Union Square', 'Bayview'): 15,
        ('Union Square', 'Presidio'): 24,
        ('Presidio', 'Bayview'): 31,
        ('Presidio', 'Union Square'): 22
    }
    
    friends_info = {
        'Richard': {
            'location': 'Union Square',
            'available_start': '8:45',
            'available_end': '13:00',
            'min_duration': 120,
            'available_start_minutes': time_to_minutes('8:45'),
            'available_end_minutes': time_to_minutes('13:00')
        },
        'Charles': {
            'location': 'Presidio',
            'available_start': '9:45',
            'available_end': '13:00',
            'min_duration': 120,
            'available_start_minutes': time_to_minutes('9:45'),
            'available_end_minutes': time_to_minutes('13:00')
        }
    }
    
    start_time_str = '9:00'
    start_time_minutes = time_to_minutes(start_time_str)
    start_location = 'Bayview'
    
    friends_list = list(friends_info.keys())
    schedule_specs = []
    strategies = ['minimize_first', 'minimize_second']
    
    for r in range(1, len(friends_list)+1):
        for order in itertools.permutations(friends_list, r):
            non_last = order[:-1]
            if non_last:
                for strat_assignment in itertools.product(strategies, repeat=len(non_last)):
                    strat_dict = {friend: strategy for friend, strategy in zip(non_last, strat_assignment)}
                    schedule_specs.append((order, strat_dict))
            else:
                schedule_specs.append((order, {}))
    
    schedules = []
    for order, strategies in schedule_specs:
        friends_copy = {name: data.copy() for name, data in friends_info.items()}
        for friend_name in order:
            if friend_name in strategies:
                friends_copy[friend_name]['strategy'] = strategies[friend_name]
            elif 'strategy' in friends_copy[friend_name]:
                del friends_copy[friend_name]['strategy']
        itinerary = generate_schedule(order, friends_copy, travel_times, start_time_minutes, start_location)
        if itinerary is None:
            continue
        travel_time = compute_travel_time(order, travel_times, start_location, friends_copy)
        num_min_met, total_meeting = evaluate_schedule(itinerary, friends_copy)
        schedules.append((itinerary, num_min_met, total_meeting, travel_time))
    
    if not schedules:
        result = {"itinerary": []}
        print(json.dumps(result))
        return
    
    best_schedule = None
    best_score = (-1, -1, -1)
    for s in schedules:
        itinerary, num_min, total_meeting, travel_time = s
        score = (num_min, total_meeting, -travel_time)
        if score > best_score:
            best_score = score
            best_schedule = itinerary
    
    result = {
        "itinerary": best_schedule
    }
    print(json.dumps(result))

if __name__ == "__main__":
    main()