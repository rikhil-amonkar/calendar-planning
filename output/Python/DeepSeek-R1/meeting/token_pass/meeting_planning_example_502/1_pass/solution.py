import itertools
import json

def main():
    # Travel times matrix
    travel_times = {
        'Financial District': {
            'Golden Gate Park': 23,
            'Chinatown': 5,
            'Union Square': 9,
            'Fisherman\'s Wharf': 10,
            'Pacific Heights': 13,
            'North Beach': 7
        },
        'Golden Gate Park': {
            'Financial District': 26,
            'Chinatown': 23,
            'Union Square': 22,
            'Fisherman\'s Wharf': 24,
            'Pacific Heights': 16,
            'North Beach': 24
        },
        'Chinatown': {
            'Financial District': 5,
            'Golden Gate Park': 23,
            'Union Square': 7,
            'Fisherman\'s Wharf': 8,
            'Pacific Heights': 10,
            'North Beach': 3
        },
        'Union Square': {
            'Financial District': 9,
            'Golden Gate Park': 22,
            'Chinatown': 7,
            'Fisherman\'s Wharf': 15,
            'Pacific Heights': 15,
            'North Beach': 10
        },
        'Fisherman\'s Wharf': {
            'Financial District': 11,
            'Golden Gate Park': 25,
            'Chinatown': 12,
            'Union Square': 13,
            'Pacific Heights': 12,
            'North Beach': 6
        },
        'Pacific Heights': {
            'Financial District': 13,
            'Golden Gate Park': 15,
            'Chinatown': 11,
            'Union Square': 12,
            'Fisherman\'s Wharf': 13,
            'North Beach': 9
        },
        'North Beach': {
            'Financial District': 8,
            'Golden Gate Park': 22,
            'Chinatown': 6,
            'Union Square': 7,
            'Fisherman\'s Wharf': 5,
            'Pacific Heights': 8
        }
    }
    
    # Helper function to convert time string to minutes
    def time_to_minutes(time_str):
        parts = time_str.split(':')
        hour = int(parts[0])
        minute = int(parts[1])
        return hour * 60 + minute

    # Helper function to convert minutes to time string
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours}:{mins:02d}"

    # Define friends with their constraints (excluding Joseph)
    friends = [
        {'name': 'Stephanie', 'location': 'Golden Gate Park', 'start': time_to_minutes('11:00'), 'end': time_to_minutes('15:00'), 'min_duration': 105},
        {'name': 'Karen', 'location': 'Chinatown', 'start': time_to_minutes('13:45'), 'end': time_to_minutes('16:30'), 'min_duration': 15},
        {'name': 'Brian', 'location': 'Union Square', 'start': time_to_minutes('15:00'), 'end': time_to_minutes('17:15'), 'min_duration': 30},
        {'name': 'Rebecca', 'location': 'Fisherman\'s Wharf', 'start': time_to_minutes('8:00'), 'end': time_to_minutes('11:15'), 'min_duration': 30},
        {'name': 'Steven', 'location': 'North Beach', 'start': time_to_minutes('14:30'), 'end': time_to_minutes('20:45'), 'min_duration': 120}
    ]
    
    start_time = time_to_minutes('9:00')
    start_location = 'Financial District'
    
    best_count = 0
    best_schedule = None
    best_travel_time = float('inf')
    
    # Generate all non-empty subsets of friends
    all_subsets = []
    for r in range(1, len(friends) + 1):
        all_subsets.extend(itertools.combinations(friends, r))
    
    for subset in all_subsets:
        for order in itertools.permutations(subset):
            current_time = start_time
            current_loc = start_location
            schedule = []
            count = 0
            travel_time_total = 0
            feasible = True
            for friend in order:
                travel_time = travel_times[current_loc][friend['location']]
                travel_time_total += travel_time
                arrival_time = current_time + travel_time
                start_meeting = max(arrival_time, friend['start'])
                if start_meeting + friend['min_duration'] <= friend['end']:
                    end_meeting = start_meeting + friend['min_duration']
                    schedule.append((friend, start_meeting, end_meeting))
                    current_time = end_meeting
                    current_loc = friend['location']
                    count += 1
                else:
                    feasible = False
                    break
            
            if feasible and count > best_count:
                best_count = count
                best_schedule = schedule
                best_travel_time = travel_time_total
            elif feasible and count == best_count and travel_time_total < best_travel_time:
                best_schedule = schedule
                best_travel_time = travel_time_total
    
    itinerary = []
    if best_schedule:
        for meeting in best_schedule:
            friend, start_minutes, end_minutes = meeting
            itinerary.append({
                "action": "meet",
                "location": friend['location'],
                "person": friend['name'],
                "start_time": minutes_to_time(start_minutes),
                "end_time": minutes_to_time(end_minutes)
            })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()