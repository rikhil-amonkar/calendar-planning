import heapq
import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    friends = [
        {'name': 'Mary', 'location': 'Embarcadero', 'available_start': 1200, 'available_end': 1275, 'required_duration': 75},
        {'name': 'Kenneth', 'location': 'The Castro', 'available_start': 675, 'available_end': 1080, 'required_duration': 30},
        {'name': 'Joseph', 'location': 'Haight-Ashbury', 'available_start': 1200, 'available_end': 1320, 'required_duration': 120},
        {'name': 'Sarah', 'location': 'Union Square', 'available_start': 705, 'available_end': 870, 'required_duration': 90},
        {'name': 'Thomas', 'location': 'North Beach', 'available_start': 1155, 'available_end': 1185, 'required_duration': 15},
        {'name': 'Daniel', 'location': 'Pacific Heights', 'available_start': 825, 'available_end': 1230, 'required_duration': 15},
        {'name': 'Richard', 'location': 'Chinatown', 'available_start': 480, 'available_end': 1125, 'required_duration': 30},
        {'name': 'Mark', 'location': 'Golden Gate Park', 'available_start': 1050, 'available_end': 1290, 'required_duration': 120},
        {'name': 'David', 'location': 'Marina District', 'available_start': 1200, 'available_end': 1260, 'required_duration': 60},
        {'name': 'Karen', 'location': 'Russian Hill', 'available_start': 795, 'available_end': 1110, 'required_duration': 120}
    ]
    num_friends = len(friends)
    
    locations = ['Nob Hill', 'Embarcadero', 'The Castro', 'Haight-Ashbury', 'Union Square', 'North Beach', 'Pacific Heights', 'Chinatown', 'Golden Gate Park', 'Marina District', 'Russian Hill']
    travel_times = {
        'Nob Hill': {
            'Embarcadero': 9,
            'The Castro': 17,
            'Haight-Ashbury': 13,
            'Union Square': 7,
            'North Beach': 8,
            'Pacific Heights': 8,
            'Chinatown': 6,
            'Golden Gate Park': 17,
            'Marina District': 11,
            'Russian Hill': 5
        },
        'Embarcadero': {
            'Nob Hill': 10,
            'The Castro': 25,
            'Haight-Ashbury': 21,
            'Union Square': 10,
            'North Beach': 5,
            'Pacific Heights': 11,
            'Chinatown': 7,
            'Golden Gate Park': 25,
            'Marina District': 12,
            'Russian Hill': 8
        },
        'The Castro': {
            'Nob Hill': 16,
            'Embarcadero': 22,
            'Haight-Ashbury': 6,
            'Union Square': 19,
            'North Beach': 20,
            'Pacific Heights': 16,
            'Chinatown': 22,
            'Golden Gate Park': 11,
            'Marina District': 21,
            'Russian Hill': 18
        },
        'Haight-Ashbury': {
            'Nob Hill': 15,
            'Embarcadero': 20,
            'The Castro': 6,
            'Union Square': 19,
            'North Beach': 19,
            'Pacific Heights': 12,
            'Chinatown': 19,
            'Golden Gate Park': 7,
            'Marina District': 17,
            'Russian Hill': 17
        },
        'Union Square': {
            'Nob Hill': 9,
            'Embarcadero': 11,
            'The Castro': 17,
            'Haight-Ashbury': 18,
            'North Beach': 10,
            'Pacific Heights': 15,
            'Chinatown': 7,
            'Golden Gate Park': 22,
            'Marina District': 18,
            'Russian Hill': 13
        },
        'North Beach': {
            'Nob Hill': 7,
            'Embarcadero': 6,
            'The Castro': 23,
            'Haight-Ashbury': 18,
            'Union Square': 7,
            'Pacific Heights': 8,
            'Chinatown': 6,
            'Golden Gate Park': 22,
            'Marina District': 9,
            'Russian Hill': 4
        },
        'Pacific Heights': {
            'Nob Hill': 8,
            'Embarcadero': 10,
            'The Castro': 16,
            'Haight-Ashbury': 11,
            'Union Square': 12,
            'North Beach': 9,
            'Chinatown': 11,
            'Golden Gate Park': 15,
            'Marina District': 6,
            'Russian Hill': 7
        },
        'Chinatown': {
            'Nob Hill': 9,
            'Embarcadero': 5,
            'The Castro': 22,
            'Haight-Ashbury': 19,
            'Union Square': 7,
            'North Beach': 3,
            'Pacific Heights': 10,
            'Golden Gate Park': 23,
            'Marina District': 12,
            'Russian Hill': 7
        },
        'Golden Gate Park': {
            'Nob Hill': 20,
            'Embarcadero': 25,
            'The Castro': 13,
            'Haight-Ashbury': 7,
            'Union Square': 22,
            'North Beach': 23,
            'Pacific Heights': 16,
            'Chinatown': 23,
            'Marina District': 16,
            'Russian Hill': 19
        },
        'Marina District': {
            'Nob Hill': 12,
            'Embarcadero': 14,
            'The Castro': 22,
            'Haight-Ashbury': 16,
            'Union Square': 16,
            'North Beach': 11,
            'Pacific Heights': 7,
            'Chinatown': 15,
            'Golden Gate Park': 18,
            'Russian Hill': 8
        },
        'Russian Hill': {
            'Nob Hill': 5,
            'Embarcadero': 8,
            'The Castro': 21,
            'Haight-Ashbury': 17,
            'Union Square': 10,
            'North Beach': 5,
            'Pacific Heights': 7,
            'Chinatown': 9,
            'Golden Gate Park': 21,
            'Marina District': 7
        }
    }
    
    initial_time = 540  # 9:00 AM
    initial_location = 'Nob Hill'
    initial_bitmask = 0
    initial_path = []
    
    heap = []
    heapq.heappush(heap, (0, initial_time, initial_location, initial_bitmask, initial_path))
    best_time = {}
    best_num_met = 0
    best_path = []
    
    while heap:
        neg_num_met, current_time, current_location, bitmask, path = heapq.heappop(heap)
        num_met = -neg_num_met
        
        key = (bitmask, current_location)
        if key in best_time:
            if best_time[key] <= current_time:
                continue
        best_time[key] = current_time
        
        if num_met > best_num_met:
            best_num_met = num_met
            best_path = path
        elif num_met == best_num_met and not best_path:
            best_path = path
        
        for friend_idx in range(num_friends):
            if not (bitmask & (1 << friend_idx)):
                friend = friends[friend_idx]
                friend_loc = friend['location']
                friend_start = friend['available_start']
                friend_end = friend['available_end']
                required = friend['required_duration']
                
                travel_time = travel_times[current_location][friend_loc]
                arrival_time = current_time + travel_time
                start_time = max(arrival_time, friend_start)
                end_time = start_time + required
                
                if end_time <= friend_end:
                    new_bitmask = bitmask | (1 << friend_idx)
                    new_path = path + [{
                        'action': 'meet',
                        'location': friend_loc,
                        'person': friend['name'],
                        'start_time': minutes_to_time(start_time),
                        'end_time': minutes_to_time(end_time)
                    }]
                    new_neg_num_met = -(num_met + 1)
                    heapq.heappush(heap, (new_neg_num_met, end_time, friend_loc, new_bitmask, new_path))
    
    result = {
        "itinerary": best_path
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()