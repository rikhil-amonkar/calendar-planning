import itertools
import json

def main():
    # Travel matrix with travel times between locations
    travel_matrix = {
        'Pacific Heights': {
            'Marina District': 6,
            'The Castro': 16,
            'Richmond District': 12,
            'Alamo Square': 10,
            'Financial District': 13,
            'Presidio': 11,
            'Mission District': 15,
            'Nob Hill': 8,
            'Russian Hill': 7
        },
        'Marina District': {
            'Pacific Heights': 7,
            'The Castro': 22,
            'Richmond District': 11,
            'Alamo Square': 15,
            'Financial District': 17,
            'Presidio': 10,
            'Mission District': 20,
            'Nob Hill': 12,
            'Russian Hill': 8
        },
        'The Castro': {
            'Pacific Heights': 16,
            'Marina District': 21,
            'Richmond District': 16,
            'Alamo Square': 8,
            'Financial District': 21,
            'Presidio': 20,
            'Mission District': 7,
            'Nob Hill': 16,
            'Russian Hill': 18
        },
        'Richmond District': {
            'Pacific Heights': 10,
            'Marina District': 9,
            'The Castro': 16,
            'Alamo Square': 13,
            'Financial District': 22,
            'Presidio': 7,
            'Mission District': 20,
            'Nob Hill': 17,
            'Russian Hill': 13
        },
        'Alamo Square': {
            'Pacific Heights': 10,
            'Marina District': 15,
            'The Castro': 8,
            'Richmond District': 11,
            'Financial District': 17,
            'Presidio': 17,
            'Mission District': 10,
            'Nob Hill': 11,
            'Russian Hill': 13
        },
        'Financial District': {
            'Pacific Heights': 13,
            'Marina District': 15,
            'The Castro': 20,
            'Richmond District': 21,
            'Alamo Square': 17,
            'Presidio': 22,
            'Mission District': 17,
            'Nob Hill': 8,
            'Russian Hill': 11
        },
        'Presidio': {
            'Pacific Heights': 11,
            'Marina District': 11,
            'The Castro': 21,
            'Richmond District': 7,
            'Alamo Square': 19,
            'Financial District': 23,
            'Mission District': 26,
            'Nob Hill': 18,
            'Russian Hill': 14
        },
        'Mission District': {
            'Pacific Heights': 16,
            'Marina District': 19,
            'The Castro': 7,
            'Richmond District': 20,
            'Alamo Square': 11,
            'Financial District': 15,
            'Presidio': 25,
            'Nob Hill': 12,
            'Russian Hill': 15
        },
        'Nob Hill': {
            'Pacific Heights': 8,
            'Marina District': 11,
            'The Castro': 17,
            'Richmond District': 14,
            'Alamo Square': 11,
            'Financial District': 9,
            'Presidio': 17,
            'Mission District': 13,
            'Russian Hill': 5
        },
        'Russian Hill': {
            'Pacific Heights': 7,
            'Marina District': 7,
            'The Castro': 21,
            'Richmond District': 14,
            'Alamo Square': 15,
            'Financial District': 11,
            'Presidio': 14,
            'Mission District': 16,
            'Nob Hill': 5
        }
    }
    
    # Define meetings with time windows and durations
    meetings = [
        {'name': 'Linda', 'location': 'Marina District', 'start': 1080, 'end': 1320, 'min_duration': 30},
        {'name': 'Kenneth', 'location': 'The Castro', 'start': 885, 'end': 975, 'min_duration': 30},
        {'name': 'Kimberly', 'location': 'Richmond District', 'start': 855, 'end': 1320, 'min_duration': 30},
        {'name': 'Paul', 'location': 'Alamo Square', 'start': 1260, 'end': 1290, 'min_duration': 15},
        {'name': 'Carol', 'location': 'Financial District', 'start': 615, 'end': 720, 'min_duration': 60},
        {'name': 'Brian', 'location': 'Presidio', 'start': 600, 'end': 1290, 'min_duration': 75},
        {'name': 'Laura', 'location': 'Mission District', 'start': 975, 'end': 1230, 'min_duration': 30},
        {'name': 'Sandra', 'location': 'Nob Hill', 'start': 555, 'end': 1110, 'min_duration': 60},
        {'name': 'Karen', 'location': 'Russian Hill', 'start': 1110, 'end': 1320, 'min_duration': 75}
    ]
    
    # Convert minutes to time string
    def minutes_to_time(m):
        hours = m // 60
        minutes = m % 60
        return f"{hours}:{minutes:02d}"
    
    # Find optimal itinerary
    best_count = -1
    best_itinerary = None
    
    for perm in itertools.permutations(meetings):
        current_time = 540  # 9:00 AM
        current_loc = 'Pacific Heights'
        itinerary = []
        for meeting in perm:
            travel_time = travel_matrix[current_loc][meeting['location']]
            arrival_time = current_time + travel_time
            start_meeting = max(arrival_time, meeting['start'])
            if start_meeting + meeting['min_duration'] <= meeting['end']:
                end_meeting = start_meeting + meeting['min_duration']
                itinerary.append({
                    'meeting': meeting,
                    'start': start_meeting,
                    'end': end_meeting
                })
                current_time = end_meeting
                current_loc = meeting['location']
        if len(itinerary) > best_count:
            best_count = len(itinerary)
            best_itinerary = itinerary
    
    # Format output
    output_list = []
    for item in best_itinerary:
        meeting = item['meeting']
        output_list.append({
            "action": "meet",
            "location": meeting['location'],
            "person": meeting['name'],
            "start_time": minutes_to_time(item['start']),
            "end_time": minutes_to_time(item['end'])
        })
    
    print(json.dumps({"itinerary": output_list}, indent=2))

if __name__ == "__main__":
    main()