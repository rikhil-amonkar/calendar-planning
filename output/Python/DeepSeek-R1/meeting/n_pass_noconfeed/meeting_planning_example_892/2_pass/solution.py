import json
from collections import deque

def main():
    def time_to_minutes(time_str):
        period = None
        if time_str.endswith('AM') or time_str.endswith('PM'):
            period = time_str[-2:]
            time_str = time_str[:-2].strip()
        parts = time_str.split(':')
        hour = int(parts[0])
        minute = int(parts[1]) if len(parts) > 1 else 0
        if period == 'PM' and hour != 12:
            hour += 12
        if period == 'AM' and hour == 12:
            hour = 0
        return hour * 60 + minute

    travel_times = {
        'Marina District': {'Bayview': 27, 'Sunset District': 19, 'Richmond District': 11, 'Nob Hill': 12, 'Chinatown': 15, 'Haight-Ashbury': 16, 'North Beach': 11, 'Russian Hill': 8, 'Embarcadero': 14},
        'Bayview': {'Marina District': 27, 'Sunset District': 23, 'Richmond District': 25, 'Nob Hill': 20, 'Chinatown': 19, 'Haight-Ashbury': 19, 'North Beach': 22, 'Russian Hill': 23, 'Embarcadero': 19},
        'Sunset District': {'Marina District': 21, 'Bayview': 22, 'Richmond District': 12, 'Nob Hill': 27, 'Chinatown': 30, 'Haight-Ashbury': 15, 'North Beach': 28, 'Russian Hill': 24, 'Embarcadero': 30},
        'Richmond District': {'Marina District': 9, 'Bayview': 27, 'Sunset District': 11, 'Nob Hill': 17, 'Chinatown': 20, 'Haight-Ashbury': 10, 'North Beach': 17, 'Russian Hill': 13, 'Embarcadero': 19},
        'Nob Hill': {'Marina District': 11, 'Bayview': 19, 'Sunset District': 24, 'Richmond District': 14, 'Chinatown': 6, 'Haight-Ashbury': 13, 'North Beach': 8, 'Russian Hill': 5, 'Embarcadero': 9},
        'Chinatown': {'Marina District': 12, 'Bayview': 20, 'Sunset District': 29, 'Richmond District': 20, 'Nob Hill': 9, 'Haight-Ashbury': 19, 'North Beach': 3, 'Russian Hill': 7, 'Embarcadero': 5},
        'Haight-Ashbury': {'Marina District': 17, 'Bayview': 18, 'Sunset District': 15, 'Richmond District': 10, 'Nob Hill': 15, 'Chinatown': 19, 'North Beach': 19, 'Russian Hill': 17, 'Embarcadero': 20},
        'North Beach': {'Marina District': 9, 'Bayview': 25, 'Sunset District': 27, 'Richmond District': 18, 'Nob Hill': 7, 'Chinatown': 6, 'Haight-Ashbury': 18, 'Russian Hill': 4, 'Embarcadero': 6},
        'Russian Hill': {'Marina District': 7, 'Bayview': 23, 'Sunset District': 23, 'Richmond District': 14, 'Nob Hill': 5, 'Chinatown': 9, 'Haight-Ashbury': 17, 'North Beach': 5, 'Embarcadero': 8},
        'Embarcadero': {'Marina District': 12, 'Bayview': 21, 'Sunset District': 30, 'Richmond District': 21, 'Nob Hill': 10, 'Chinatown': 7, 'Haight-Ashbury': 21, 'North Beach': 5, 'Russian Hill': 8}
    }

    friends = [
        {'name': 'Charles', 'location': 'Bayview', 'start': time_to_minutes('11:30'), 'end': time_to_minutes('2:30PM'), 'dur': 45},
        {'name': 'Robert', 'location': 'Sunset District', 'start': time_to_minutes('4:45PM'), 'end': time_to_minutes('9:00PM'), 'dur': 30},
        {'name': 'Karen', 'location': 'Richmond District', 'start': time_to_minutes('7:15PM'), 'end': time_to_minutes('9:30PM'), 'dur': 60},
        {'name': 'Rebecca', 'location': 'Nob Hill', 'start': time_to_minutes('4:15PM'), 'end': time_to_minutes('8:30PM'), 'dur': 90},
        {'name': 'Margaret', 'location': 'Chinatown', 'start': time_to_minutes('2:15PM'), 'end': time_to_minutes('7:45PM'), 'dur': 120},
        {'name': 'Patricia', 'location': 'Haight-Ashbury', 'start': time_to_minutes('2:30PM'), 'end': time_to_minutes('8:30PM'), 'dur': 45},
        {'name': 'Mark', 'location': 'North Beach', 'start': time_to_minutes('2:00PM'), 'end': time_to_minutes('6:30PM'), 'dur': 105},
        {'name': 'Melissa', 'location': 'Russian Hill', 'start': time_to_minutes('1:00PM'), 'end': time_to_minutes('7:45PM'), 'dur': 30},
        {'name': 'Laura', 'location': 'Embarcadero', 'start': time_to_minutes('7:45AM'), 'end': time_to_minutes('1:15PM'), 'dur': 105}
    ]

    start_time = time_to_minutes('9:00AM')
    start_location = 'Marina District'

    best_path = []
    best_count = 0
    queue = deque()
    queue.append((0, start_location, start_time, []))  # (visited_bitmask, current_location, current_time, path)

    while queue:
        visited, loc, time, path = queue.popleft()
        count = bin(visited).count("1")
        if count > best_count:
            best_count = count
            best_path = path

        for idx, friend in enumerate(friends):
            if visited & (1 << idx):
                continue
            if loc in travel_times and friend['location'] in travel_times[loc]:
                travel_duration = travel_times[loc][friend['location']]
                arrival_time = time + travel_duration
                start_meeting = max(arrival_time, friend['start'])
                end_meeting = start_meeting + friend['dur']
                if end_meeting <= friend['end']:
                    new_visited = visited | (1 << idx)
                    new_loc = friend['location']
                    new_path = path + [{
                        'name': friend['name'],
                        'location': new_loc,
                        'start': start_meeting,
                        'end': end_meeting
                    }]
                    queue.append((new_visited, new_loc, end_meeting, new_path))

    def format_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours}:{mins:02d}"

    itinerary = []
    for meeting in best_path:
        itinerary.append({
            "action": "meet",
            "location": meeting['location'],
            "person": meeting['name'],
            "start_time": format_time(meeting['start']),
            "end_time": format_time(meeting['end'])
        })

    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()