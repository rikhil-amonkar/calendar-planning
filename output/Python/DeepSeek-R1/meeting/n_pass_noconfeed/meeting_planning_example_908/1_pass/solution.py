import json

def main():
    # Define travel times dictionary
    travel_times = {
        "Financial District": {
            "Fisherman's Wharf": 10,
            "Presidio": 22,
            "Bayview": 19,
            "Haight-Ashbury": 19,
            "Russian Hill": 11,
            "The Castro": 20,
            "Marina District": 15,
            "Richmond District": 21,
            "Union Square": 9,
            "Sunset District": 30
        },
        "Fisherman's Wharf": {
            "Financial District": 11,
            "Presidio": 17,
            "Bayview": 26,
            "Haight-Ashbury": 22,
            "Russian Hill": 7,
            "The Castro": 27,
            "Marina District": 9,
            "Richmond District": 18,
            "Union Square": 13,
            "Sunset District": 27
        },
        "Presidio": {
            "Financial District": 23,
            "Fisherman's Wharf": 19,
            "Bayview": 31,
            "Haight-Ashbury": 15,
            "Russian Hill": 14,
            "The Castro": 21,
            "Marina District": 11,
            "Richmond District": 7,
            "Union Square": 22,
            "Sunset District": 15
        },
        "Bayview": {
            "Financial District": 19,
            "Fisherman's Wharf": 25,
            "Presidio": 32,
            "Haight-Ashbury": 19,
            "Russian Hill": 23,
            "The Castro": 19,
            "Marina District": 27,
            "Richmond District": 25,
            "Union Square": 18,
            "Sunset District": 23
        },
        "Haight-Ashbury": {
            "Financial District": 21,
            "Fisherman's Wharf": 23,
            "Presidio": 15,
            "Bayview": 18,
            "Russian Hill": 17,
            "The Castro": 6,
            "Marina District": 17,
            "Richmond District": 10,
            "Union Square": 19,
            "Sunset District": 15
        },
        "Russian Hill": {
            "Financial District": 11,
            "Fisherman's Wharf": 7,
            "Presidio": 14,
            "Bayview": 23,
            "Haight-Ashbury": 17,
            "The Castro": 21,
            "Marina District": 7,
            "Richmond District": 14,
            "Union Square": 10,
            "Sunset District": 23
        },
        "The Castro": {
            "Financial District": 21,
            "Fisherman's Wharf": 24,
            "Presidio": 20,
            "Bayview": 19,
            "Haight-Ashbury": 6,
            "Russian Hill": 18,
            "Marina District": 21,
            "Richmond District": 16,
            "Union Square": 19,
            "Sunset District": 17
        },
        "Marina District": {
            "Financial District": 17,
            "Fisherman's Wharf": 10,
            "Presidio": 10,
            "Bayview": 27,
            "Haight-Ashbury": 16,
            "Russian Hill": 8,
            "The Castro": 22,
            "Richmond District": 11,
            "Union Square": 16,
            "Sunset District": 19
        },
        "Richmond District": {
            "Financial District": 22,
            "Fisherman's Wharf": 18,
            "Presidio": 7,
            "Bayview": 27,
            "Haight-Ashbury": 10,
            "Russian Hill": 13,
            "The Castro": 16,
            "Marina District": 9,
            "Union Square": 21,
            "Sunset District": 11
        },
        "Union Square": {
            "Financial District": 9,
            "Fisherman's Wharf": 15,
            "Presidio": 24,
            "Bayview": 15,
            "Haight-Ashbury": 18,
            "Russian Hill": 13,
            "The Castro": 17,
            "Marina District": 18,
            "Richmond District": 20,
            "Sunset District": 27
        },
        "Sunset District": {
            "Financial District": 30,
            "Fisherman's Wharf": 29,
            "Presidio": 16,
            "Bayview": 22,
            "Haight-Ashbury": 15,
            "Russian Hill": 24,
            "The Castro": 17,
            "Marina District": 21,
            "Richmond District": 12,
            "Union Square": 30
        }
    }
    
    # Helper function to convert time string to minutes from 9:00 AM
    def time_str_to_minutes(s):
        s = s.strip().upper()
        if s.endswith('AM') or s.endswith('PM'):
            time_part = s[:-2].strip()
            period = s[-2:]
        else:
            time_part = s
            period = ''
        parts = time_part.split(':')
        hour = int(parts[0])
        minute = int(parts[1])
        if period == 'PM' and hour != 12:
            hour += 12
        if period == 'AM' and hour == 12:
            hour = 0
        total_minutes = hour * 60 + minute
        return total_minutes - 540  # 9:00 AM is 540 minutes from midnight
    
    # Define friends with their constraints
    friends = [
        {'name': 'Mark', 'location': "Fisherman's Wharf", 'start': time_str_to_minutes('8:15AM'), 'end': time_str_to_minutes('10:00AM'), 'duration': 30},
        {'name': 'Stephanie', 'location': 'Presidio', 'start': time_str_to_minutes('12:15PM'), 'end': time_str_to_minutes('3:00PM'), 'duration': 75},
        {'name': 'Betty', 'location': 'Bayview', 'start': time_str_to_minutes('7:15AM'), 'end': time_str_to_minutes('8:30PM'), 'duration': 15},
        {'name': 'Lisa', 'location': 'Haight-Ashbury', 'start': time_str_to_minutes('3:30PM'), 'end': time_str_to_minutes('6:30PM'), 'duration': 45},
        {'name': 'William', 'location': 'Russian Hill', 'start': time_str_to_minutes('6:45PM'), 'end': time_str_to_minutes('8:00PM'), 'duration': 60},
        {'name': 'Brian', 'location': 'The Castro', 'start': time_str_to_minutes('9:15AM'), 'end': time_str_to_minutes('1:15PM'), 'duration': 30},
        {'name': 'Joseph', 'location': 'Marina District', 'start': time_str_to_minutes('10:45AM'), 'end': time_str_to_minutes('3:00PM'), 'duration': 90},
        {'name': 'Ashley', 'location': 'Richmond District', 'start': time_str_to_minutes('9:45AM'), 'end': time_str_to_minutes('11:15AM'), 'duration': 45},
        {'name': 'Patricia', 'location': 'Union Square', 'start': time_str_to_minutes('4:30PM'), 'end': time_str_to_minutes('8:00PM'), 'duration': 120},
        {'name': 'Karen', 'location': 'Sunset District', 'start': time_str_to_minutes('4:30PM'), 'end': time_str_to_minutes('10:00PM'), 'duration': 105}
    ]
    
    # Initialize DFS
    stack = []
    start_location = "Financial District"
    start_time = 0  # 9:00 AM
    start_visited = frozenset()
    start_path = []
    stack.append((start_location, start_time, start_visited, start_path))
    
    memo = {}
    best_count = 0
    best_path = None
    
    # DFS
    while stack:
        loc, time, visited, path = stack.pop()
        state_key = (loc, visited)
        if state_key in memo and memo[state_key] <= time:
            continue
        memo[state_key] = time
        
        # Update best_path if current state has more meetings
        if len(visited) > best_count:
            best_count = len(visited)
            best_path = path
        
        # Try to extend the schedule
        for friend in friends:
            if friend['name'] in visited:
                continue
            try:
                tt = travel_times[loc][friend['location']]
            except KeyError:
                continue
            arrival = time + tt
            meeting_start = max(arrival, friend['start'])
            meeting_end = meeting_start + friend['duration']
            if meeting_end > friend['end']:
                continue
            new_loc = friend['location']
            new_time = meeting_end
            new_visited = visited | {friend['name']}
            new_path = path + [(friend['name'], friend['location'], meeting_start, meeting_end)]
            new_state_key = (new_loc, new_visited)
            if new_state_key in memo and memo[new_state_key] <= new_time:
                continue
            stack.append((new_loc, new_time, new_visited, new_path))
    
    # Convert best_path to itinerary
    def minutes_to_time(minutes):
        total_minutes = minutes + 540
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour}:{minute:02d}"
    
    itinerary = []
    if best_path is not None:
        for meeting in best_path:
            name, location, start_minutes, end_minutes = meeting
            start_time = minutes_to_time(start_minutes)
            end_time = minutes_to_time(end_minutes)
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": name,
                "start_time": start_time,
                "end_time": end_time
            })
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()