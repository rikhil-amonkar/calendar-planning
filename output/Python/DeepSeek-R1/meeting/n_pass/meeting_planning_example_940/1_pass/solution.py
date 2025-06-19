import json

def main():
    travel_times = {
        "Union Square": {
            "Mission District": 14,
            "Fisherman's Wharf": 15,
            "Russian Hill": 13,
            "Marina District": 18,
            "North Beach": 10,
            "Chinatown": 7,
            "Pacific Heights": 15,
            "The Castro": 17,
            "Nob Hill": 9,
            "Sunset District": 27
        },
        "Mission District": {
            "Union Square": 15,
            "Fisherman's Wharf": 22,
            "Russian Hill": 15,
            "Marina District": 19,
            "North Beach": 17,
            "Chinatown": 16,
            "Pacific Heights": 16,
            "The Castro": 7,
            "Nob Hill": 12,
            "Sunset District": 24
        },
        "Fisherman's Wharf": {
            "Union Square": 13,
            "Mission District": 22,
            "Russian Hill": 7,
            "Marina District": 9,
            "North Beach": 6,
            "Chinatown": 12,
            "Pacific Heights": 12,
            "The Castro": 27,
            "Nob Hill": 11,
            "Sunset District": 27
        },
        "Russian Hill": {
            "Union Square": 10,
            "Mission District": 16,
            "Fisherman's Wharf": 7,
            "Marina District": 7,
            "North Beach": 5,
            "Chinatown": 9,
            "Pacific Heights": 7,
            "The Castro": 21,
            "Nob Hill": 5,
            "Sunset District": 23
        },
        "Marina District": {
            "Union Square": 16,
            "Mission District": 20,
            "Fisherman's Wharf": 10,
            "Russian Hill": 8,
            "North Beach": 11,
            "Chinatown": 15,
            "Pacific Heights": 7,
            "The Castro": 22,
            "Nob Hill": 12,
            "Sunset District": 19
        },
        "North Beach": {
            "Union Square": 7,
            "Mission District": 18,
            "Fisherman's Wharf": 5,
            "Russian Hill": 4,
            "Marina District": 9,
            "Chinatown": 6,
            "Pacific Heights": 8,
            "The Castro": 23,
            "Nob Hill": 7,
            "Sunset District": 27
        },
        "Chinatown": {
            "Union Square": 7,
            "Mission District": 17,
            "Fisherman's Wharf": 8,
            "Russian Hill": 7,
            "Marina District": 12,
            "North Beach": 3,
            "Pacific Heights": 10,
            "The Castro": 22,
            "Nob Hill": 9,
            "Sunset District": 29
        },
        "Pacific Heights": {
            "Union Square": 12,
            "Mission District": 15,
            "Fisherman's Wharf": 13,
            "Russian Hill": 7,
            "Marina District": 6,
            "North Beach": 9,
            "Chinatown": 11,
            "The Castro": 16,
            "Nob Hill": 8,
            "Sunset District": 21
        },
        "The Castro": {
            "Union Square": 19,
            "Mission District": 7,
            "Fisherman's Wharf": 24,
            "Russian Hill": 18,
            "Marina District": 21,
            "North Beach": 20,
            "Chinatown": 22,
            "Pacific Heights": 16,
            "Nob Hill": 16,
            "Sunset District": 17
        },
        "Nob Hill": {
            "Union Square": 7,
            "Mission District": 13,
            "Fisherman's Wharf": 10,
            "Russian Hill": 5,
            "Marina District": 11,
            "North Beach": 8,
            "Chinatown": 6,
            "Pacific Heights": 8,
            "The Castro": 17,
            "Sunset District": 24
        },
        "Sunset District": {
            "Union Square": 30,
            "Mission District": 25,
            "Fisherman's Wharf": 29,
            "Russian Hill": 24,
            "Marina District": 21,
            "North Beach": 28,
            "Chinatown": 30,
            "Pacific Heights": 21,
            "The Castro": 17,
            "Nob Hill": 27
        }
    }

    friends = [
        {'name': 'Kevin', 'location': 'Mission District', 'start': 20*60+45, 'end': 21*60+45, 'min_duration': 60},
        {'name': 'Mark', 'location': "Fisherman's Wharf", 'start': 17*60+15, 'end': 20*60+0, 'min_duration': 90},
        {'name': 'Jessica', 'location': 'Russian Hill', 'start': 9*60+0, 'end': 15*60+0, 'min_duration': 120},
        {'name': 'Jason', 'location': 'Marina District', 'start': 15*60+15, 'end': 21*60+45, 'min_duration': 120},
        {'name': 'John', 'location': 'North Beach', 'start': 9*60+45, 'end': 18*60+0, 'min_duration': 15},
        {'name': 'Karen', 'location': 'Chinatown', 'start': 16*60+45, 'end': 19*60+0, 'min_duration': 75},
        {'name': 'Sarah', 'location': 'Pacific Heights', 'start': 17*60+30, 'end': 18*60+15, 'min_duration': 45},
        {'name': 'Amanda', 'location': 'The Castro', 'start': 20*60+0, 'end': 21*60+15, 'min_duration': 60},
        {'name': 'Nancy', 'location': 'Nob Hill', 'start': 9*60+45, 'end': 13*60+0, 'min_duration': 45},
        {'name': 'Rebecca', 'location': 'Sunset District', 'start': 8*60+45, 'end': 15*60+0, 'min_duration': 75}
    ]

    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours}:{mins:02d}"

    n = len(friends)
    memo = {}

    def dfs(loc, mask, time):
        key = (loc, mask, time)
        if key in memo:
            return memo[key]
        
        best_count = 0
        best_path = []
        
        for i in range(n):
            if mask & (1 << i):
                continue
            f = friends[i]
            if loc == f['location']:
                travel_dur = 0
            else:
                travel_dur = travel_times[loc][f['location']]
                
            arrival_time = time + travel_dur
            start_time = max(arrival_time, f['start'])
            end_time = start_time + f['min_duration']
            
            if end_time <= f['end']:
                new_time = end_time
                new_loc = f['location']
                new_mask = mask | (1 << i)
                count, path = dfs(new_loc, new_mask, new_time)
                count += 1
                if count > best_count:
                    best_count = count
                    meeting = {
                        'action': 'meet',
                        'location': f['location'],
                        'person': f['name'],
                        'start_time': minutes_to_time(start_time),
                        'end_time': minutes_to_time(end_time)
                    }
                    best_path = [meeting] + path
                    
        memo[key] = (best_count, best_path)
        return (best_count, best_path)

    start_loc = 'Union Square'
    start_time_minutes = 9 * 60
    mask = 0
    best_count, best_path = dfs(start_loc, mask, start_time_minutes)

    result = {
        "itinerary": best_path
    }
    print(json.dumps(result))

if __name__ == "__main__":
    main()