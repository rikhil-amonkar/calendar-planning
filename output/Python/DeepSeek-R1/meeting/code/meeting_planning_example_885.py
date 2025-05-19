import json

friends = [
    {'name': 'Karen', 'location': 'Financial District', 'start': 570, 'end': 765, 'min_duration': 90},
    {'name': 'David', 'location': 'The Castro', 'start': 540, 'end': 1080, 'min_duration': 120},
    {'name': 'Barbara', 'location': 'Alamo Square', 'start': 600, 'end': 1170, 'min_duration': 90},
    {'name': 'Matthew', 'location': 'Haight-Ashbury', 'start': 615, 'end': 930, 'min_duration': 45},
    {'name': 'Andrew', 'location': 'Nob Hill', 'start': 705, 'end': 1005, 'min_duration': 105},
    {'name': 'Kevin', 'location': 'Sunset District', 'start': 600, 'end': 1065, 'min_duration': 120},
    {'name': 'Nancy', 'location': 'Golden Gate Park', 'start': 1005, 'end': 1200, 'min_duration': 105},
    {'name': 'Linda', 'location': 'Bayview', 'start': 1095, 'end': 1185, 'min_duration': 45},
    {'name': 'Mark', 'location': 'Marina District', 'start': 1125, 'end': 1260, 'min_duration': 90}
]

travel_times = {
    'Russian Hill': {'Marina District': 7, 'Financial District': 11, 'Alamo Square': 15, 'Golden Gate Park': 21, 'The Castro': 21, 'Bayview': 23, 'Sunset District': 23, 'Haight-Ashbury': 17, 'Nob Hill': 5},
    'Marina District': {'Russian Hill': 8, 'Financial District': 17, 'Alamo Square': 15, 'Golden Gate Park': 18, 'The Castro': 22, 'Bayview': 27, 'Sunset District': 19, 'Haight-Ashbury': 16, 'Nob Hill': 12},
    'Financial District': {'Russian Hill': 11, 'Marina District': 15, 'Alamo Square': 17, 'Golden Gate Park': 23, 'The Castro': 20, 'Bayview': 19, 'Sunset District': 30, 'Haight-Ashbury': 19, 'Nob Hill': 8},
    'Alamo Square': {'Russian Hill': 13, 'Marina District': 15, 'Financial District': 17, 'Golden Gate Park': 9, 'The Castro': 8, 'Bayview': 16, 'Sunset District': 16, 'Haight-Ashbury': 5, 'Nob Hill': 11},
    'Golden Gate Park': {'Russian Hill': 19, 'Marina District': 16, 'Financial District': 26, 'Alamo Square': 9, 'The Castro': 13, 'Bayview': 23, 'Sunset District': 10, 'Haight-Ashbury': 7, 'Nob Hill': 20},
    'The Castro': {'Russian Hill': 18, 'Marina District': 21, 'Financial District': 21, 'Alamo Square': 8, 'Golden Gate Park': 11, 'Bayview': 19, 'Sunset District': 17, 'Haight-Ashbury': 6, 'Nob Hill': 16},
    'Bayview': {'Russian Hill': 23, 'Marina District': 27, 'Financial District': 19, 'Alamo Square': 16, 'Golden Gate Park': 22, 'The Castro': 19, 'Sunset District': 23, 'Haight-Ashbury': 19, 'Nob Hill': 20},
    'Sunset District': {'Russian Hill': 24, 'Marina District': 21, 'Financial District': 30, 'Alamo Square': 17, 'Golden Gate Park': 11, 'The Castro': 17, 'Bayview': 22, 'Haight-Ashbury': 15, 'Nob Hill': 27},
    'Haight-Ashbury': {'Russian Hill': 17, 'Marina District': 17, 'Financial District': 21, 'Alamo Square': 5, 'Golden Gate Park': 7, 'The Castro': 6, 'Bayview': 18, 'Sunset District': 15, 'Nob Hill': 15},
    'Nob Hill': {'Russian Hill': 5, 'Marina District': 11, 'Financial District': 9, 'Alamo Square': 11, 'Golden Gate Park': 17, 'The Castro': 17, 'Bayview': 19, 'Sunset District': 24, 'Haight-Ashbury': 13}
}

def time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}".replace(":00", "").replace(":0", ":")

def main():
    best = []
    
    def backtrack(current_loc, current_time, met, itinerary):
        nonlocal best
        if len(itinerary) > len(best):
            best = itinerary.copy()
        elif len(itinerary) == len(best) and itinerary:
            if itinerary[-1]['end'] < best[-1]['end']:
                best = itinerary.copy()
        for friend in friends:
            if friend['name'] in met:
                continue
            from_loc = current_loc
            to_loc = friend['location']
            if from_loc not in travel_times or to_loc not in travel_times[from_loc]:
                continue
            travel = travel_times[from_loc][to_loc]
            arrive = current_time + travel
            start = max(arrive, friend['start'])
            end = start + friend['min_duration']
            if end > friend['end']:
                continue
            new_met = met | {friend['name']}
            new_entry = {
                'action': 'meet',
                'location': to_loc,
                'person': friend['name'],
                'start_time': start,
                'end_time': end
            }
            backtrack(to_loc, end, new_met, itinerary + [new_entry])
    
    backtrack('Russian Hill', 540, set(), [])
    
    output = {"itinerary": []}
    for entry in best:
        output["itinerary"].append({
            "action": "meet",
            "location": entry['location'],
            "person": entry['person'],
            "start_time": time_str(entry['start_time']),
            "end_time": time_str(entry['end_time'])
        })
    
    print(json.dumps(output))

if __name__ == "__main__":
    main()