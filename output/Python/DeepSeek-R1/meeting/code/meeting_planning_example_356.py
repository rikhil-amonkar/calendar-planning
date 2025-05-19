import itertools
import json

friends = [
    {'name': 'Barbara', 'location': 'North Beach', 'start': 825, 'end': 1215, 'duration': 60},
    {'name': 'Margaret', 'location': 'Presidio', 'start': 615, 'end': 915, 'duration': 30},
    {'name': 'Kevin', 'location': 'Haight-Ashbury', 'start': 1200, 'end': 1245, 'duration': 30},
    {'name': 'Kimberly', 'location': 'Union Square', 'start': 465, 'end': 1005, 'duration': 30}
]

travel_times = {
    'Bayview': {'North Beach':21,'Presidio':31,'Haight-Ashbury':19,'Union Square':17},
    'North Beach': {'Bayview':22,'Presidio':17,'Haight-Ashbury':18,'Union Square':7},
    'Presidio': {'Bayview':31,'North Beach':18,'Haight-Ashbury':15,'Union Square':22},
    'Haight-Ashbury': {'Bayview':18,'North Beach':19,'Presidio':15,'Union Square':17},
    'Union Square': {'Bayview':15,'North Beach':10,'Presidio':24,'Haight-Ashbury':18}
}

def format_time(mins):
    return f"{mins//60}:{mins%60:02d}"

def compute():
    best = []
    max_met = 0
    min_end = float('inf')
    
    for perm in itertools.permutations(friends):
        current_loc = 'Bayview'
        current_time = 540
        itinerary = []
        valid = True
        
        for f in perm:
            travel = travel_times[current_loc].get(f['location'], None)
            if not travel:
                valid = False
                break
            arrive = current_time + travel
            start = max(arrive, f['start'])
            latest_start = f['end'] - f['duration']
            if start > latest_start:
                valid = False
                break
            end = start + f['duration']
            itinerary.append((f, start, end))
            current_loc = f['location']
            current_time = end
        
        if valid:
            met = len(itinerary)
            if met > max_met or (met == max_met and current_time < min_end):
                best = itinerary
                max_met = met
                min_end = current_time

    result = []
    for item in best:
        f, s, e = item
        result.append({
            "action": "meet",
            "location": f['location'],
            "person": f['name'],
            "start_time": format_time(s),
            "end_time": format_time(e)
        })
    
    return {"itinerary": result}

print(json.dumps(compute(), indent=2))