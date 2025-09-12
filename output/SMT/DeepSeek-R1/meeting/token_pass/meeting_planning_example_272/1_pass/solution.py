import json
from z3 import *
from itertools import combinations, permutations

def min_to_time(m):
    total_minutes = 540 + m
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours}:{minutes:02d}"

travel_times = {
    'Russian Hill': {'Nob Hill': 5, 'Mission District': 16, 'Embarcadero': 8},
    'Nob Hill': {'Russian Hill': 5, 'Mission District': 13, 'Embarcadero': 9},
    'Mission District': {'Russian Hill': 15, 'Nob Hill': 12, 'Embarcadero': 19},
    'Embarcadero': {'Russian Hill': 8, 'Nob Hill': 10, 'Mission District': 20}
}

meetings = [
    {'person': 'Patricia', 'location': 'Nob Hill', 'avail_start': 570, 'avail_end': 765, 'min_duration': 90},
    {'person': 'Ashley', 'location': 'Mission District', 'avail_start': 690, 'avail_end': 735, 'min_duration': 45},
    {'person': 'Timothy', 'location': 'Embarcadero', 'avail_start': 45, 'avail_end': 525, 'min_duration': 120}
]

found_schedule = None
for num_meetings in range(3, 0, -1):
    for subset in combinations(meetings, num_meetings):
        for order in permutations(subset):
            s = Solver()
            starts = [Int(f"start_{i}") for i in range(num_meetings)]
            ends = [Int(f"end_{i}") for i in range(num_meetings)]
            
            first_travel = travel_times['Russian Hill'][order[0]['location']]
            s.add(starts[0] >= first_travel)
            
            for i, meeting in enumerate(order):
                s.add(starts[i] >= meeting['avail_start'])
                s.add(ends[i] <= meeting['avail_end'])
                s.add(ends[i] - starts[i] >= meeting['min_duration'])
            
            for i in range(1, num_meetings):
                travel = travel_times[order[i-1]['location']][order[i]['location']]
                s.add(starts[i] >= ends[i-1] + travel)
            
            if s.check() == sat:
                m = s.model()
                itinerary = []
                for i, meeting in enumerate(order):
                    start_val = m.eval(starts[i]).as_long()
                    end_val = m.eval(ends[i]).as_long()
                    itinerary.append({
                        "action": "meet",
                        "location": meeting['location'],
                        "person": meeting['person'],
                        "start_time": min_to_time(start_val),
                        "end_time": min_to_time(end_val)
                    })
                found_schedule = itinerary
                break
        if found_schedule:
            break
    if found_schedule:
        break

if found_schedule is None:
    found_schedule = []

print(json.dumps({"itinerary": found_schedule}, indent=2))