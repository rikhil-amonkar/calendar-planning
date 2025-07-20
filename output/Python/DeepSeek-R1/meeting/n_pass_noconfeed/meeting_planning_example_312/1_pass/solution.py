import itertools
import json

def minutes_to_time(minutes):
    total_minutes = minutes
    hours = 9 + total_minutes // 60
    mins = total_minutes % 60
    return f"{hours}:{mins:02d}"

travel_matrix = [
    [0, 11, 10, 20, 9],
    [12, 0, 15, 24, 11],
    [10, 15, 0, 11, 7],
    [20, 24, 12, 0, 17],
    [7, 10, 7, 17, 0]
]

meetings = [
    {
        "name": "Sarah",
        "location": 1,
        "start_avail": 105,
        "end_avail": 600,
        "min_dur": 30,
        "location_name": "Sunset District"
    },
    {
        "name": "Richard",
        "location": 2,
        "start_avail": 165,
        "end_avail": 405,
        "min_dur": 90,
        "location_name": "Haight-Ashbury"
    },
    {
        "name": "Elizabeth",
        "location": 3,
        "start_avail": 120,
        "end_avail": 495,
        "min_dur": 120,
        "location_name": "Mission District"
    },
    {
        "name": "Michelle",
        "location": 4,
        "start_avail": 555,
        "end_avail": 705,
        "min_dur": 90,
        "location_name": "Golden Gate Park"
    }
]

best_count = 0
best_schedule = None

for perm in itertools.permutations(range(4)):
    current_time = 0
    current_location = 0
    schedule = []
    for idx in perm:
        m = meetings[idx]
        travel = travel_matrix[current_location][m['location']]
        arrival = current_time + travel
        start = max(arrival, m['start_avail'])
        if start > m['end_avail'] - m['min_dur']:
            break
        end = start + m['min_dur']
        schedule.append((idx, start, end))
        current_time = end
        current_location = m['location']
    else:
        if len(schedule) == 4:
            best_schedule = schedule
            best_count = 4
            break
    count = len(schedule)
    if count > best_count:
        best_count = count
        best_schedule = schedule

itinerary = []
if best_schedule is not None:
    for (idx, start, end) in best_schedule:
        m = meetings[idx]
        itinerary.append({
            "action": "meet",
            "location": m['location_name'],
            "person": m['name'],
            "start_time": minutes_to_time(start),
            "end_time": minutes_to_time(end)
        })

result = {
    "itinerary": itinerary
}
print(json.dumps(result))