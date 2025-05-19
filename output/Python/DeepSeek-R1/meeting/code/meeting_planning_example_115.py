import json

def time_to_min(time_str):
    hours, mins = map(int, time_str.split(':'))
    return hours * 60 + mins

def min_to_time(mins):
    return f"{mins // 60}:{mins % 60:02d}"

travel_times = {
    'Richmond District': {'Pacific Heights': 10, 'Marina District': 9},
    'Pacific Heights': {'Richmond District': 12, 'Marina District': 6},
    'Marina District': {'Richmond District': 11, 'Pacific Heights': 7}
}

start_time = time_to_min('9:00')
carol_available = (time_to_min('11:30'), time_to_min('15:00'))
jessica_available = (time_to_min('15:30'), time_to_min('16:45'))

best = None
for carol_start in range(carol_available[1] - 60, carol_available[0] - 1, -1):
    if carol_start < carol_available[0]:
        continue
    departure = carol_start - travel_times['Richmond District']['Marina District']
    if departure < start_time:
        continue
    
    arrival_jessica = carol_start + 60 + travel_times['Marina District']['Pacific Heights']
    jessica_start = max(arrival_jessica, jessica_available[0])
    if jessica_start + 45 > jessica_available[1]:
        continue
    
    best = {
        'carol': (carol_start, carol_start + 60),
        'jessica': (jessica_start, jessica_start + 45)
    }
    break

itinerary = []
if best:
    itinerary.append({
        "action": "meet", "location": "Marina District", "person": "Carol",
        "start_time": min_to_time(best['carol'][0]), "end_time": min_to_time(best['carol'][1])
    })
    itinerary.append({
        "action": "meet", "location": "Pacific Heights", "person": "Jessica",
        "start_time": min_to_time(best['jessica'][0]), "end_time": min_to_time(best['jessica'][1])
    })

print(json.dumps({"itinerary": itinerary}, indent=2))