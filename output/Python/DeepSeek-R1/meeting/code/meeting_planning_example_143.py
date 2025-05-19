def time_to_min(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def min_to_time(m):
    return f"{m // 60}:{m % 60:02d}"

travel_time = {
    'North Beach': {'Pacific Heights': 8, 'Embarcadero': 6},
    'Pacific Heights': {'North Beach': 9, 'Embarcadero': 10},
    'Embarcadero': {'North Beach': 5, 'Pacific Heights': 11}
}

initial_location = 'North Beach'
initial_time = time_to_min('9:00')

mark_location = 'Embarcadero'
mark_start = time_to_min('13:00')
mark_end = time_to_min('17:45')
mark_duration = 120

karen_location = 'Pacific Heights'
karen_start = time_to_min('18:45')
karen_end = time_to_min('20:15')
karen_duration = 90

latest_mark_start = mark_end - mark_duration
mark_possible = latest_mark_start >= mark_start

itinerary = []
if mark_possible:
    departure_to_mark = latest_mark_start - travel_time[initial_location][mark_location]
    if departure_to_mark < initial_time:
        departure_to_mark = initial_time
        arrival_at_mark = departure_to_mark + travel_time[initial_location][mark_location]
        mark_start_time = max(arrival_at_mark, mark_start)
        if mark_start_time + mark_duration > mark_end:
            mark_possible = False
        else:
            latest_mark_start = mark_start_time
    else:
        arrival_at_mark = latest_mark_start

    if mark_possible:
        mark_end_time = latest_mark_start + mark_duration
        arrival_at_karen = mark_end_time + travel_time[mark_location][karen_location]
        karen_start_time = max(arrival_at_karen, karen_start)
        karen_end_time = karen_start_time + karen_duration
        if karen_end_time <= karen_end:
            itinerary.append({
                "action": "meet",
                "location": mark_location,
                "person": "Mark",
                "start_time": min_to_time(latest_mark_start),
                "end_time": min_to_time(mark_end_time)
            })
            itinerary.append({
                "action": "meet",
                "location": karen_location,
                "person": "Karen",
                "start_time": min_to_time(karen_start_time),
                "end_time": min_to_time(karen_end_time)
            })

import json
print(json.dumps({"itinerary": itinerary}, indent=2))