if solver.check() == z3.sat:
    model = solver.model()
    visited_names = [name for name in friends if model.eval(visited[name])]
    visited_meetings = []
    for name in visited_names:
        start_val = model.eval(start_times[name]).as_long()
        duration = friends[name]['min_duration']
        end_val = start_val + duration
        visited_meetings.append({
            'name': name,
            'start': start_val,
            'end': end_val
        })
    visited_meetings.sort(key=lambda x: x['start'])

    def to_time_str(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours}:{mins:02d}"

    itinerary = []
    for item in visited_meetings:
        itinerary.append({
            "action": "meet",
            "location": friends[item['name']]['location'],
            "person": item['name'],
            "start_time": to_time_str(item['start']),
            "end_time": to_time_str(item['end'])
        })
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found.")