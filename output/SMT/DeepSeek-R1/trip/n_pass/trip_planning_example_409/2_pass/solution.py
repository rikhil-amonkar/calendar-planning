def generate_itinerary(events):
    if not events:
        return {"itinerary": []}
    
    max_event_day = max(event['end'] for event in events)
    max_itinerary_day = max_event_day + 1
    active = [set() for _ in range(max_itinerary_day + 2)]
    
    for event in events:
        start_it = event['start'] + 1
        end_it = event['end'] + 1
        for day in range(start_it, end_it + 1):
            if day < len(active):
                active[day].add(event['city'])
    
    itinerary_entries = []
    events_sorted = sorted(events, key=lambda x: x['start'])
    
    for event in events_sorted:
        city = event['city']
        start_it = event['start'] + 1
        end_it = event['end'] + 1
        
        if start_it < len(active) and len(active[start_it]) > 1:
            itinerary_entries.append({"day_range": f"Day {start_it}", "place": city})
            start_it += 1
            if start_it > end_it:
                continue
        
        last_day = None
        if end_it < len(active) and len(active[end_it]) > 1:
            last_day = end_it
            end_it -= 1
        
        if start_it <= end_it:
            if start_it == end_it:
                itinerary_entries.append({"day_range": f"Day {start_it}", "place": city})
            else:
                itinerary_entries.append({"day_range": f"Day {start_it}-{end_it}", "place": city})
        
        if last_day is not None:
            itinerary_entries.append({"day_range": f"Day {last_day}", "place": city})
    
    def get_start_day(entry):
        day_str = entry['day_range'].split()[1]
        if '-' in day_str:
            return int(day_str.split('-')[0])
        else:
            return int(day_str)
    
    sorted_entries = sorted(itinerary_entries, key=get_start_day)
    return {"itinerary": sorted_entries}

events = [
    {'city': 'Bucharest', 'start': 0, 'end': 1},
    {'city': 'Zurich', 'start': 1, 'end': 3},
    {'city': 'Split', 'start': 3, 'end': 9},
    {'city': 'Helsinki', 'start': 9, 'end': 10},
    {'city': 'Hamburg', 'start': 10, 'end': 11}
]

result = generate_itinerary(events)