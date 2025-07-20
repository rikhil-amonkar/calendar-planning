def plan_trip(events_data):
    events = events_data
    total_days = 21
    from itertools import permutations
    for perm in permutations(events):
        current_day = 1
        valid = True
        itinerary = []
        for event in perm:
            con = event['consecutive_days']
            start = current_day
            end = current_day + con - 1
            if start < event['earliest_start'] or end > event['latest_end']:
                valid = False
                break
            itinerary.append((event['city'], start, end))
            current_day = end + 1
        if valid and current_day == total_days + 1:
            result = []
            for (city, start, end) in itinerary:
                if start == end:
                    day_range_str = f"Day {start}"
                else:
                    day_range_str = f"Day {start}-{end}"
                result.append({'day_range': day_range_str, 'place': city})
            return {'itinerary': result}
    return "Impossible"

events = [
    {"city": "Reykjavik", "consecutive_days": 2, "earliest_start": 1, "latest_end": 21},
    {"city": "Tallinn", "consecutive_days": 4, "earliest_start": 2, "latest_end": 6},
    {"city": "Oslo", "consecutive_days": 4, "earliest_start": 6, "latest_end": 10},
    {"city": "Split", "consecutive_days": 2, "earliest_start": 10, "latest_end": 12},
    {"city": "Stuttgart", "consecutive_days": 4, "earliest_start": 12, "latest_end": 16},
    {"city": "Stockholm", "consecutive_days": 2, "earliest_start": 2, "latest_end": 4},
    {"city": "Geneva", "consecutive_days": 1, "earliest_start": 18, "latest_end": 19},
    {"city": "Porto", "consecutive_days": 2, "earliest_start": 19, "latest_end": 21}
]

result = plan_trip(events)
print(result)