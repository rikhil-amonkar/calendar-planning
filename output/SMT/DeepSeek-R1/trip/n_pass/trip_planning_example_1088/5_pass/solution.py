from itertools import permutations

def plan_trip(events_data):
    events = events_data
    total_days = 21
    for perm in permutations(events):
        current_day = 1
        itinerary = []
        valid = True
        for event in perm:
            s = max(current_day, event['earliest_start'])
            latest_start = event['latest_end'] - event['consecutive_days'] + 1
            if s > latest_start:
                valid = False
                break
            end_day = s + event['consecutive_days'] - 1
            if end_day > event['latest_end']:
                valid = False
                break
            itinerary.append((event['city'], s, end_day))
            current_day = end_day + 1
        if valid and current_day == total_days + 1:
            result = []
            for (city, start, end) in itinerary:
                if start == end:
                    day_range = f"Day {start}"
                else:
                    day_range = f"Day {start}-{end}"
                result.append({'day_range': day_range, 'place': city})
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