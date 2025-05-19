import json

def main():
    required_days = {
        'Venice': 5,
        'Salzburg': 4,
        'Stockholm': 2,
        'Frankfurt': 4,
        'Florence': 4,
        'Barcelona': 2,
        'Stuttgart': 3
    }
    adjacency = {
        'Venice': ['Barcelona', 'Stuttgart', 'Frankfurt'],
        'Barcelona': ['Frankfurt', 'Florence', 'Stockholm', 'Stuttgart', 'Venice'],
        'Stuttgart': ['Barcelona', 'Frankfurt', 'Stockholm', 'Venice'],
        'Frankfurt': ['Barcelona', 'Florence', 'Stuttgart', 'Stockholm', 'Salzburg', 'Venice'],
        'Florence': ['Frankfurt', 'Barcelona'],
        'Stockholm': ['Barcelona', 'Frankfurt', 'Stuttgart'],
        'Salzburg': ['Frankfurt']
    }

    initial = [{'city': 'Venice', 'start': 1, 'end': 5}]
    used = {'Venice'}
    path = []

    def backtrack(current, used_cities, last_city, last_end):
        if len(used_cities) == len(required_days) and last_end == 18:
            path.extend(current)
            return True
        if last_end >= 18:
            return False
        for next_city in adjacency.get(last_city, []):
            if next_city not in used_cities:
                req = required_days[next_city]
                start = last_end
                end = start + req - 1
                if end > 18:
                    continue
                new_current = current + [{'city': next_city, 'start': start, 'end': end}]
                new_used = set(used_cities)
                new_used.add(next_city)
                if backtrack(new_current, new_used, next_city, end):
                    return True
        return False

    if backtrack(initial, used, 'Venice', 5):
        itinerary = []
        for seg in path:
            start = seg['start']
            end = seg['end']
            dr = f"Day {start}-{end}" if start != end else f"Day {start}"
            itinerary.append({'day_range': dr, 'place': seg['city']})
        print(json.dumps({'itinerary': itinerary}))
    else:
        print(json.dumps({'itinerary': []}))

if __name__ == "__main__":
    main()