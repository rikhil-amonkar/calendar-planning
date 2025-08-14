import itertools
import json

def main():
    cities = ['Amsterdam', 'Vienna', 'Santorini', 'Lyon']
    allowed_flights = {
        'Amsterdam': ['Vienna', 'Santorini'],
        'Vienna': ['Amsterdam', 'Lyon', 'Santorini'],
        'Lyon': ['Vienna', 'Amsterdam'],
        'Santorini': ['Vienna', 'Amsterdam']
    }
    durations = {
        'Amsterdam': 3,
        'Vienna': 7,
        'Santorini': 4,
        'Lyon': 3
    }
    
    for perm in itertools.permutations(cities):
        valid_sequence = True
        for i in range(len(perm) - 1):
            current = perm[i]
            next_city = perm[i + 1]
            if next_city not in allowed_flights[current]:
                valid_sequence = False
                break
        if not valid_sequence:
            continue
        
        day_ranges = []
        current_day = 1
        for city in perm:
            dur = durations[city]
            end_day = current_day + dur - 1
            day_ranges.append((current_day, end_day, city))
            current_day = end_day
        
        if day_ranges[-1][1] != 14:
            continue
        
        lyon_days = None
        for dr in day_ranges:
            if dr[2] == 'Lyon':
                lyon_days = (dr[0], dr[1])
        if not lyon_days:
            continue
        
        overlap_start = max(lyon_days[0], 7)
        overlap_end = min(lyon_days[1], 9)
        if overlap_start > overlap_end:
            continue
        
        amsterdam_days = None
        for dr in day_ranges:
            if dr[2] == 'Amsterdam':
                amsterdam_days = (dr[0], dr[1])
        if not amsterdam_days:
            continue
        
        overlap_start_a = max(amsterdam_days[0], 9)
        overlap_end_a = min(amsterdam_days[1], 11)
        if overlap_start_a > overlap_end_a:
            continue
        
        itinerary = []
        for start, end, city in day_ranges:
            day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": city})
        
        print(json.dumps({"itinerary": itinerary}))
        return

if __name__ == "__main__":
    main()