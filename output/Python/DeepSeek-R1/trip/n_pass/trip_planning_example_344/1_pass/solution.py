import json

def main():
    total_days = 20
    cities = {
        'Athens': {'days': 6, 'fixed_start': 1, 'fixed_end': 6},
        'Naples': {'days': 5, 'fixed_start': 16, 'fixed_end': 20},
        'Valencia': {'days': 6},
        'Zurich': {'days': 6}
    }
    
    directed_flights = {
        ('Valencia', 'Athens'),
        ('Valencia', 'Naples'), ('Naples', 'Valencia'),
        ('Valencia', 'Zurich'), ('Zurich', 'Valencia'),
        ('Athens', 'Naples'), ('Naples', 'Athens'),
        ('Athens', 'Zurich'), ('Zurich', 'Athens'),
        ('Zurich', 'Naples'), ('Naples', 'Zurich')
    }
    
    segments = []
    segments.append({
        'city': 'Athens',
        'start': cities['Athens']['fixed_start'],
        'end': cities['Athens']['fixed_end']
    })
    
    segments.append({
        'city': 'Zurich',
        'start': segments[-1]['end'],
        'end': segments[-1]['end'] + cities['Zurich']['days'] - 1
    })
    
    segments.append({
        'city': 'Valencia',
        'start': segments[-1]['end'],
        'end': segments[-1]['end'] + cities['Valencia']['days'] - 1
    })
    
    segments.append({
        'city': 'Naples',
        'start': segments[-1]['end'],
        'end': segments[-1]['end'] + cities['Naples']['days'] - 1
    })
    
    itinerary_list = []
    for seg in segments:
        start = seg['start']
        end = seg['end']
        day_range_str = f"Day {start}-{end}" if start != end else f"Day {start}"
        itinerary_list.append({"day_range": day_range_str, "place": seg['city']})
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == "__main__":
    main()