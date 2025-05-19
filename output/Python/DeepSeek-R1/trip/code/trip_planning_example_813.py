import json

def main():
    cities = {
        'Seville': 5,
        'Vilnius': 3,
        'Santorini': 2,
        'London': 2,
        'Stuttgart': 3,
        'Dublin': 3,
        'Frankfurt': 5
    }
    
    flights = {
        'Frankfurt': ['Dublin', 'London', 'Vilnius', 'Stuttgart'],
        'Dublin': ['Frankfurt', 'London', 'Seville', 'Santorini'],
        'London': ['Frankfurt', 'Dublin', 'Santorini', 'Stuttgart'],
        'Vilnius': ['Frankfurt'],
        'Stuttgart': ['Frankfurt', 'London'],
        'Santorini': ['London', 'Dublin'],
        'Seville': ['Dublin']
    }
    
    itinerary = []
    
    # Assign fixed Stuttgart and London constraints
    itinerary.append({'day_range': 'Day 7-9', 'place': 'Stuttgart'})
    itinerary.append({'day_range': 'Day 9-10', 'place': 'London'})
    
    # Build pre-Stuttgart path
    pre_blocks = [
        ('Vilnius', 3, 1),
        ('Frankfurt', 5, 3)
    ]
    for city, duration, start in pre_blocks:
        end = start + duration - 1
        if end >= 7: end = 7  # Ensure flight to Stuttgart on day 7
        itinerary.append({'day_range': f'Day {start}-{end}', 'place': city})
    
    # Build post-London path
    post_blocks = [
        ('Santorini', 2, 10),
        ('Dublin', 3, 11),
        ('Seville', 5, 13)
    ]
    for city, duration, start in post_blocks:
        end = start + duration - 1
        itinerary.append({'day_range': f'Day {start}-{end}', 'place': city})
    
    # Validate flight connections
    ordered = sorted(itinerary, key=lambda x: int(x['day_range'].split('-')[0].split()[1]))
    path = [block['place'] for block in ordered]
    for i in range(1, len(path)):
        prev = path[i-1]
        curr = path[i]
        if curr not in flights[prev]:
            raise ValueError(f"No flight from {prev} to {curr}")
    
    # Ensure all cities are included
    visited = set(block['place'] for block in ordered)
    if visited != set(cities.keys()):
        raise ValueError("Missing cities in itinerary")
    
    # Ensure total days
    last_day = max(int(block['day_range'].split('-')[1].split()[1]) for block in ordered)
    if last_day != 17:
        raise ValueError("Itinerary exceeds 17 days")
    
    print(json.dumps({'itinerary': ordered}, indent=2))

if __name__ == "__main__":
    main()