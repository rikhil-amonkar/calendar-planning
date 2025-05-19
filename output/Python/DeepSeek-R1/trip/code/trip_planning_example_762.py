import json

def main():
    itinerary = [
        {"day_range": "Day 1-2", "place": "London"},
        {"day_range": "Day 2-3", "place": "Madrid"},
        {"day_range": "Day 3-7", "place": "Berlin"},
        {"day_range": "Day 7-9", "place": "Dublin"},
        {"day_range": "Day 9-11", "place": "Oslo"},
        {"day_range": "Day 11-13", "place": "Vilnius"}
    ]

    direct_flights = {
        'London': ['Madrid', 'Oslo', 'Dublin', 'Berlin'],
        'Madrid': ['London', 'Oslo', 'Dublin', 'Berlin'],
        'Berlin': ['Vilnius', 'Madrid', 'Oslo', 'Dublin'],
        'Dublin': ['Madrid', 'London', 'Oslo', 'Berlin'],
        'Oslo': ['London', 'Madrid', 'Berlin', 'Dublin', 'Vilnius'],
        'Vilnius': ['Oslo', 'Berlin']
    }
    valid = True
    previous = None
    for entry in itinerary:
        current = entry['place']
        if previous is not None:
            if current not in direct_flights.get(previous, []):
                valid = False
                break
        previous = current

    required_days = {
        'London': 2,
        'Madrid': 2,
        'Berlin': 5,
        'Dublin': 3,
        'Oslo': 3,
        'Vilnius': 3
    }
    days_spent = {}
    for entry in itinerary:
        city = entry['place']
        start, end = map(int, entry['day_range'].split()[1].split('-'))
        days = end - start + 1
        days_spent[city] = days_spent.get(city, 0) + days
    for city, req in required_days.items():
        if days_spent.get(city, 0) != req:
            valid = False

    date_constraints = [
        ('Madrid', 2, 3),
        ('Berlin', 3, 7),
        ('Dublin', 7, 9)
    ]
    for city, start_day, end_day in date_constraints:
        found = False
        for entry in itinerary:
            if entry['place'] == city:
                current_start, current_end = map(int, entry['day_range'].split()[1].split('-'))
                if current_start <= start_day and current_end >= end_day:
                    found = True
                    break
        if not found:
            valid = False

    print(json.dumps({'itinerary': itinerary if valid else []}))

if __name__ == "__main__":
    main()