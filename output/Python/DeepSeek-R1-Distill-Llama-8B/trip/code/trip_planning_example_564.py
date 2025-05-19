import json

def main():
    city_days = {
        'Istanbul': (1, 2),
        'Rome': (5, 8),
        'Seville': (10, 13),
        'Naples': (14, 20),
        'Santorini': (13, 16)
    }

    flights = {
        ('Istanbul', 'Rome'): [1, 2, 3, 4, 5],
        ('Rome', 'Santorini'): [1, 2, 3, 4, 5],
        ('Seville', 'Rome'): [1, 2, 3, 4, 5],
        ('Istanbul', 'Naples'): [1, 2, 3, 4, 5],
        ('Naples', 'Santorini'): [1, 2, 3, 4, 5],
        ('Rome', 'Naples'): [1, 2, 3, 4, 5],
        ('Rome', 'Istanbul'): [1, 2, 3, 4, 5],
    }

    result = []

    def backtrack(current, next_city, next_day):
        if next_day > 16:
            return None
        if next_city in city_days:
            start, end = city_days[next_city]
            if next_day < start or next_day > end:
                return None
        for day in flights.get((current, next_city), []):
            if day < next_day:
                continue
            new_result = current.copy()
            new_result.append({'day_range': f'Day {day+1}-{day+1}', 'place': next_city})
            res = backtrack(new_result, next_city, day + 1)
            if res is not None:
                return res
        return None

    initial = []
    for city in ['Istanbul']:
        start, end = city_days[city]
        initial.append({'day_range': f'Day {start}-{end}', 'place': city})

    itinerary = backtrack(initial, 'Istanbul', 1)

    if itinerary:
        print(json.dumps(itinerary))
    else:
        print("No valid itinerary found")

if __name__ == "__main__":
    main()