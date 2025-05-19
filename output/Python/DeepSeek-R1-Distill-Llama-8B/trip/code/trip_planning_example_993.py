import json

def main():
    city_days = {
        'Riga': (1, 2),
        'Frankfurt': (3, 5),
        'Amsterdam': (7, 8),
        'Vilnius': (7, 11),
        'London': (13, 14),
        'Stockholm': (13, 15),
        'Bucharest': (10, 13),
    }

    flights = {
        ('London', 'Amsterdam'): [1, 2, 3],
        ('Vilnius', 'Frankfurt'): [4, 5, 6],
        ('Riga', 'Vilnius'): [7, 8, 9],
        ('Riga', 'Stockholm'): [10, 11, 12],
        ('London', 'Bucharest'): [13, 14, 15],
        ('Amsterdam', 'Stockholm'): [16, 17, 18],
        ('Amsterdam', 'Frankfurt'): [19, 20, 21],
        ('Frankfurt', 'Stockholm'): [22, 23, 24],
        ('Bucharest', 'Riga'): [25, 26, 27],
        ('Amsterdam', 'Riga'): [28, 29, 30],
        ('Amsterdam', 'Bucharest'): [31, 32, 33],
        ('Riga', 'Frankfurt'): [34, 35, 36],
        ('Bucharest', 'Frankfurt'): [37, 38, 39],
        ('London', 'Frankfurt'): [40, 41, 42],
        ('London', 'Stockholm'): [43, 44, 45],
        ('Amsterdam', 'Vilnius'): [46, 47, 48],
    }

    result = []

    def backtrack(current, next_city, next_day):
        if next_day > 15:
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
    for city in ['Riga']:
        start, end = city_days[city]
        initial.append({'day_range': f'Day {start}-{end}', 'place': city})

    itinerary = backtrack(initial, 'Riga', 1)

    if itinerary:
        print(json.dumps(itinerary))
    else:
        print("No valid itinerary found")

if __name__ == "__main__":
    main()