from z3 import *
import json

def solve_itinerary():
    s = Solver()

    cities = ['Bucharest', 'Venice', 'Prague', 'Frankfurt', 'Zurich', 'Florence', 'Tallinn']
    city_vars = {city: {'start': Int(f'start_{city}'), 'end': Int(f'end_{city}')} for city in cities}

    flights = {
        'Prague': ['Tallinn', 'Zurich', 'Florence', 'Bucharest', 'Frankfurt'],
        'Tallinn': ['Prague', 'Frankfurt', 'Zurich'],
        'Zurich': ['Prague', 'Bucharest', 'Frankfurt', 'Venice', 'Florence', 'Tallinn'],
        'Florence': ['Prague', 'Frankfurt', 'Zurich'],
        'Frankfurt': ['Bucharest', 'Venice', 'Tallinn', 'Zurich', 'Prague', 'Florence'],
        'Bucharest': ['Frankfurt', 'Prague', 'Zurich'],
        'Venice': ['Frankfurt', 'Zurich']
    }

    durations = {
        'Bucharest': 3,
        'Venice': 5,
        'Prague': 4,
        'Frankfurt': 5,
        'Zurich': 5,
        'Florence': 5,
        'Tallinn': 5
    }

    # Specific constraints
    # Venice: 5 days, wedding between day 22-26. So must be in Venice during these days.
    s.add(city_vars['Venice']['start'] <= 22)
    s.add(city_vars['Venice']['end'] >= 22)
    s.add(city_vars['Venice']['end'] <= 26)
    s.add(city_vars['Venice']['end'] == city_vars['Venice']['start'] + 4)  # 5 days: start + 4 = end

    # Frankfurt: 5 days, show day 12-16. Must be in Frankfurt during these days.
    s.add(city_vars['Frankfurt']['start'] <= 12)
    s.add(city_vars['Frankfurt']['end'] >= 16)
    s.add(city_vars['Frankfurt']['end'] == city_vars['Frankfurt']['start'] + 4)  # 5 days

    # Tallinn: 5 days, friends day 8-12. Must be in Tallinn during these days.
    s.add(city_vars['Tallinn']['start'] <= 8)
    s.add(city_vars['Tallinn']['end'] >= 8)
    s.add(city_vars['Tallinn']['end'] <= 12)
    s.add(city_vars['Tallinn']['end'] == city_vars['Tallinn']['start'] + 4)  # 5 days

    # Other cities: general constraints
    for city in ['Bucharest', 'Prague', 'Zurich', 'Florence']:
        s.add(city_vars[city]['start'] >= 1)
        s.add(city_vars[city]['end'] <= 26)
        s.add(city_vars[city]['end'] == city_vars[city]['start'] + durations[city] - 1)

    # Ensure no overlapping stays except for flight days
    for city1 in cities:
        for city2 in cities:
            if city1 == city2:
                continue
            s.add(Or(
                city_vars[city1]['end'] < city_vars[city2]['start'],
                city_vars[city2]['end'] < city_vars[city1]['start'],
                And(city_vars[city1]['end'] == city_vars[city2]['start'], city2 in flights[city1]),
                And(city_vars[city2]['end'] == city_vars[city1]['start'], city1 in flights[city2])
            ))

    if s.check() == sat:
        model = s.model()
        itinerary_info = []
        for city in cities:
            start = model[city_vars[city]['start']].as_long()
            end = model[city_vars[city]['end']].as_long()
            itinerary_info.append({'city': city, 'start': start, 'end': end})

        itinerary_info.sort(key=lambda x: x['start'])

        itinerary = []
        for i, info in enumerate(itinerary_info):
            city = info['city']
            start = info['start']
            end = info['end']

            if i > 0:
                prev_info = itinerary_info[i-1]
                prev_end = prev_info['end']
                if prev_end == start:
                    itinerary.append({'day_range': f'Day {start}', 'place': prev_info['city']})
                    itinerary.append({'day_range': f'Day {start}', 'place': city})

            if start == end:
                itinerary.append({'day_range': f'Day {start}', 'place': city})
            else:
                itinerary.append({'day_range': f'Day {start}-{end}', 'place': city})

        output = {'itinerary': itinerary}
        return output
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))