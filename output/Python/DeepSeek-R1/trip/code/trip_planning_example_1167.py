import json

def main():
    flights = {
        'Mykonos': ['Naples'],
        'Naples': ['Mykonos', 'Dublin', 'Istanbul', 'Venice', 'Brussels', 'Frankfurt'],
        'Venice': ['Istanbul', 'Naples', 'Brussels', 'Dublin', 'Frankfurt'],
        'Istanbul': ['Venice', 'Naples', 'Frankfurt', 'Krakow', 'Brussels', 'Dublin'],
        'Dublin': ['Brussels', 'Naples', 'Krakow', 'Istanbul', 'Venice', 'Frankfurt'],
        'Frankfurt': ['Krakow', 'Istanbul', 'Venice', 'Naples', 'Brussels', 'Dublin'],
        'Krakow': ['Frankfurt', 'Brussels', 'Dublin', 'Istanbul'],
        'Brussels': ['Dublin', 'Krakow', 'Naples', 'Venice', 'Istanbul', 'Frankfurt']
    }

    itinerary = [
        {'place': 'Mykonos', 'start': 1, 'end': 4},
        {'place': 'Naples', 'start': 4, 'end': 7},
        {'place': 'Venice', 'start': 7, 'end': 9},
        {'place': 'Istanbul', 'start': 9, 'end': 11},
        {'place': 'Dublin', 'start': 11, 'end': 15},
        {'place': 'Frankfurt', 'start': 15, 'end': 17},
        {'place': 'Krakow', 'start': 17, 'end': 20},
        {'place': 'Brussels', 'start': 20, 'end': 21}
    ]

    for i in range(len(itinerary) - 1):
        current = itinerary[i]['place']
        next_place = itinerary[i+1]['place']
        if next_place not in flights[current]:
            print(json.dumps({"itinerary": []}))
            return

    total_days = sum(seg['end'] - seg['start'] + 1 for seg in itinerary)
    if total_days != 21:
        print(json.dumps({"itinerary": []}))
        return

    required_days = {
        'Dublin': 5, 'Krakow': 4, 'Istanbul': 3, 'Venice': 3,
        'Naples': 4, 'Brussels': 2, 'Mykonos': 4, 'Frankfurt': 3
    }
    actual_days = {}
    for seg in itinerary:
        city = seg['place']
        actual_days[city] = actual_days.get(city, 0) + seg['end'] - seg['start'] + 1
    if any(actual_days.get(c,0) != required_days[c] for c in required_days):
        print(json.dumps({"itinerary": []}))
        return

    constraints = [
        {'city': 'Dublin', 'start': 11, 'end': 15},
        {'city': 'Frankfurt', 'start': 15, 'end': 17},
        {'city': 'Istanbul', 'start': 9, 'end': 11},
        {'city': 'Mykonos', 'start': 1, 'end': 4}
    ]
    for c in constraints:
        valid = False
        for seg in itinerary:
            if seg['place'] == c['city'] and seg['start'] <= c['start'] and seg['end'] >= c['end']:
                valid = True
                break
        if not valid:
            print(json.dumps({"itinerary": []}))
            return

    output = {"itinerary": []}
    for seg in itinerary:
        s, e = seg['start'], seg['end']
        day_range = f"Day {s}" if s == e else f"Day {s}-{e}"
        output['itinerary'].append({"day_range": day_range, "place": seg['place']})
    print(json.dumps(output))

if __name__ == "__main__":
    main()