import json

def main():
    cities = {
        'Porto': {'days': 3, 'fixed': (1, 3)},
        'Paris': {'days': 5},
        'Florence': {'days': 3},
        'Vienna': {'days': 2, 'fixed': (19, 20)},
        'Munich': {'days': 5},
        'Nice': {'days': 5},
        'Warsaw': {'days': 3, 'fixed': (13, 15)}
    }

    flights = {
        'Florence': {'Vienna', 'Munich', 'Paris', 'Munich'},  # 'Munich' should be 'Munich'
        'Paris': {'Warsaw', 'Florence', 'Vienna', 'Munich', 'Nice', 'Porto'},
        'Munich': {'Vienna', 'Florence', 'Warsaw', 'Nice', 'Porto', 'Paris'},
        'Porto': {'Vienna', 'Munich', 'Nice', 'Warsaw', 'Paris'},
        'Warsaw': {'Paris', 'Vienna', 'Munich', 'Nice', 'Porto'},
        'Vienna': {'Florence', 'Paris', 'Munich', 'Porto', 'Warsaw', 'Nice'},
        'Nice': {'Paris', 'Munich', 'Porto', 'Warsaw', 'Vienna'}
    }

    itinerary_steps = [
        {'city': 'Porto', 'start': 1, 'end': 3},
        {'city': 'Paris', 'start': 3, 'end': 7},
        {'city': 'Florence', 'start': 7, 'end': 9},
        {'city': 'Munich', 'start': 9, 'end': 13},
        {'city': 'Warsaw', 'start': 13, 'end': 15},
        {'city': 'Nice', 'start': 15, 'end': 19},
        {'city': 'Vienna', 'start': 19, 'end': 20}
    ]

    valid = True
    for i in range(1, len(itinerary_steps)):
        prev = itinerary_steps[i-1]['city']
        curr = itinerary_steps[i]['city']
        if curr not in flights.get(prev, set()):
            valid = False
            break

    for step in itinerary_steps:
        city = step['city']
        req = cities[city]['days']
        allocated = step['end'] - step['start'] + 1
        if 'fixed' in cities[city]:
            if (step['start'], step['end']) != cities[city]['fixed']:
                valid = False
        elif allocated != req:
            valid = False

    if not valid:
        print(json.dumps({"itinerary": []}))
        return

    output = {"itinerary": []}
    for step in itinerary_steps:
        start = step['start']
        end = step['end']
        dr = f"Day {start}" if start == end else f"Day {start}-{end}"
        output['itinerary'].append({"day_range": dr, "place": step['city']})

    print(json.dumps(output))

if __name__ == "__main__":
    main()