import itertools
import json

def main():
    cities = ['Split', 'Helsinki', 'Reykjavik', 'Vilnius', 'Geneva']
    required_days = {
        'Split': 2,
        'Helsinki': 2,
        'Reykjavik': 3,
        'Vilnius': 3,
        'Geneva': 6
    }
    adjacency = {
        'Split': {'Helsinki', 'Geneva', 'Vilnius'},
        'Helsinki': {'Split', 'Geneva', 'Reykjavik', 'Vilnius'},
        'Reykjavik': {'Helsinki'},
        'Vilnius': {'Helsinki', 'Split'},
        'Geneva': {'Split', 'Helsinki'}
    }

    for perm in itertools.permutations(cities):
        valid = True
        for i in range(len(perm) - 1):
            current = perm[i]
            next_city = perm[i+1]
            if next_city not in adjacency[current]:
                valid = False
                break
        if not valid:
            continue

        itinerary = []
        start_day = 1
        vilnius_end = None
        reyk_start = None
        for city in perm:
            days = required_days[city]
            end_day = start_day + days - 1
            itinerary.append((start_day, end_day, city))
            if city == 'Vilnius':
                vilnius_end = end_day
            if city == 'Reykjavik':
                reyk_start = start_day
            start_day = end_day

        if vilnius_end == 9 and reyk_start == 10:
            output_itinerary = []
            for start, end, city in itinerary:
                output_itinerary.append({
                    "day_range": f"Day {start}-{end}",
                    "place": city
                })
            print(json.dumps({"itinerary": output_itinerary}))
            return

    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()