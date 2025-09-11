import itertools
import json

def main():
    cities = ['Prague', 'Frankfurt', 'Lyon', 'Helsinki', 'Naples']
    required_days = {
        'Prague': 2,
        'Frankfurt': 3,
        'Lyon': 3,
        'Helsinki': 4,
        'Naples': 4
    }
    direct_flight_pairs = {
        frozenset({'Prague', 'Lyon'}),
        frozenset({'Prague', 'Frankfurt'}),
        frozenset({'Frankfurt', 'Lyon'}),
        frozenset({'Helsinki', 'Naples'}),
        frozenset({'Helsinki', 'Frankfurt'}),
        frozenset({'Naples', 'Frankfurt'}),
        frozenset({'Prague', 'Helsinki'}),
    }

    for perm in itertools.permutations(cities):
        if perm[0] != 'Prague':
            continue
        valid_sequence = True
        for i in range(len(perm) - 1):
            city_a, city_b = perm[i], perm[i+1]
            if frozenset({city_a, city_b}) not in direct_flight_pairs:
                valid_sequence = False
                break
        if not valid_sequence:
            continue
        current_day = 1
        itinerary_segments = []
        for city in perm:
            duration = required_days[city]
            end_day = current_day + duration - 1
            itinerary_segments.append( (current_day, end_day, city) )
            current_day = end_day
        # Check Helsinki's segment
        helsinki_found = False
        for seg in itinerary_segments:
            if seg[2] == 'Helsinki':
                helsinki_start, helsinki_end, _ = seg
                if helsinki_start <= 2 and helsinki_end >= 5:
                    helsinki_found = True
                    break
        if helsinki_found:
            json_itinerary = []
            for start, end, city in itinerary_segments:
                day_range = f"Day {start}-{end}"
                json_itinerary.append({"day_range": day_range, "place": city})
            result = {"itinerary": json_itinerary}
            print(json.dumps(result, indent=2))
            return

if __name__ == "__main__":
    main()