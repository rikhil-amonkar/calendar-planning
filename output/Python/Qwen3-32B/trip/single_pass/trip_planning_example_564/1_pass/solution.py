import itertools
import json

def main():
    cities = ['Seville', 'Rome', 'Istanbul', 'Naples', 'Santorini']
    required_days = {
        'Seville': 4,
        'Rome': 3,
        'Istanbul': 2,
        'Naples': 7,
        'Santorini': 4
    }
    direct_flights = {
        ('Rome', 'Santorini'),
        ('Santorini', 'Rome'),
        ('Seville', 'Rome'),
        ('Rome', 'Seville'),
        ('Istanbul', 'Naples'),
        ('Naples', 'Istanbul'),
        ('Naples', 'Santorini'),
        ('Santorini', 'Naples'),
        ('Rome', 'Naples'),
        ('Naples', 'Rome'),
        ('Rome', 'Istanbul'),
        ('Istanbul', 'Rome'),
    }

    for perm in itertools.permutations(cities):
        valid_transitions = True
        for i in range(1, len(perm)):
            if (perm[i-1], perm[i]) not in direct_flights:
                valid_transitions = False
                break
        if not valid_transitions:
            continue

        current_start = 1
        valid_istanbul = False
        valid_santorini = False
        end_day = 0
        for city in perm:
            days = required_days[city]
            end = current_start + days - 1
            if city == 'Istanbul':
                if current_start == 6 and end == 7:
                    valid_istanbul = True
                else:
                    valid_istanbul = False
                    break
            if city == 'Santorini':
                if current_start == 13 and end == 16:
                    valid_santorini = True
                else:
                    valid_santorini = False
                    break
            current_start = end
            end_day = end

        if valid_istanbul and valid_santorini and end_day == 16:
            itinerary = []
            current_start = 1
            for city in perm:
                days = required_days[city]
                end = current_start + days - 1
                day_range = f"Day {current_start}-{end}"
                itinerary.append({"day_range": day_range, "place": city})
                current_start = end
            print(json.dumps({"itinerary": itinerary}))
            return

if __name__ == "__main__":
    main()