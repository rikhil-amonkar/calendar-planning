import itertools
import json

def main():
    cities = ['Manchester', 'Stuttgart', 'Madrid', 'Vienna']
    durations = {
        'Manchester': 7,
        'Stuttgart': 5,
        'Madrid': 4,
        'Vienna': 2
    }
    allowed_flights = {
        ('Vienna', 'Stuttgart'),
        ('Stuttgart', 'Vienna'),
        ('Manchester', 'Vienna'),
        ('Vienna', 'Manchester'),
        ('Madrid', 'Vienna'),
        ('Vienna', 'Madrid'),
        ('Manchester', 'Stuttgart'),
        ('Stuttgart', 'Manchester'),
        ('Manchester', 'Madrid'),
        ('Madrid', 'Manchester'),
    }

    for perm in itertools.permutations(cities):
        valid_transitions = True
        for i in range(len(perm) - 1):
            if (perm[i], perm[i+1]) not in allowed_flights:
                valid_transitions = False
                break
        if not valid_transitions:
            continue

        start_days = [1]
        for i in range(1, len(perm)):
            prev_duration = durations[perm[i-1]]
            current_start = start_days[i-1] + prev_duration - 1
            start_days.append(current_start)

        man_index = perm.index('Manchester')
        man_start = start_days[man_index]
        if man_start > 7:
            continue

        stutt_index = perm.index('Stuttgart')
        stutt_start = start_days[stutt_index]
        if not (7 <= stutt_start <= 11):
            continue

        itinerary = []
        for i in range(len(perm)):
            city = perm[i]
            start = start_days[i]
            end = start + durations[city] - 1
            day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": city})

        print(json.dumps({"itinerary": itinerary}))
        return

if __name__ == "__main__":
    main()