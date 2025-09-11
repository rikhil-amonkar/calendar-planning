import itertools
import json

def main():
    cities = ['Amsterdam', 'Edinburgh', 'Brussels', 'Vienna', 'Berlin', 'Reykjavik']
    durations = {
        'Amsterdam': 4,
        'Edinburgh': 5,
        'Brussels': 5,
        'Vienna': 5,
        'Berlin': 4,
        'Reykjavik': 5
    }

    flight_graph = {
        'Amsterdam': {'Berlin', 'Edinburgh', 'Reykjavik', 'Vienna'},
        'Edinburgh': {'Berlin', 'Amsterdam', 'Brussels'},
        'Brussels': {'Edinburgh', 'Berlin', 'Vienna', 'Reykjavik'},
        'Vienna': {'Berlin', 'Brussels', 'Reykjavik', 'Amsterdam'},
        'Berlin': {'Amsterdam', 'Edinburgh', 'Vienna', 'Brussels', 'Reykjavik'},
        'Reykjavik': {'Amsterdam', 'Vienna', 'Brussels', 'Berlin'},
    }

    def is_valid_permutation(perm):
        for i in range(len(perm) - 1):
            current = perm[i]
            next_city = perm[i+1]
            if next_city not in flight_graph[current]:
                return False
        return True

    def compute_days(perm):
        start_days = {}
        end_days = {}
        current_start = 1
        for city in perm:
            duration = durations[city]
            end_day = current_start + duration - 1
            start_days[city] = current_start
            end_days[city] = end_day
            current_start = end_day  # next city starts at this day
        return start_days, end_days

    def check_constraints(start_days, end_days):
        # Check Amsterdam's stay overlaps with 5-8
        a_start = start_days.get('Amsterdam', 0)
        a_end = end_days.get('Amsterdam', 0)
        a_overlap = not (a_end < 5 or a_start > 8)
        # Check Berlin's stay overlaps with 16-19
        b_start = start_days.get('Berlin', 0)
        b_end = end_days.get('Berlin', 0)
        b_overlap = not (b_end < 16 or b_start > 19)
        # Check Reykjavik's stay overlaps with 12-16
        r_start = start_days.get('Reykjavik', 0)
        r_end = end_days.get('Reykjavik', 0)
        r_overlap = not (r_end < 12 or r_start > 16)
        return a_overlap and b_overlap and r_overlap

    for perm in itertools.permutations(cities):
        if not is_valid_permutation(perm):
            continue
        start_days, end_days = compute_days(perm)
        if check_constraints(start_days, end_days):
            # Build itinerary
            itinerary = []
            current_day = 1
            for city in perm:
                duration = durations[city]
                end_day = current_day + duration - 1
                day_range = f"Day {current_day}-{end_day}"
                itinerary.append({"day_range": day_range, "place": city})
                current_day = end_day  # next city starts at this day
            print(json.dumps({"itinerary": itinerary}))
            return

if __name__ == "__main__":
    main()