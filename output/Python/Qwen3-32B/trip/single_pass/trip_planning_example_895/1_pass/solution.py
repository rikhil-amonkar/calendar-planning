import itertools
import json

def main():
    city_days = {
        'Brussels': 2,
        'Lisbon': 4,
        'Venice': 3,
        'Madrid': 5,
        'Santorini': 3,
        'London': 3,
        'Reykjavik': 3
    }

    cities = ['Brussels', 'Lisbon', 'Venice', 'Madrid', 'Santorini', 'London', 'Reykjavik']
    remaining_cities = ['Lisbon', 'Venice', 'Madrid', 'Santorini', 'London', 'Reykjavik']

    flights = {
        'Brussels': ['Venice', 'London', 'Lisbon', 'Reykjavik', 'Madrid'],
        'Venice': ['Madrid', 'Santorini', 'Lisbon', 'London', 'Brussels'],
        'Lisbon': ['Venice', 'Reykjavik', 'Brussels', 'London', 'Madrid'],
        'London': ['Venice', 'Madrid', 'Santorini', 'Reykjavik', 'Brussels', 'Lisbon'],
        'Reykjavik': ['Lisbon', 'Madrid', 'London', 'Brussels'],
        'Santorini': ['Venice', 'London', 'Madrid'],
        'Madrid': ['Venice', 'Lisbon', 'Santorini', 'London', 'Reykjavik', 'Brussels']
    }

    for perm in itertools.permutations(remaining_cities):
        path = ['Brussels'] + list(perm)
        # Check flight connections
        valid_path = True
        for i in range(len(path) - 1):
            current = path[i]
            next_city = path[i+1]
            if next_city not in flights[current]:
                valid_path = False
                break
        if not valid_path:
            continue

        # Calculate day ranges
        current_day = 1
        itinerary_data = []
        for city in path:
            start_day = current_day
            end_day = start_day + city_days[city] - 1
            itinerary_data.append((city, (start_day, end_day)))
            current_day = end_day

        # Check Brussels constraint
        brussels_start, brussels_end = itinerary_data[0][1]
        if (brussels_start, brussels_end) != (1, 2):
            continue

        # Check Venice constraint
        venice_start = venice_end = None
        for city, (start, end) in itinerary_data:
            if city == 'Venice':
                venice_start, venice_end = start, end
        if venice_start is None or not (venice_start <= 7 and venice_end >= 5):
            continue

        # Check Madrid constraint
        madrid_start = madrid_end = None
        for city, (start, end) in itinerary_data:
            if city == 'Madrid':
                madrid_start, madrid_end = start, end
        if madrid_start is None or not (madrid_start <= 11 and madrid_end >= 7):
            continue

        # If all constraints are met, construct the JSON
        itinerary = []
        for city, (start, end) in itinerary_data:
            day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": city})
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
        return

if __name__ == "__main__":
    main()