import itertools
import json

def main():
    # Define cities and their required durations
    cities = ['Reykjavik', 'Istanbul', 'Edinburgh', 'Oslo', 'Stuttgart', 'Bucharest']
    durations = {
        'Reykjavik': 5,
        'Istanbul': 4,
        'Edinburgh': 5,
        'Oslo': 2,
        'Stuttgart': 3,
        'Bucharest': 5
    }

    # Define direct flight connections
    flights = {
        'Reykjavik': ['Stuttgart', 'Bucharest', 'Istanbul'],
        'Stuttgart': ['Reykjavik', 'Edinburgh', 'Istanbul'],
        'Edinburgh': ['Stuttgart', 'Istanbul', 'Oslo'],
        'Istanbul': ['Reykjavik', 'Stuttgart', 'Edinburgh', 'Oslo', 'Bucharest'],
        'Oslo': ['Istanbul', 'Bucharest', 'Reykjavik', 'Edinburgh'],
        'Bucharest': ['Reykjavik', 'Istanbul', 'Oslo']
    }

    # Generate all permutations of the cities
    for perm in itertools.permutations(cities):
        valid = True
        # Check if each consecutive pair has a direct flight
        for i in range(len(perm) - 1):
            current = perm[i]
            next_city = perm[i + 1]
            if next_city not in flights[current]:
                valid = False
                break
        if not valid:
            continue

        # Compute start and end days for each city
        start_days = {}
        end_days = {}
        current_day = 1
        for city in perm:
            start_days[city] = current_day
            end_days[city] = current_day + durations[city] - 1
            current_day += durations[city] - 1  # Overlap one day

        # Check if total days is 19
        if current_day != 19:
            continue

        # Check constraints for Istanbul and Oslo
        if start_days['Istanbul'] == 5 and start_days['Oslo'] == 8:
            # Build the itinerary
            itinerary = []
            for i in range(len(perm)):
                city = perm[i]
                start = start_days[city]
                end = end_days[city]
                day_range = f"Day {start}-{end}"
                itinerary.append({"day_range": day_range, "place": city})
            print(json.dumps({"itinerary": itinerary}))
            return

    # If no valid itinerary found
    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()