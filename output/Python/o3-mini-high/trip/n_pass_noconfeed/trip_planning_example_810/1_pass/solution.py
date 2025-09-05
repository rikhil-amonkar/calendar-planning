import itertools
import json

def compute_schedule(order, durations):
    schedule = []
    current_day = 1
    for i, city in enumerate(order):
        start = current_day
        end = start + durations[city] - 1
        schedule.append((city, start, end))
        # If not the last city, take a flight on the ending day (overlap)
        if i < len(order) - 1:
            current_day = end
    return schedule

def schedule_total_days(schedule):
    # The total unique days equal the end day of the last city
    return schedule[-1][2]

def check_events(schedule):
    # Build a mapping from city to its (start, end) days
    city_days = {city: (start, end) for city, start, end in schedule}
    
    # Berlin: conference on Day 1 and Day 3
    if "Berlin" not in city_days:
        return False
    b_start, b_end = city_days["Berlin"]
    if not (b_start <= 1 <= b_end and b_start <= 3 <= b_end):
        return False

    # Barcelona: workshop between Day 3 and Day 4
    if "Barcelona" not in city_days:
        return False
    ba_start, ba_end = city_days["Barcelona"]
    # Must cover either day 3 or day 4 (or both)
    if not ((ba_start <= 3 <= ba_end) or (ba_start <= 4 <= ba_end)):
        return False

    # Lyon: wedding between Day 4 and Day 5
    if "Lyon" not in city_days:
        return False
    ly_start, ly_end = city_days["Lyon"]
    if not ((ly_start <= 4 <= ly_end) or (ly_start <= 5 <= ly_end)):
        return False

    return True

def flights_connected(order, flights):
    # Check that for each consecutive city pair, a direct flight exists
    for i in range(len(order) - 1):
        a = order[i]
        b = order[i+1]
        if b not in flights[a]:
            return False
    return True

def find_valid_itineraries(cities, durations, flights, total_days_required=20):
    valid_itins = []
    # Force Berlin as the first city because of the conference day1 requirement.
    start_city = "Berlin"
    remaining_cities = [city for city in cities if city != start_city]
    # Generate all permutations of the other 6 cities.
    for perm in itertools.permutations(remaining_cities):
        order = [start_city] + list(perm)
        # Check that every leg has a direct flight.
        if not flights_connected(order, flights):
            continue
        # Compute the schedule given the ordering and durations.
        schedule = compute_schedule(order, durations)
        # The overall unique days available is schedule_total_days(schedule)
        if schedule_total_days(schedule) != total_days_required:
            continue
        # Check that the specific event days fall within the proper city intervals.
        if not check_events(schedule):
            continue
        valid_itins.append((order, schedule))
    return valid_itins

def main():
    # Define the cities and their required durations.
    cities = ["Berlin", "Nice", "Athens", "Stockholm", "Barcelona", "Vilnius", "Lyon"]
    durations = {
        "Berlin": 3,
        "Nice": 5,
        "Athens": 5,
        "Stockholm": 5,
        "Barcelona": 2,
        "Vilnius": 4,
        "Lyon": 2
    }
    
    # Define the direct flights (bidirectional) as given.
    flights = {
        "Lyon": ["Nice", "Barcelona"],
        "Nice": ["Lyon", "Athens", "Berlin", "Stockholm", "Barcelona"],
        "Athens": ["Nice", "Berlin", "Vilnius", "Stockholm", "Barcelona"],
        "Berlin": ["Athens", "Nice", "Barcelona", "Vilnius", "Stockholm"],
        "Barcelona": ["Berlin", "Nice", "Athens", "Stockholm", "Lyon"],
        "Stockholm": ["Athens", "Berlin", "Nice", "Barcelona"],
        "Vilnius": ["Berlin", "Athens"]
    }
    
    # Find all itineraries that satisfy the flight connections, total days, and event constraints.
    valid_itineraries = find_valid_itineraries(cities, durations, flights, total_days_required=20)
    
    # For this example, we select the first valid itinerary found.
    if valid_itineraries:
        best_order, best_schedule = valid_itineraries[0]
        # Build the JSON output structure.
        itinerary_output = {"itinerary": []}
        for city, start, end in best_schedule:
            itinerary_output["itinerary"].append({
                "day_range": f"Day {start}-{end}",
                "place": city
            })
        print(json.dumps(itinerary_output))
    else:
        # If no valid itinerary is found, output an empty itinerary.
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()