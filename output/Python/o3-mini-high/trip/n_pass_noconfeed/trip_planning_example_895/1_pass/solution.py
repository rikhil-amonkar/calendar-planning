import itertools
import json

def main():
    total_days = 17
    # Define the required durations for each city
    city_durations = {
        "Brussels": 2,
        "Venice": 3,
        "London": 3,
        "Lisbon": 4,
        "Reykjavik": 3,
        "Santorini": 3,
        "Madrid": 5
    }
    
    # Define direct flight connections as undirected edges (using frozenset)
    flights = {
        frozenset(["Venice", "Madrid"]),
        frozenset(["Lisbon", "Reykjavik"]),
        frozenset(["Brussels", "Venice"]),
        frozenset(["Venice", "Santorini"]),
        frozenset(["Lisbon", "Venice"]),
        frozenset(["Reykjavik", "Madrid"]),
        frozenset(["Brussels", "London"]),
        frozenset(["Madrid", "London"]),
        frozenset(["Santorini", "London"]),
        frozenset(["London", "Reykjavik"]),
        frozenset(["Brussels", "Lisbon"]),
        frozenset(["Lisbon", "London"]),
        frozenset(["Lisbon", "Madrid"]),
        frozenset(["Madrid", "Santorini"]),
        frozenset(["Brussels", "Reykjavik"]),
        frozenset(["Brussels", "Madrid"]),
        frozenset(["Venice", "London"])
    }
    
    # Fixed start: you must attend a conference in Brussels on Day 1 and 2.
    # So Brussels is forced as the starting city.
    remaining_cities = ["Venice", "London", "Lisbon", "Reykjavik", "Santorini", "Madrid"]
    
    valid_itinerary = None
    
    # Iterate over all permutations of the remaining cities
    for perm in itertools.permutations(remaining_cities):
        itinerary_order = ["Brussels"] + list(perm)
        
        # Check that every consecutive pair of cities is connected by a direct flight.
        valid_flights = True
        for i in range(len(itinerary_order) - 1):
            if frozenset([itinerary_order[i], itinerary_order[i+1]]) not in flights:
                valid_flights = False
                break
        if not valid_flights:
            continue
        
        # Compute the itinerary timeline.
        # Rule: The first city starts on Day 1.
        # When flying from city A to city B on day X, that day X counts as being in both A and B.
        # Thus, the start day of a city (after the first) equals the previous city’s end day.
        schedule = []
        current_day = 1
        for city in itinerary_order:
            duration = city_durations[city]
            start_day = current_day
            end_day = current_day + duration - 1
            schedule.append((city, start_day, end_day))
            current_day = end_day  # Next city shares the flight day
        
        # Check that the finished itinerary ends exactly on total_days.
        if schedule[-1][2] != total_days:
            continue
        
        # Apply the special scheduling constraints.
        # Constraint for Venice: 3 days in Venice,
        # with at least one day between Day 5 and Day 7 (relative visit).
        venice_ok = True
        for (city, start, end) in schedule:
            if city == "Venice":
                if end < 5 or start > 7:
                    venice_ok = False
                break
        if not venice_ok:
            continue
        
        # Constraint for Madrid: 5 days in Madrid,
        # with the wedding between Day 7 and Day 11.
        madrid_ok = True
        for (city, start, end) in schedule:
            if city == "Madrid":
                if end < 7 or start > 11:
                    madrid_ok = False
                break
        if not madrid_ok:
            continue
        
        # If all constraints are met, we have found a valid itinerary.
        valid_itinerary = schedule
        break

    # Build the JSON output with the itinerary:
    # Each entry includes a day_range (e.g., "Day 1-2") and the place.
    output = {"itinerary": []}
    if valid_itinerary:
        for city, start, end in valid_itinerary:
            output["itinerary"].append({"day_range": f"Day {start}-{end}", "place": city})
    
    print(json.dumps(output))

if __name__ == "__main__":
    main()