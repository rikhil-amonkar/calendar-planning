import itertools
import json

def main():
    # Input trip constraints
    total_days = 20
    # Required days per city (note: these include the flight overlap days)
    city_durations = {
        "Nice": 5,       # Must be visited from day 1 to day 5 (relatives)
        "Krakow": 6,     # 6 days in Krakow
        "Dublin": 7,     # 7 days in Dublin
        "Lyon": 4,       # 4 days in Lyon
        "Frankfurt": 2   # 2 days in Frankfurt (meeting friends between day 19 and day 20)
    }
    
    # List of direct flight connections (undirected)
    flight_edges = [
        ("Nice", "Dublin"),
        ("Dublin", "Frankfurt"),
        ("Dublin", "Krakow"),
        ("Krakow", "Frankfurt"),
        ("Lyon", "Frankfurt"),
        ("Nice", "Frankfurt"),
        ("Lyon", "Dublin"),
        ("Nice", "Lyon")
    ]
    
    # Build bidirectional flight graph
    graph = {city: set() for city in city_durations.keys()}
    for c1, c2 in flight_edges:
        graph[c1].add(c2)
        graph[c2].add(c1)
    
    # We fix the start and end due to the specific constraints:
    # - Visit relatives in Nice between Day 1 and 5 => Nice must be at the start.
    # - Meet friends in Frankfurt between Day 19 and 20 => Frankfurt must be last.
    start_city = "Nice"
    end_city = "Frankfurt"
    middle_cities = [city for city in city_durations if city not in [start_city, end_city]]
    
    # Generate all valid orderings that use direct flights between consecutive cities.
    valid_orderings = []
    for perm in itertools.permutations(middle_cities):
        itinerary_order = [start_city] + list(perm) + [end_city]
        valid = True
        for i in range(len(itinerary_order) - 1):
            current = itinerary_order[i]
            next_city = itinerary_order[i+1]
            if next_city not in graph[current]:
                valid = False
                break
        if valid:
            valid_orderings.append(itinerary_order)
    
    # Function to compute the itinerary schedule in day ranges.
    def compute_schedule(order):
        itinerary_schedule = []
        current_day = 1
        for city in order:
            duration = city_durations[city]
            # The traveler spends 'duration' days at the city.
            # NOTE: Flight days are overlap days. So if you fly on a day,
            # that day counts for both the city you left and the city you arrive in.
            start = current_day
            end = start + duration - 1
            itinerary_schedule.append({"day_range": f"Day {start}-{end}", "place": city})
            # The next city starts on the same day as the end day of this city.
            current_day = end
        return itinerary_schedule, current_day - 1  # last day computed
    
    # Select an ordering that also meets the total_days constraint.
    optimal_schedule = None
    for order in valid_orderings:
        schedule, last_day = compute_schedule(order)
        if last_day == total_days:
            # Additional constraints: 
            #   - "Nice" must be visited on Day 1-5.
            #   - "Frankfurt" must include days 19-20.
            if schedule[0]["day_range"] == "Day 1-5" and schedule[-1]["day_range"] == "Day 19-20":
                optimal_schedule = schedule
                break

    # If no ordering was found (should not happen with the given constraints), return an error itinerary.
    if optimal_schedule is None:
        output = {"itinerary": [{"error": "No valid itinerary found."}]}
    else:
        output = {"itinerary": optimal_schedule}

    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()