import json
import itertools

def main():
    # Total itinerary days and specific constraints
    total_days = 16
    conference_days = [14, 16]  # Must be in Nice
    friend_meeting_window = (10, 14)  # In Oslo
    
    # Required durations for each city
    city_durations = {
        "Mykonos": 4,
        "Nice": 3,
        "London": 2,
        "Copenhagen": 3,
        "Oslo": 5,
        "Tallinn": 4
    }
    
    # All cities list
    cities = list(city_durations.keys())
    
    # Define direct flight links (bidirectional)
    flights = [
        ("London", "Copenhagen"),
        ("Copenhagen", "Tallinn"),
        ("Tallinn", "Oslo"),
        ("Mykonos", "London"),
        ("Oslo", "Nice"),
        ("London", "Nice"),
        ("Mykonos", "Nice"),
        ("London", "Oslo"),
        ("Copenhagen", "Nice"),
        ("Copenhagen", "Oslo")
    ]
    
    # Build flight graph as a dictionary of sets.
    flight_graph = {city: set() for city in cities}
    for a, b in flights:
        flight_graph[a].add(b)
        flight_graph[b].add(a)
    
    # For conference constraints in Nice, we fix Nice as the final destination.
    remaining_cities = [city for city in cities if city != "Nice"]
    
    valid_itinerary = None
    # Try every permutation of the remaining five cities and append Nice at the end.
    for perm in itertools.permutations(remaining_cities):
        itinerary_order = list(perm) + ["Nice"]
        
        # Check that every consecutive flight is possible
        valid_route = True
        for i in range(len(itinerary_order) - 1):
            if itinerary_order[i+1] not in flight_graph[itinerary_order[i]]:
                valid_route = False
                break
        if not valid_route:
            continue
        
        # Compute day intervals for each city segment.
        # Rule: For the first city, you spend its full duration starting on Day 1.
        # For subsequent cities, you fly on the same day your stay in the previous city ends.
        segments = []  # Each segment: (city, start_day, end_day)
        current_day = 1
        for i, city in enumerate(itinerary_order):
            duration = city_durations[city]
            if i == 0:
                start_day = current_day
                end_day = start_day + duration - 1
            else:
                # Flight day: the current_day equals the previous city's end day.
                start_day = current_day
                end_day = start_day + duration - 1
            segments.append((city, start_day, end_day))
            current_day = end_day  # Next segment starts on the same day as end_day
        
        # Check that the overall itinerary fits the 16-day schedule.
        if segments[-1][2] != total_days:
            continue
        
        # Ensure Nice (always last) covers the conference days (Day 14 and Day 16).
        nice_city, nice_start, nice_end = segments[-1]
        if not (nice_start <= conference_days[0] <= nice_end and nice_start <= conference_days[1] <= nice_end):
            continue
        
        # Find the Oslo segment and check that it overlaps with the friend meeting window.
        oslo_ok = False
        for city, start_day, end_day in segments:
            if city == "Oslo":
                # Check for overlap with the friend meeting window.
                if not (end_day < friend_meeting_window[0] or start_day > friend_meeting_window[1]):
                    oslo_ok = True
                break
        if not oslo_ok:
            continue
        
        valid_itinerary = segments
        break
    
    if valid_itinerary is None:
        output = {"itinerary": []}
    else:
        # Build the JSON output list with day ranges.
        itinerary_list = []
        for city, start_day, end_day in valid_itinerary:
            day_range = f"Day {start_day}-{end_day}"
            itinerary_list.append({"day_range": day_range, "place": city})
        output = {"itinerary": itinerary_list}
    
    print(json.dumps(output))

if __name__ == "__main__":
    main()