import json
import itertools

def compute_itinerary():
    total_days = 16

    # Required durations for each city
    city_durations = {
        "Frankfurt": 4,
        "Manchester": 4,
        "Valencia": 4,
        "Naples": 4,
        "Oslo": 3,
        "Vilnius": 2
    }
    
    # Direct flight connectivity (bidirectional)
    flight_graph = {
        "Valencia": {"Frankfurt", "Naples"},
        "Frankfurt": {"Valencia", "Manchester", "Naples", "Oslo", "Vilnius"},
        "Manchester": {"Frankfurt", "Naples", "Oslo"},
        "Naples": {"Frankfurt", "Manchester", "Oslo", "Valencia"},
        "Oslo": {"Frankfurt", "Naples", "Vilnius", "Manchester"},
        "Vilnius": {"Frankfurt", "Oslo"}
    }
    
    # The cities to visit
    all_cities = {"Frankfurt", "Manchester", "Valencia", "Naples", "Oslo", "Vilnius"}
    # We fix Frankfurt as the final destination because of the annual show (Day 13-16)
    remaining_cities = list(all_cities - {"Frankfurt"})
    
    valid_schedule = None

    # Try every permutation of the remaining cities; the final ordering always ends with Frankfurt.
    for perm in itertools.permutations(remaining_cities):
        itinerary_order = list(perm) + ["Frankfurt"]
        
        # Compute day ranges following the overlapping rule.
        # Rule: For the first city, start on Day 1.
        # For each consecutive flight from city A to city B on day X,
        # Day X counts as part of both A and B.
        schedule = []
        current_day = 1
        for city in itinerary_order:
            start_day = current_day
            duration = city_durations[city]
            end_day = start_day + duration - 1
            schedule.append((city, start_day, end_day))
            current_day = end_day  # next city's start equals this flight (overlap) day

        # The computed itinerary must end exactly on total_days.
        if schedule[-1][2] != total_days:
            continue

        # Check direct flight connectivity for consecutive cities.
        valid = True
        for i in range(1, len(itinerary_order)):
            prev_city = itinerary_order[i - 1]
            current_city = itinerary_order[i]
            if current_city not in flight_graph.get(prev_city, set()):
                valid = False
                break
        if not valid:
            continue
        
        # Special event constraint: Frankfurt's annual show from Day 13-16 
        # forces its visit to occur from day 13 to 16.
        for city, start, end in schedule:
            if city == "Frankfurt" and start != 13:
                valid = False
                break
        if not valid:
            continue

        # Wedding constraint: The wedding in Vilnius must be attended between Day 12 and Day 13.
        # That is, the Vilnius block must include Day 12 or Day 13.
        for city, start, end in schedule:
            if city == "Vilnius":
                if not (start <= 12 <= end or start <= 13 <= end):
                    valid = False
                break
        if not valid:
            continue

        # If all constraints are met, we have found our valid itinerary.
        valid_schedule = schedule
        break

    if valid_schedule is None:
        return {"error": "No valid itinerary found."}

    # Format the schedule as a list of day-range mappings.
    itinerary_json = {"itinerary": []}
    for city, start, end in valid_schedule:
        itinerary_json["itinerary"].append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })
    return itinerary_json

if __name__ == "__main__":
    itinerary = compute_itinerary()
    print(json.dumps(itinerary))