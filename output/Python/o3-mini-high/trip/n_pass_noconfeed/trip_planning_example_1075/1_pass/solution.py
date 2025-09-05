import itertools
import json

def main():
    # Trip constraints
    total_days = 25
    # Required number of days in each city (pre-flight overlap counted)
    durations = {
        "Vienna": 4,
        "Lyon": 3,
        "Edinburgh": 4,
        "Reykjavik": 5,
        "Stuttgart": 5,
        "Manchester": 2,
        "Split": 5,
        "Prague": 4
    }
    
    # Direct flights (treat as bidirectional)
    flights = {
        frozenset({"Reykjavik", "Stuttgart"}),
        frozenset({"Stuttgart", "Split"}),
        frozenset({"Stuttgart", "Vienna"}),
        frozenset({"Prague", "Manchester"}),
        frozenset({"Edinburgh", "Prague"}),
        frozenset({"Manchester", "Split"}),
        frozenset({"Prague", "Vienna"}),
        frozenset({"Vienna", "Manchester"}),
        frozenset({"Prague", "Split"}),
        frozenset({"Vienna", "Lyon"}),
        frozenset({"Stuttgart", "Edinburgh"}),
        frozenset({"Split", "Lyon"}),
        frozenset({"Stuttgart", "Manchester"}),
        frozenset({"Prague", "Lyon"}),
        frozenset({"Reykjavik", "Vienna"}),
        frozenset({"Prague", "Reykjavik"}),
        frozenset({"Vienna", "Split"})
    }
    
    # List of all cities
    cities = list(durations.keys())
    
    valid_itinerary = None
    
    # In our scheduling algorithm, if the itinerary order is:
    # City1: days 1 to R(city1)
    # City2: days = previous_end (overlap) to previous_end + (R(city2)-1)
    # ...
    # Total days = sum(durations) - (number_of_cities - 1) = 32 - 7 = 25, as required.
    #
    # Additional constraints:
    # - Edinburgh must be visited with day range exactly Day 5-8.
    #   (Thus, Edinburgh cannot be the first city and must start on day 5.)
    # - Split must be visited such that its block overlaps the wedding window (day 19 to 23).
    #   For a 5-day stay, if its start day S satisfies S >= 15 and S <= 23 then the block S...S+4 contains at least one day in [19,23].
    
    for perm in itertools.permutations(cities):
        # Skip if Edinburgh is the first city, as its days would be Day 1-4.
        if perm[0] == "Edinburgh":
            continue

        itinerary_steps = []  # Each element: (city, start_day, end_day)
        current_day = 1
        valid = True
        
        # Compute day assignments following the rule:
        # First city: start = 1, end = start + duration - 1.
        # Each subsequent city: start = previous end (flight day overlap), end = start + duration - 1.
        for city in perm:
            start = current_day
            end = start + durations[city] - 1
            itinerary_steps.append((city, start, end))
            current_day = end  # next city starts on the same day as previous city's end
        
        # Check connectivity using direct flights for each consecutive pair.
        for i in range(len(itinerary_steps) - 1):
            city_a = itinerary_steps[i][0]
            city_b = itinerary_steps[i + 1][0]
            if frozenset({city_a, city_b}) not in flights:
                valid = False
                break
        if not valid:
            continue
        
        # Check Edinburgh constraint: its day block must be exactly Day 5-8.
        for city, start, end in itinerary_steps:
            if city == "Edinburgh":
                if start != 5 or end != 8:
                    valid = False
                break
        if not valid:
            continue
        
        # Check Split wedding constraint:
        # For a 5-day stay in Split, block = [S, S+1, S+2, S+3, S+4].
        # We require that the block overlaps with days 19 to 23.
        # That is, we need S <= 23 and (S+4) >= 19, equivalently S >= 15 and S <= 23.
        for city, start, end in itinerary_steps:
            if city == "Split":
                if start < 15 or start > 23:
                    valid = False
                break
        if not valid:
            continue
        
        # Check total itinerary days matches required total (last city's end should be total_days).
        if itinerary_steps[-1][2] != total_days:
            valid = False
        if not valid:
            continue
        
        valid_itinerary = itinerary_steps
        break  # Found a valid itinerary, so stop searching
    
    # Format the itinerary for JSON output.
    if valid_itinerary is None:
        result = {"itinerary": []}
    else:
        itinerary_output = []
        for city, start, end in valid_itinerary:
            day_range = f"Day {start}-{end}"
            itinerary_output.append({"day_range": day_range, "place": city})
        result = {"itinerary": itinerary_output}
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()