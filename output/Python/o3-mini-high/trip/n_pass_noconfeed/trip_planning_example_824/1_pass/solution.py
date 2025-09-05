import json

# Define city parameters: required stay duration and any fixed start day constraints.
# If a city has a fixed start day constraint, its allocated period must start at that day.
cities = {
    "Berlin": {"duration": 5, "fixed_start": 1},         # Annual show from day 1 to 5
    "Split": {"duration": 3},
    "Lyon": {"duration": 5, "fixed_start": 7},             # Wedding must be attended in Lyon between day 7 and 11, so Lyon should be [7-11]
    "Lisbon": {"duration": 3},
    "Bucharest": {"duration": 3, "fixed_start": 13},       # Visit relatives in Bucharest between day 13 and 15 => [13-15]
    "Riga": {"duration": 5},
    "Tallinn": {"duration": 4}
}

# Define direct flights between cities (bidirectional connections)
# Each key has a list of cities that it directly connects to.
flights = {
    "Berlin": ["Lisbon", "Riga", "Split", "Tallinn"],
    "Split": ["Berlin", "Lyon"],
    "Lyon": ["Split", "Lisbon", "Bucharest"],
    "Lisbon": ["Berlin", "Bucharest", "Riga", "Lyon"],
    "Bucharest": ["Lisbon", "Riga", "Lyon"],
    "Riga": ["Berlin", "Bucharest", "Lisbon", "Tallinn"],
    "Tallinn": ["Berlin", "Riga"]
}

# Total trip duration is 22 days (this is implied by the overlaps)
TOTAL_TRIP_DAYS = 22

# Backtracking function to build an itinerary.
# The itinerary is a list of tuples: (city, start_day, end_day)
# The rule for transitions: if you fly on day X, then X is the final day for the departure city and the start day for the arrival city.
def backtrack(itinerary, remaining):
    if not remaining:
        # When itinerary is complete, check if the overall end day equals TOTAL_TRIP_DAYS.
        if itinerary[-1][2] == TOTAL_TRIP_DAYS:
            return itinerary
        else:
            return None

    current_city, _, current_end = itinerary[-1]
    for city in list(remaining):
        # Check if there is a direct flight between the current city and candidate city.
        if city not in flights[current_city]:
            continue

        # Compute the start day for the candidate city (same as the current city's end day due to flight overlap)
        next_start = current_end
        candidate_duration = cities[city]["duration"]
        candidate_end = next_start + candidate_duration - 1

        # If the candidate has a fixed start day constraint, enforce it.
        if "fixed_start" in cities[city]:
            if cities[city]["fixed_start"] != next_start:
                continue

        # Create a new itinerary branch with the candidate city added.
        new_itinerary = itinerary + [(city, next_start, candidate_end)]
        new_remaining = remaining.copy()
        new_remaining.remove(city)

        result = backtrack(new_itinerary, new_remaining)
        if result is not None:
            return result

    return None

def main():
    # Start the itinerary with Berlin (which must be day 1; fixed_start = 1).
    start_city = "Berlin"
    start_day = cities[start_city]["fixed_start"]
    end_day = start_day + cities[start_city]["duration"] - 1  # For Berlin, 1 + 5 - 1 = 5
    initial_itinerary = [(start_city, start_day, end_day)]
    
    # Remaining cities to schedule.
    remaining_cities = set(cities.keys()) - {start_city}
    
    solution = backtrack(initial_itinerary, remaining_cities)
    
    if solution is None:
        output = {"itinerary": []}
    else:
        # Format the itinerary into the desired JSON structure.
        itinerary_output = []
        for city, start, end in solution:
            itinerary_output.append({"day_range": f"Day {start}-{end}", "place": city})
        output = {"itinerary": itinerary_output}
    
    print(json.dumps(output, indent=2))

if __name__ == '__main__':
    main()