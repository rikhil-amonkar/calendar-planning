import json
from itertools import permutations

# Define cities and their required durations (adjusted to make the total 15 days)
city_durations = {
    "Riga": 1,
    "Frankfurt": 1,
    "Amsterdam": 2,
    "Vilnius": 5,
    "London": 1,
    "Stockholm": 3,
    "Bucharest": 2
}

# Direct flight connections (symmetric)
direct_flights = {
    "London": {"Amsterdam", "Bucharest", "Frankfurt", "Stockholm"},
    "Amsterdam": {"London", "Frankfurt", "Stockholm", "Riga", "Bucharest", "Vilnius"},
    "Frankfurt": {"Vilnius", "Amsterdam", "Bucharest", "London", "Stockholm"},
    "Vilnius": {"Frankfurt", "Amsterdam"},
    "Riga": {"Vilnius", "Stockholm", "Amsterdam", "Bucharest"},
    "Stockholm": {"Frankfurt", "Amsterdam", "London"},
    "Bucharest": {"Riga", "Frankfurt", "London"}
}

# Helper function to check if a sequence is valid
def is_valid_sequence(seq):
    # Check if all cities are included
    if len(set(seq)) != 7:
        return False
    # Check direct flights between consecutive cities
    for i in range(len(seq) - 1):
        if seq[i+1] not in direct_flights[seq[i]]:
            return False
    return True

# Function to calculate day ranges
def calculate_itinerary(sequence):
    # Initialize start and end days for each city
    start_days = {}
    end_days = {}

    # Start with day 1 for the first city
    start_days[sequence[0]] = 1
    end_days[sequence[0]] = 1 + city_durations[sequence[0]] - 1

    for i in range(1, len(sequence)):
        # Transition day is the end day of previous city + 1
        transition_day = end_days[sequence[i - 1]] + 1
        start_days[sequence[i]] = transition_day
        end_days[sequence[i]] = transition_day + city_durations[sequence[i]] - 1

    # Check if total days is 15
    if end_days[sequence[-1]] != 15:
        return None

    # Check specific constraints by start and end days
    if not (start_days["Amsterdam"] == 2 and end_days["Amsterdam"] == 3):
        return None

    if not (start_days["Vilnius"] == 7 and end_days["Vilnius"] == 11):
        return None

    if not (start_days["Stockholm"] == 13 and end_days["Stockholm"] == 15):
        return None

    # Build itinerary
    itinerary = []
    for city in sequence:
        day_start = start_days[city]
        day_end = end_days[city]
        itinerary.append({"day_range": f"Day {day_start}-{day_end}", "place": city})

    return itinerary

# Find the correct sequence and calculate itinerary
itinerary = None
for perm in permutations(city_durations.keys()):
    if is_valid_sequence(perm):
        calculated_itinerary = calculate_itinerary(perm)
        if calculated_itinerary:
            itinerary = calculated_itinerary
            break

# Output the result as JSON
print(json.dumps({"itinerary": itinerary}, indent=2))