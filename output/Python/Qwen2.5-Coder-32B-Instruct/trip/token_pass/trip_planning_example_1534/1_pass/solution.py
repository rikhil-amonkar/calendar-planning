import json
from collections import defaultdict

# Define the constraints
constraints = {
    "Warsaw": {"days": 4},
    "Venice": {"days": 3},
    "Vilnius": {"days": 3},
    "Salzburg": {"days": 4, "events": [(22, 25)]},  # Wedding
    "Amsterdam": {"days": 2},
    "Barcelona": {"days": 5, "events": [(2, 6)]},  # Friend meeting
    "Paris": {"days": 2, "events": [(1, 2)]},      # Workshop
    "Hamburg": {"days": 4, "events": [(19, 22)]},  # Conference
    "Florence": {"days": 5},
    "Tallinn": {"days": 2, "events": [(11, 12)]}    # Friend meeting
}

# Define the graph of direct flights
direct_flights = {
    "Paris": ["Venice", "Hamburg", "Vilnius", "Amsterdam", "Florence", "Warsaw", "Tallinn", "Barcelona"],
    "Barcelona": ["Amsterdam", "Warsaw", "Hamburg", "Florence", "Venice", "Tallinn"],
    "Amsterdam": ["Paris", "Barcelona", "Warsaw", "Vilnius", "Hamburg", "Florence", "Tallinn"],
    "Warsaw": ["Paris", "Venice", "Barcelona", "Vilnius", "Hamburg", "Tallinn"],
    "Venice": ["Paris", "Barcelona", "Hamburg", "Warsaw"],
    "Hamburg": ["Paris", "Barcelona", "Amsterdam", "Warsaw", "Salzburg", "Venice"],
    "Florence": ["Paris", "Barcelona", "Amsterdam", "Tallinn"],
    "Vilnius": ["Paris", "Amsterdam", "Warsaw", "Tallinn"],
    "Tallinn": ["Paris", "Barcelona", "Amsterdam", "Warsaw", "Vilnius", "Florence"],
    "Salzburg": ["Hamburg"]
}

# Initialize the schedule
schedule = []

# Helper function to find the next available day
def find_next_available_day(current_day):
    for day in range(current_day + 1, 26):
        if all(day not in range(event[0], event[1] + 1) for city in constraints for event in constraints[city].get("events", [])):
            return day
    return None

# Function to add a city to the schedule
def add_city_to_schedule(city, start_day):
    days = constraints[city]["days"]
    end_day = start_day + days - 1
    schedule.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
    return end_day

# Start with Paris for the workshop
current_day = add_city_to_schedule("Paris", 1)

# Friend meeting in Barcelona from day 2 to day 6
current_day = add_city_to_schedule("Barcelona", 2)

# Add Vilnius after Barcelona
current_day = find_next_available_day(current_day)
current_day = add_city_to_schedule("Vilnius", current_day)

# Add Warsaw after Vilnius
current_day = find_next_available_day(current_day)
current_day = add_city_to_schedule("Warsaw", current_day)

# Add Florence after Warsaw
current_day = find_next_available_day(current_day)
current_day = add_city_to_schedule("Florence", current_day)

# Add Tallinn after Florence
current_day = find_next_available_day(current_day)
current_day = add_city_to_schedule("Tallinn", current_day)

# Add Amsterdam after Tallinn
current_day = find_next_available_day(current_day)
current_day = add_city_to_schedule("Amsterdam", current_day)

# Add Hamburg for the conference
current_day = add_city_to_schedule("Hamburg", 19)

# Add Salzburg for the wedding
current_day = add_city_to_schedule("Salzburg", 22)

# Output the schedule as JSON
output = {"itinerary": schedule}
print(json.dumps(output, indent=4))