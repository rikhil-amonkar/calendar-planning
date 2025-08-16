import json
from datetime import timedelta

# Define the constraints
constraints = {
    "Paris": {"days": 5, "meeting": (4, 8)},
    "Warsaw": {"days": 2},
    "Krakow": {"days": 2, "workshop": (17, 18)},
    "Tallinn": {"days": 2},
    "Riga": {"days": 2, "wedding": (23, 24)},
    "Copenhagen": {"days": 5},
    "Helsinki": {"days": 5, "friend": (18, 22)},
    "Oslo": {"days": 5},
    "Santorini": {"days": 2, "relatives": (12, 13)},
    "Lyon": {"days": 4}
}

# Define the direct flight connections
connections = {
    "Warsaw": ["Riga", "Tallinn", "Copenhagen", "Krakow", "Helsinki"],
    "Riga": ["Warsaw", "Tallinn", "Oslo", "Helsinki", "Copenhagen", "Paris"],
    "Tallinn": ["Warsaw", "Riga", "Oslo", "Helsinki"],
    "Copenhagen": ["Helsinki", "Warsaw", "Lyon", "Oslo", "Santorini", "Krakow", "Riga"],
    "Lyon": ["Paris", "Oslo", "Copenhagen"],
    "Paris": ["Oslo", "Riga", "Tallinn", "Krakow", "Helsinki", "Copenhagen", "Lyon"],
    "Krakow": ["Helsinki", "Warsaw", "Copenhagen", "Paris"],
    "Helsinki": ["Warsaw", "Riga", "Tallinn", "Copenhagen", "Krakow", "Oslo"],
    "Oslo": ["Lyon", "Paris", "Copenhagen", "Tallinn", "Helsinki", "Krakow", "Santorini", "Warsaw"],
    "Santorini": ["Copenhagen", "Oslo"]
}

def find_itinerary(constraints, connections):
    def is_valid_day(day, city):
        if city == "Paris":
            return constraints[city]["meeting"][0] <= day <= constraints[city]["meeting"][1]
        elif city == "Krakow":
            return constraints[city]["workshop"][0] <= day <= constraints[city]["workshop"][1]
        elif city == "Riga":
            return constraints[city]["wedding"][0] <= day <= constraints[city]["wedding"][1]
        elif city == "Helsinki":
            return constraints[city]["friend"][0] <= day <= constraints[city]["friend"][1]
        elif city == "Santorini":
            return constraints[city]["relatives"][0] <= day <= constraints[city]["relatives"][1]
        return True

    def backtrack(day, current_city, visited_cities, itinerary):
        if len(visited_cities) == len(constraints) and day == 26:
            return itinerary

        for next_city in connections[current_city]:
            if next_city not in visited_cities:
                days_in_next_city = constraints[next_city]["days"]
                if all(is_valid_day(day + i, next_city) for i in range(days_in_next_city)):
                    new_itinerary = itinerary + [(day, day + days_in_next_city - 1, next_city)]
                    result = backtrack(day + days_in_next_city, next_city, visited_cities | {next_city}, new_itinerary)
                    if result:
                        return result
        return None

    # Try starting from each city to ensure we find a valid itinerary
    for start_city in constraints:
        initial_days = constraints[start_city]["days"]
        if all(is_valid_day(i, start_city) for i in range(1, initial_days + 1)):
            initial_itinerary = [(1, initial_days, start_city)]
            final_itinerary = backtrack(initial_days + 1, start_city, {start_city}, initial_itinerary)
            if final_itinerary:
                return final_itinerary

    return None

itinerary = find_itinerary(constraints, connections)
if itinerary is not None:
    formatted_itinerary = [{"day_range": f"Day {start}-{end}", "place": place} for start, end, place in itinerary]
    print(json.dumps({"itinerary": formatted_itinerary}))
else:
    print("No valid itinerary found.")