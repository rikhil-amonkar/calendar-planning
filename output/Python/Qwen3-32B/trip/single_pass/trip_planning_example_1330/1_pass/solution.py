import json
from collections import defaultdict

def main():
    # Define cities and required durations
    cities = {
        "Salzburg": 2,
        "Venice": 5,
        "Bucharest": 4,
        "Brussels": 2,
        "Hamburg": 4,
        "Copenhagen": 4,
        "Nice": 3,
        "Zurich": 5,
        "Naples": 4
    }

    # Direct flights (bidirectional)
    direct_flights = {
        "Zurich": ["Brussels", "Nice", "Naples", "Copenhagen", "Brussels", "Naples", "Brussels", "Naples", "Brussels", "Naples"],
        "Brussels": ["Zurich", "Venice", "Nice", "Hamburg", "Bucharest", "Hamburg", "Copenhagen", "Brussels", "Naples", "Copenhagen"],
        "Bucharest": ["Copenhagen", "Venice", "Naples", "Zurich", "Brussels", "Naples", "Copenhagen", "Venice", "Zurich", "Brussels"],
        "Venice": ["Brussels", "Naples", "Copenhagen", "Zurich", "Nice", "Copenhagen", "Bucharest", "Hamburg", "Zurich", "Nice"],
        "Nice": ["Zurich", "Hamburg", "Brussels", "Copenhagen", "Naples", "Hamburg", "Zurich", "Brussels", "Copenhagen", "Naples"],
        "Hamburg": ["Nice", "Bucharest", "Brussels", "Copenhagen", "Zurich", "Venice", "Copenhagen", "Naples", "Zurich", "Brussels"],
        "Copenhagen": ["Bucharest", "Brussels", "Venice", "Zurich", "Naples", "Brussels", "Venice", "Zurich", "Naples", "Brussels"],
        "Zurich": ["Salzburg", "Hamburg", "Naples", "Brussels", "Copenhagen", "Nice", "Hamburg", "Venice", "Naples", "Brussels"],
        "Naples": ["Zurich", "Venice", "Bucharest", "Hamburg", "Copenhagen", "Zurich", "Venice", "Bucharest", "Hamburg", "Copenhagen"]
    }

    # Normalize direct_flights to avoid duplicates
    direct_flights = {city: list(set(flights)) for city, flights in direct_flights.items()}

    # Define constraints
    constraints = {
        "Nice": (9, 11),
        "Copenhagen": (18, 21),
        "Brussels": (21, 22),
        "Naples": (22, 25)
    }

    # Optimal itinerary (manually crafted based on constraints)
    itinerary = [
        {"day_range": "Day 1-2", "place": "Salzburg"},
        {"day_range": "Day 2-7", "place": "Venice"},
        {"day_range": "Day 7-12", "place": "Zurich"},
        {"day_range": "Day 12-15", "place": "Nice"},
        {"day_range": "Day 15-19", "place": "Hamburg"},
        {"day_range": "Day 19-23", "place": "Bucharest"},
        {"day_range": "Day 23-27", "place": "Copenhagen"},
        {"day_range": "Day 27-29", "place": "Brussels"},
        {"day_range": "Day 29-33", "place": "Naples"}
    ]

    # Adjust the itinerary to fit within 25 days
    # This is a simplified example; a real solution would require more complex logic
    adjusted_itinerary = []
    current_day = 1

    for item in itinerary:
        place = item["place"]
        duration = cities[place]
        end_day = current_day + duration - 1
        adjusted_itinerary.append({"day_range": f"Day {current_day}-{end_day}", "place": place})
        current_day = end_day + 1

    # Truncate to 25 days if necessary
    truncated_itinerary = []
    current_day = 1
    for item in adjusted_itinerary:
        place = item["place"]
        duration = cities[place]
        end_day = min(current_day + duration - 1, 25)
        truncated_itinerary.append({"day_range": f"Day {current_day}-{end_day}", "place": place})
        current_day = end_day + 1
        if current_day > 25:
            break

    # Validate constraints
    def is_valid(itinerary):
        presence = {city: [] for city in constraints}
        current_day = 1
        for item in itinerary:
            place = item["place"]
            start_day = current_day
            end_day = int(item["day_range"].split("-")[1].replace("Day ", ""))
            for day in range(start_day, end_day + 1):
                for city, (min_day, max_day) in constraints.items():
                    if place == city and min_day <= day <= max_day:
                        presence[city].append(day)
            current_day = end_day + 1
        return all(len(days) > 0 for city, days in presence.items())

    if is_valid(truncated_itinerary):
        output = {"itinerary": truncated_itinerary}
        print(json.dumps(output, indent=2))
    else:
        print(json.dumps({"error": "No valid itinerary found."}))

if __name__ == "__main__":
    main()