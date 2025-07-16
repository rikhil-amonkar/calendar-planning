import json

def main():
    # Cities and their required stay days
    cities = {
        "Frankfurt": 4,
        "Salzburg": 5,
        "Athens": 5,
        "Reykjavik": 4,
        "Bucharest": 3,
        "Valencia": 2,
        "Vienna": 4,
        "Amsterdam": 3,
        "Stockholm": 3,
        "Riga": 2
    }

    # Constraints
    constraints = {
        "Athens": (14, 18),
        "Valencia": (5, 6),
        "Vienna": (6, 10),
        "Stockholm": (1, 3),
        "Riga": (19, 20)
    }

    # Direct flights
    direct_flights = {
        "Valencia": ["Frankfurt", "Athens", "Amsterdam", "Bucharest", "Vienna"],
        "Vienna": ["Bucharest", "Riga", "Frankfurt", "Amsterdam", "Athens", "Reykjavik", "Stockholm"],
        "Athens": ["Valencia", "Bucharest", "Riga", "Frankfurt", "Stockholm", "Reykjavik", "Amsterdam", "Vienna"],
        "Riga": ["Frankfurt", "Vienna", "Bucharest", "Amsterdam", "Stockholm"],
        "Amsterdam": ["Bucharest", "Frankfurt", "Reykjavik", "Stockholm", "Valencia", "Vienna", "Riga", "Athens"],
        "Stockholm": ["Athens", "Vienna", "Amsterdam", "Riga", "Frankfurt", "Reykjavik"],
        "Frankfurt": ["Valencia", "Riga", "Amsterdam", "Salzburg", "Bucharest", "Vienna", "Stockholm", "Athens"],
        "Bucharest": ["Vienna", "Athens", "Amsterdam", "Valencia", "Frankfurt", "Riga"],
        "Reykjavik": ["Amsterdam", "Frankfurt", "Athens", "Stockholm", "Vienna"],
        "Salzburg": ["Frankfurt"]
    }

    # Initialize itinerary with fixed constraints
    itinerary = {}
    for day in range(1, 30):
        itinerary[day] = None

    # Assign fixed cities first
    for city, (start, end) in constraints.items():
        for day in range(start, end + 1):
            itinerary[day] = city

    # Assign remaining cities with proper flight connections
    remaining_cities = {city: cities[city] for city in cities}
    for city in constraints:
        remaining_cities[city] = 0  # These are already fully assigned

    # Helper function to find next available day
    def next_available_day(start_day):
        for day in range(start_day, 30):
            if itinerary[day] is None:
                return day
        return None

    # Assign Frankfurt (4 days)
    frankfurt_days = 0
    day = next_available_day(1)
    while frankfurt_days < 4 and day is not None:
        # Check flight connection with previous day
        prev_city = itinerary[day-1] if day > 1 else None
        if prev_city is None or "Frankfurt" in direct_flights.get(prev_city, []):
            itinerary[day] = "Frankfurt"
            frankfurt_days += 1
            day = next_available_day(day + 1)
        else:
            day += 1

    # Assign other cities with flight connections
    for city, required_days in remaining_cities.items():
        if required_days == 0:
            continue
            
        assigned_days = 0
        day = next_available_day(1)
        while assigned_days < required_days and day is not None:
            # Check flight connection
            prev_city = itinerary[day-1] if day > 1 else None
            if prev_city is None or city in direct_flights.get(prev_city, []):
                itinerary[day] = city
                assigned_days += 1
                day = next_available_day(day + 1)
            else:
                day += 1

    # Convert to day ranges
    day_ranges = []
    current_place = itinerary[1]
    start_day = 1
    for day in range(2, 30):
        if itinerary[day] != current_place:
            day_ranges.append({
                "day_range": f"Day {start_day}-{day-1}",
                "place": current_place
            })
            current_place = itinerary[day]
            start_day = day
    day_ranges.append({
        "day_range": f"Day {start_day}-29",
        "place": current_place
    })

    # Output JSON
    output = {"itinerary": day_ranges}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()