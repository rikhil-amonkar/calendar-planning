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

    # Constraints (city: (start_day, end_day))
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

    # Assign remaining required cities with proper flight connections
    remaining_cities = {city: cities[city] for city in cities}
    for city in constraints:
        remaining_cities[city] = 0  # These are already fully assigned

    # Assign Frankfurt (4 consecutive days)
    frankfurt_assigned = False
    for start_day in range(1, 27):  # Need 4 consecutive days
        if all(itinerary[d] is None for d in range(start_day, start_day + 4)):
            prev_city = itinerary[start_day - 1] if start_day > 1 else None
            next_city = itinerary[start_day + 4] if start_day + 4 <= 29 else None
            
            # Check flight connections
            if (prev_city is None or "Frankfurt" in direct_flights.get(prev_city, [])) and \
               (next_city is None or next_city in direct_flights.get("Frankfurt", [])):
                for d in range(start_day, start_day + 4):
                    itinerary[d] = "Frankfurt"
                frankfurt_assigned = True
                break

    if not frankfurt_assigned:
        # Fallback - assign any 4 available days
        days_assigned = 0
        for day in range(1, 30):
            if itinerary[day] is None and days_assigned < 4:
                itinerary[day] = "Frankfurt"
                days_assigned += 1

    # Assign Salzburg (5 consecutive days)
    salzburg_assigned = False
    for start_day in range(1, 26):  # Need 5 consecutive days
        if all(itinerary[d] is None for d in range(start_day, start_day + 5)):
            prev_city = itinerary[start_day - 1] if start_day > 1 else None
            next_city = itinerary[start_day + 5] if start_day + 5 <= 29 else None
            
            # Salzburg can only be reached from Frankfurt
            if (prev_city == "Frankfurt" or prev_city is None) and \
               (next_city is None or next_city in direct_flights.get("Salzburg", [])):
                for d in range(start_day, start_day + 5):
                    itinerary[d] = "Salzburg"
                salzburg_assigned = True
                break

    if not salzburg_assigned:
        # Fallback - assign any 5 available days after Frankfurt
        days_assigned = 0
        for day in range(1, 30):
            if itinerary[day] is None and days_assigned < 5 and \
               (day == 1 or itinerary[day - 1] == "Frankfurt"):
                itinerary[day] = "Salzburg"
                days_assigned += 1

    # Assign remaining cities
    remaining_days = [day for day in range(1, 30) if itinerary[day] is None]
    for day in remaining_days:
        prev_city = itinerary[day - 1] if day > 1 else None
        next_city = itinerary[day + 1] if day < 29 else None
        
        possible_cities = []
        for city in remaining_cities:
            if remaining_cities[city] > 0:
                # Check flight connections
                if (prev_city is None or city in direct_flights.get(prev_city, [])) and \
                   (next_city is None or next_city in direct_flights.get(city, [])):
                    possible_cities.append(city)
        
        if possible_cities:
            # Prioritize cities with most remaining days needed
            possible_cities.sort(key=lambda x: remaining_cities[x], reverse=True)
            chosen_city = possible_cities[0]
            itinerary[day] = chosen_city
            remaining_cities[chosen_city] -= 1
        else:
            # As last resort, use a city that connects at least one way
            for city in remaining_cities:
                if remaining_cities[city] > 0 and \
                   (prev_city is None or city in direct_flights.get(prev_city, [])):
                    itinerary[day] = city
                    remaining_cities[city] -= 1
                    break

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