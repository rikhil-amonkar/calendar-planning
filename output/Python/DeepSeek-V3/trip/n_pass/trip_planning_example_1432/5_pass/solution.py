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
                remaining_cities["Frankfurt"] = 0
                break

    if not frankfurt_assigned:
        # Try to find Frankfurt days that might be split but still meet requirements
        frankfurt_days = []
        for day in range(1, 30):
            if itinerary[day] is None:
                frankfurt_days.append(day)
                if len(frankfurt_days) == 4:
                    break
        
        if len(frankfurt_days) == 4:
            # Check if these days can be connected properly
            valid = True
            for i in range(1, len(frankfurt_days)):
                prev_day = frankfurt_days[i] - 1
                if prev_day not in frankfurt_days and itinerary[prev_day] is not None:
                    if "Frankfurt" not in direct_flights.get(itinerary[prev_day], []):
                        valid = False
                        break
            
            if valid:
                for day in frankfurt_days:
                    itinerary[day] = "Frankfurt"
                remaining_cities["Frankfurt"] = 0

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
                remaining_cities["Salzburg"] = 0
                break

    # Assign Reykjavik (4 consecutive days)
    reykjavik_assigned = False
    for start_day in range(1, 27):  # Need 4 consecutive days
        if all(itinerary[d] is None for d in range(start_day, start_day + 4)):
            prev_city = itinerary[start_day - 1] if start_day > 1 else None
            next_city = itinerary[start_day + 4] if start_day + 4 <= 29 else None
            
            # Check flight connections
            if (prev_city is None or "Reykjavik" in direct_flights.get(prev_city, [])) and \
               (next_city is None or next_city in direct_flights.get("Reykjavik", [])):
                for d in range(start_day, start_day + 4):
                    itinerary[d] = "Reykjavik"
                reykjavik_assigned = True
                remaining_cities["Reykjavik"] = 0
                break

    # Assign Bucharest (3 consecutive days)
    bucharest_assigned = False
    for start_day in range(1, 28):  # Need 3 consecutive days
        if all(itinerary[d] is None for d in range(start_day, start_day + 3)):
            prev_city = itinerary[start_day - 1] if start_day > 1 else None
            next_city = itinerary[start_day + 3] if start_day + 3 <= 29 else None
            
            # Check flight connections
            if (prev_city is None or "Bucharest" in direct_flights.get(prev_city, [])) and \
               (next_city is None or next_city in direct_flights.get("Bucharest", [])):
                for d in range(start_day, start_day + 3):
                    itinerary[d] = "Bucharest"
                bucharest_assigned = True
                remaining_cities["Bucharest"] = 0
                break

    # Assign remaining cities
    remaining_days = [day for day in range(1, 30) if itinerary[day] is None]
    for city in remaining_cities:
        if remaining_cities[city] > 0:
            # Try to assign remaining days for this city
            for day in remaining_days:
                if itinerary[day] is None:
                    prev_city = itinerary[day - 1] if day > 1 else None
                    next_city = itinerary[day + 1] if day < 29 else None
                    
                    if (prev_city is None or city in direct_flights.get(prev_city, [])) and \
                       (next_city is None or next_city in direct_flights.get(city, [])):
                        itinerary[day] = city
                        remaining_cities[city] -= 1
                        if remaining_cities[city] == 0:
                            break

    # Final check for any remaining unassigned days
    for day in range(1, 30):
        if itinerary[day] is None:
            # Assign any city that fits flight connections
            prev_city = itinerary[day - 1] if day > 1 else None
            next_city = itinerary[day + 1] if day < 29 else None
            
            for city in remaining_cities:
                if (prev_city is None or city in direct_flights.get(prev_city, [])) and \
                   (next_city is None or next_city in direct_flights.get(city, [])):
                    itinerary[day] = city
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