import json
from itertools import permutations

def main():
    # Define cities and their required days
    cities = {
        "Paris": 5,
        "Warsaw": 2,
        "Krakow": 2,
        "Tallinn": 2,
        "Riga": 2,
        "Copenhagen": 5,
        "Helsinki": 5,
        "Oslo": 5,
        "Santorini": 2,
        "Lyon": 4
    }

    # Define constraints
    constraints = [
        ("Paris", (4, 8)),
        ("Krakow", (17, 18)),
        ("Riga", (23, 24)),
        ("Helsinki", (18, 22)),
        ("Santorini", (12, 13))
    ]

    # Define direct flights
    flights = {
        "Warsaw": ["Riga", "Tallinn", "Copenhagen", "Paris", "Helsinki", "Oslo"],
        "Riga": ["Warsaw", "Paris", "Helsinki", "Copenhagen", "Tallinn", "Oslo"],
        "Tallinn": ["Warsaw", "Oslo", "Helsinki", "Copenhagen", "Paris", "Riga"],
        "Copenhagen": ["Helsinki", "Warsaw", "Lyon", "Oslo", "Santorini", "Krakow", "Riga", "Tallinn", "Paris"],
        "Helsinki": ["Copenhagen", "Warsaw", "Oslo", "Krakow", "Paris", "Riga", "Tallinn"],
        "Oslo": ["Lyon", "Paris", "Copenhagen", "Warsaw", "Riga", "Tallinn", "Helsinki", "Krakow", "Santorini"],
        "Paris": ["Lyon", "Oslo", "Warsaw", "Riga", "Tallinn", "Helsinki", "Krakow", "Copenhagen"],
        "Krakow": ["Helsinki", "Warsaw", "Copenhagen", "Paris", "Oslo"],
        "Santorini": ["Copenhagen", "Oslo"],
        "Lyon": ["Paris", "Oslo", "Copenhagen"]
    }

    # Generate all possible city orders (permutations)
    city_names = list(cities.keys())
    possible_orders = permutations(city_names)

    best_itinerary = None
    best_score = float('inf')

    for order in possible_orders:
        try:
            itinerary = []
            current_day = 1
            prev_city = None

            for city in order:
                required_days = cities[city]
                start_day = current_day
                end_day = current_day + required_days - 1

                # Check if this city has constraints
                for const_city, (const_start, const_end) in constraints:
                    if city == const_city:
                        # Adjust to meet constraint
                        if end_day < const_start:
                            # Need to move this visit later
                            start_day = const_start - required_days + 1
                            end_day = const_start
                        elif start_day > const_end:
                            # Need to move this visit earlier
                            end_day = const_end
                            start_day = const_end - required_days + 1

                # Check flight connection
                if prev_city and prev_city != city:
                    if city not in flights[prev_city]:
                        raise ValueError("No flight connection")

                itinerary.append({
                    "day_range": f"Day {start_day}-{end_day}",
                    "place": city
                })
                current_day = end_day + 1
                prev_city = city

            # Check if all cities are visited within 25 days
            if current_day - 1 <= 25:
                # Score based on how well constraints are met
                score = 0
                for const_city, (const_start, const_end) in constraints:
                    for visit in itinerary:
                        if visit["place"] == const_city:
                            day_start = int(visit["day_range"].split("-")[0].split(" ")[1])
                            day_end = int(visit["day_range"].split("-")[1])
                            # Check if constraint is fully within visit
                            if not (day_start <= const_start and day_end >= const_end):
                                score += 1
                if score < best_score:
                    best_score = score
                    best_itinerary = itinerary

        except ValueError:
            continue

    # Output the best itinerary found
    if best_itinerary:
        print(json.dumps({"itinerary": best_itinerary}))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()