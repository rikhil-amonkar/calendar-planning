import json
from itertools import permutations

def main():
    # Cities and their required days
    city_days = {
        "Venice": 3,
        "Reykjavik": 2,
        "Munich": 3,
        "Santorini": 3,
        "Manchester": 3,
        "Porto": 3,
        "Bucharest": 5,
        "Tallinn": 4,
        "Valencia": 2,
        "Vienna": 5
    }

    # Fixed constraints
    fixed_constraints = [
        ("Munich", 4, 6),
        ("Santorini", 8, 10),
        ("Valencia", 14, 15)
    ]

    # Direct flights
    direct_flights = {
        "Bucharest": ["Manchester", "Valencia", "Vienna", "Munich", "Santorini"],
        "Manchester": ["Bucharest", "Santorini", "Vienna", "Porto", "Venice", "Munich"],
        "Munich": ["Venice", "Porto", "Manchester", "Reykjavik", "Vienna", "Valencia", "Bucharest", "Tallinn"],
        "Santorini": ["Manchester", "Venice", "Vienna", "Bucharest"],
        "Vienna": ["Reykjavik", "Valencia", "Manchester", "Porto", "Venice", "Santorini", "Bucharest", "Munich"],
        "Venice": ["Munich", "Santorini", "Manchester", "Vienna"],
        "Porto": ["Munich", "Vienna", "Valencia", "Manchester"],
        "Valencia": ["Vienna", "Porto", "Bucharest", "Munich"],
        "Reykjavik": ["Vienna", "Munich"],
        "Tallinn": ["Munich"]
    }

    # Correcting the direct_flights dictionary (fixing typos)
    direct_flights_corrected = {
        "Bucharest": ["Manchester", "Valencia", "Vienna", "Munich", "Santorini"],
        "Manchester": ["Bucharest", "Santorini", "Vienna", "Porto", "Venice", "Munich"],
        "Munich": ["Venice", "Porto", "Manchester", "Reykjavik", "Vienna", "Valencia", "Bucharest", "Tallinn"],
        "Santorini": ["Manchester", "Venice", "Vienna", "Bucharest"],
        "Vienna": ["Reykjavik", "Valencia", "Manchester", "Porto", "Venice", "Santorini", "Bucharest", "Munich"],
        "Venice": ["Munich", "Santorini", "Manchester", "Vienna"],
        "Porto": ["Munich", "Vienna", "Valencia", "Manchester"],
        "Valencia": ["Vienna", "Porto", "Bucharest", "Munich"],
        "Reykjavik": ["Vienna", "Munich"],
        "Tallinn": ["Munich"]
    }

    # Correcting the direct_flights dictionary (fixing typos)
    direct_flights = {
        "Bucharest": ["Manchester", "Valencia", "Vienna", "Munich", "Santorini"],
        "Manchester": ["Bucharest", "Santorini", "Vienna", "Porto", "Venice", "Munich"],
        "Munich": ["Venice", "Porto", "Manchester", "Reykjavik", "Vienna", "Valencia", "Bucharest", "Tallinn"],
        "Santorini": ["Manchester", "Venice", "Vienna", "Bucharest"],
        "Vienna": ["Reykjavik", "Valencia", "Manchester", "Porto", "Venice", "Santorini", "Bucharest", "Munich"],
        "Venice": ["Munich", "Santorini", "Manchester", "Vienna"],
        "Porto": ["Munich", "Vienna", "Valencia", "Manchester"],
        "Valencia": ["Vienna", "Porto", "Bucharest", "Munich"],
        "Reykjavik": ["Vienna", "Munich"],
        "Tallinn": ["Munich"]
    }

    # Check if all cities are in direct_flights
    for city in city_days:
        if city not in direct_flights:
            print(f"Error: {city} not found in direct_flights")
            return

    # Generate all possible permutations of cities
    cities = list(city_days.keys())
    for perm in permutations(cities):
        itinerary = []
        current_day = 1
        prev_city = None

        # Check fixed constraints
        valid = True
        for city, start_day, end_day in fixed_constraints:
            if city not in perm:
                valid = False
                break
            city_index = perm.index(city)
            days_needed = city_days[city]
            # Check if the city can be placed within the fixed days
            if end_day - start_day + 1 < days_needed:
                valid = False
                break
        if not valid:
            continue

        # Try to build itinerary
        for city in perm:
            days_needed = city_days[city]
            # Check if we can fly to this city from previous city
            if prev_city and city not in direct_flights[prev_city]:
                valid = False
                break
            # Check fixed constraints
            for fc_city, start_day, end_day in fixed_constraints:
                if fc_city == city:
                    if current_day > start_day or current_day + days_needed - 1 < start_day:
                        valid = False
                        break
                    # Adjust current_day to match fixed constraint
                    current_day = start_day
            if not valid:
                break
            # Add to itinerary
            end_day = current_day + days_needed - 1
            itinerary.append({
                "day_range": f"Day {current_day}-{end_day}",
                "place": city
            })
            current_day = end_day + 1
            prev_city = city

        # Check if all days are covered
        if valid and current_day - 1 <= 24:
            # Check if all cities are included
            included_cities = {item["place"] for item in itinerary}
            if included_cities == set(cities):
                # Output the itinerary
                print(json.dumps({"itinerary": itinerary}))
                return

    # If no valid itinerary found
    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()