import json
from itertools import permutations

def main():
    # Define cities and their required days
    cities = {
        "Zurich": 2,
        "Bucharest": 2,
        "Hamburg": 5,
        "Barcelona": 4,
        "Reykjavik": 5,
        "Stuttgart": 5,
        "Stockholm": 2,
        "Tallinn": 4,
        "Milan": 5,
        "London": 3
    }
    
    # Fixed constraints
    fixed_constraints = [
        ("London", (1, 3)),
        ("Milan", (3, 7)),
        ("Zurich", (7, 8)),
        ("Reykjavik", (9, 13))
    ]
    
    # Direct flights
    direct_flights = {
        "London": ["Hamburg", "Reykjavik", "Stuttgart", "Barcelona", "Bucharest", "Stockholm", "Zurich", "Milan"],
        "Hamburg": ["London", "Stockholm", "Bucharest", "Milan", "Stuttgart", "Barcelona", "Zurich"],
        "Reykjavik": ["London", "Barcelona", "Stuttgart", "Stockholm", "Milan", "Zurich"],
        "Milan": ["Barcelona", "Zurich", "Hamburg", "Stockholm", "Stuttgart", "Reykjavik", "London"],
        "Barcelona": ["Milan", "Reykjavik", "London", "Stockholm", "Bucharest", "Tallinn", "Zurich", "Hamburg", "Stuttgart"],
        "Stuttgart": ["Reykjavik", "London", "Stockholm", "Milan", "Hamburg", "Barcelona"],
        "Stockholm": ["Hamburg", "Reykjavik", "London", "Milan", "Stuttgart", "Barcelona", "Tallinn", "Zurich"],
        "Tallinn": ["Stockholm", "Barcelona", "Zurich"],
        "Bucharest": ["Hamburg", "London", "Barcelona", "Zurich"],
        "Zurich": ["London", "Milan", "Hamburg", "Barcelona", "Stockholm", "Tallinn", "Reykjavik", "Bucharest"]
    }
    
    # Initialize itinerary with fixed constraints
    itinerary = []
    for city, (start, end) in fixed_constraints:
        itinerary.append({"day_range": f"Day {start}-{end}", "place": city})
    
    # Collect all cities not in fixed constraints
    remaining_cities = [city for city in cities if city not in [fc[0] for fc in fixed_constraints]]
    remaining_days = {city: cities[city] for city in remaining_cities}
    
    # Days already allocated
    allocated_days = set()
    for fc in fixed_constraints:
        start, end = fc[1]
        allocated_days.update(range(start, end + 1))
    
    # Find available days (1-28 not in allocated_days)
    available_days = [day for day in range(1, 29) if day not in allocated_days]
    
    # Function to check if two cities are connected
    def is_connected(city1, city2):
        return city2 in direct_flights.get(city1, [])
    
    # Function to find the last city in the itinerary before a given day
    def get_last_city_before(day):
        for entry in reversed(itinerary):
            day_range = entry["day_range"]
            start_day = int(day_range.split('-')[0].split(' ')[1])
            end_day = int(day_range.split('-')[1])
            if start_day <= day <= end_day:
                return entry["place"]
            if end_day < day:
                return entry["place"]
        return None
    
    # Try to place remaining cities
    for city in remaining_cities:
        required_days = remaining_days[city]
        # Find all possible day ranges that fit the required days
        possible_ranges = []
        for i in range(len(available_days) - required_days + 1):
            start_day = available_days[i]
            end_day = available_days[i + required_days - 1]
            if end_day - start_day + 1 == required_days:
                # Check connection with previous city
                prev_city = get_last_city_before(start_day - 1)
                if prev_city is None or is_connected(prev_city, city):
                    possible_ranges.append((start_day, end_day))
        
        # Place the city in the first valid range
        if possible_ranges:
            start_day, end_day = possible_ranges[0]
            itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
            # Update allocated_days and available_days
            allocated_days.update(range(start_day, end_day + 1))
            available_days = [day for day in range(1, 29) if day not in allocated_days]
    
    # Sort itinerary by day range
    itinerary.sort(key=lambda x: int(x["day_range"].split('-')[0].split(' ')[1]))
    
    # Verify all cities are included
    included_cities = {entry["place"] for entry in itinerary}
    if included_cities != set(cities.keys()):
        # If missing cities, try to fit them in remaining gaps
        missing_cities = set(cities.keys()) - included_cities
        for city in missing_cities:
            required_days = cities[city]
            # Find any available consecutive days
            for i in range(len(available_days) - required_days + 1):
                start_day = available_days[i]
                end_day = available_days[i + required_days - 1]
                if end_day - start_day + 1 == required_days:
                    prev_city = get_last_city_before(start_day - 1)
                    if prev_city is None or is_connected(prev_city, city):
                        itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
                        allocated_days.update(range(start_day, end_day + 1))
                        available_days = [day for day in range(1, 29) if day not in allocated_days])
                        break
    
    # Final sort
    itinerary.sort(key=lambda x: int(x["day_range"].split('-')[0].split(' ')[1]))
    
    # Output the result
    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    main()