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

    # Fixed constraints - (city, start_day, end_day)
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

    # Generate all possible permutations of cities
    cities = list(city_days.keys())
    fixed_cities = {fc[0] for fc in fixed_constraints}
    
    for perm in permutations(cities):
        # Check if all fixed cities are in the permutation
        if not fixed_cities.issubset(set(perm)):
            continue
            
        # Initialize itinerary and tracking variables
        itinerary = []
        used_days = set()
        prev_city = None
        valid = True
        
        # Process fixed constraints first
        for city, start_day, end_day in fixed_constraints:
            days_needed = city_days[city]
            # Check if the fixed stay fits in the allocated days
            if days_needed > (end_day - start_day + 1):
                valid = False
                break
            # Check if days are available
            for day in range(start_day, start_day + days_needed):
                if day in used_days:
                    valid = False
                    break
            if not valid:
                break
                
            # Add to itinerary
            itinerary.append({
                "day_range": f"Day {start_day}-{start_day + days_needed - 1}",
                "place": city
            })
            # Mark days as used
            for day in range(start_day, start_day + days_needed):
                used_days.add(day)
            prev_city = city
        
        if not valid:
            continue
            
        # Process remaining cities in permutation order
        current_day = 1
        for city in perm:
            # Skip cities already processed as fixed constraints
            if city in fixed_cities:
                continue
                
            days_needed = city_days[city]
            
            # Check flight connection
            if prev_city and city not in direct_flights.get(prev_city, []):
                valid = False
                break
                
            # Find next available consecutive days
            start_day = current_day
            while True:
                # Find first available start day
                while start_day in used_days:
                    start_day += 1
                # Check if we have enough consecutive days
                end_day = start_day + days_needed - 1
                if end_day > 24:
                    valid = False
                    break
                # Check if all days in range are available
                all_available = True
                for day in range(start_day, end_day + 1):
                    if day in used_days:
                        all_available = False
                        start_day = day + 1
                        break
                if all_available:
                    break
                if start_day > 24 - days_needed + 1:
                    valid = False
                    break
            
            if not valid:
                break
                
            # Add to itinerary
            itinerary.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": city
            })
            # Mark days as used
            for day in range(start_day, end_day + 1):
                used_days.add(day)
            prev_city = city
            current_day = end_day + 1
        
        # Check if exactly 24 days are covered and all cities included
        if valid and len(used_days) == 24 and len(itinerary) == len(cities):
            # Sort itinerary by day range
            itinerary.sort(key=lambda x: int(x['day_range'].split('-')[0].split(' ')[1]))
            print(json.dumps({"itinerary": itinerary}, indent=2))
            return

    # If no valid itinerary found
    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()