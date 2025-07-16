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
    for perm in permutations(cities):
        itinerary = []
        current_day = 1
        prev_city = None
        valid = True
        used_days = set()
        fixed_cities = {fc[0] for fc in fixed_constraints}
        
        # First check if all fixed cities are in the permutation
        if not fixed_cities.issubset(set(perm)):
            continue
            
        # Try to build itinerary
        for city in perm:
            days_needed = city_days[city]
            
            # Check if we can fly to this city from previous city
            if prev_city and city not in direct_flights[prev_city]:
                valid = False
                break
                
            # Check if this city has fixed constraints
            fixed_days = None
            for fc_city, start_day, end_day in fixed_constraints:
                if fc_city == city:
                    fixed_days = (start_day, end_day)
                    break
                    
            if fixed_days:
                start_day, end_day = fixed_days
                # Check if city can fit in the fixed days
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
                # Update current_day to after this visit
                current_day = max(current_day, start_day + days_needed)
            else:
                # Find next available days for non-fixed cities
                while current_day in used_days:
                    current_day += 1
                end_day = current_day + days_needed - 1
                # Check if exceeds 24 days
                if end_day > 24:
                    valid = False
                    break
                # Add to itinerary
                itinerary.append({
                    "day_range": f"Day {current_day}-{end_day}",
                    "place": city
                })
                # Mark days as used
                for day in range(current_day, end_day + 1):
                    used_days.add(day)
                prev_city = city
                current_day = end_day + 1

        # Check if exactly 24 days are covered and all cities included
        if valid and len(used_days) == 24 and len(itinerary) == len(cities):
            # Output the itinerary
            print(json.dumps({"itinerary": itinerary}, indent=2))
            return

    # If no valid itinerary found
    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()