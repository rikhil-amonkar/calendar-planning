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

    # Process fixed constraints first
    used_days = set()
    fixed_itinerary = []
    prev_city = None
    
    for city, start_day, end_day in fixed_constraints:
        days_needed = city_days[city]
        actual_end_day = start_day + days_needed - 1
        
        # Check if the stay fits in the allocated days
        if actual_end_day > end_day:
            print(json.dumps({"itinerary": []}))
            return
            
        # Check if days are available
        for day in range(start_day, actual_end_day + 1):
            if day in used_days:
                print(json.dumps({"itinerary": []}))
                return
                
        # Add to itinerary
        fixed_itinerary.append({
            "day_range": f"Day {start_day}-{actual_end_day}",
            "place": city
        })
        
        # Mark days as used
        for day in range(start_day, actual_end_day + 1):
            used_days.add(day)
            
        prev_city = city

    # Remaining cities to schedule
    remaining_cities = [city for city in city_days if city not in {fc[0] for fc in fixed_constraints}]
    
    # Try all possible orders for remaining cities
    for perm in permutations(remaining_cities):
        itinerary = fixed_itinerary.copy()
        current_used_days = used_days.copy()
        current_prev_city = prev_city
        valid = True
        
        for city in perm:
            days_needed = city_days[city]
            
            # Check flight connection if not first city
            if current_prev_city and city not in direct_flights.get(current_prev_city, []):
                valid = False
                break
                
            # Find earliest available consecutive days
            start_day = 1
            while True:
                # Find first available start day
                while start_day in current_used_days:
                    start_day += 1
                    
                end_day = start_day + days_needed - 1
                if end_day > 24:
                    valid = False
                    break
                    
                # Check if all days in range are available
                all_available = True
                for day in range(start_day, end_day + 1):
                    if day in current_used_days:
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
                current_used_days.add(day)
                
            current_prev_city = city
            
        # Check if all 24 days are covered
        if valid and len(current_used_days) == 24:
            # Sort itinerary by start day
            itinerary.sort(key=lambda x: int(x['day_range'].split('-')[0].split(' ')[1]))
            print(json.dumps({"itinerary": itinerary}, indent=2))
            return
            
    # If no valid itinerary found
    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()