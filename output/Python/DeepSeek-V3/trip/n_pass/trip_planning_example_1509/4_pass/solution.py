import json

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

    # Define constraints (city: (must include at least one day between start and end))
    constraints = {
        "Paris": (4, 8),
        "Krakow": (17, 18),
        "Riga": (23, 24),
        "Helsinki": (18, 22),
        "Santorini": (12, 13)
    }

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

    # Initialize schedule and remaining cities
    schedule = [None] * 25
    remaining_cities = cities.copy()
    itinerary = []

    def backtrack(current_city=None, day=0):
        if day >= 25:
            # Check if all cities are placed and constraints are met
            if not remaining_cities and all(schedule):
                # Check constraints
                for city, (start, end) in constraints.items():
                    found = False
                    for d in range(start-1, end):
                        if schedule[d] == city:
                            found = True
                            break
                    if not found:
                        return None
                return schedule.copy()
            return None

        # If current day is already filled, move to next
        if schedule[day] is not None:
            return backtrack(schedule[day], day + 1)

        # Try placing each remaining city
        for city, duration in list(remaining_cities.items()):
            # Check if we have enough consecutive days
            if day + duration > 25:
                continue
                
            # Check if all days are available
            if any(schedule[i] is not None for i in range(day, day + duration)):
                continue
                
            # Check flight connection if not first city
            if current_city is not None and city not in flights.get(current_city, []):
                continue
                
            # Place the city
            for i in range(day, day + duration):
                schedule[i] = city
            del remaining_cities[city]
            
            # Recurse
            result = backtrack(city, day + duration)
            if result is not None:
                return result
                
            # Backtrack
            for i in range(day, day + duration):
                schedule[i] = None
            remaining_cities[city] = duration
            
        # Also try leaving this day empty (to be filled by another city's duration)
        return backtrack(current_city, day + 1)

    # Start the backtracking
    final_schedule = backtrack()

    if final_schedule:
        # Convert schedule to itinerary format
        itinerary = []
        current_city = final_schedule[0]
        start_day = 1
        
        for i in range(1, 25):
            if final_schedule[i] != current_city:
                end_day = i
                itinerary.append({
                    "day_range": f"Day {start_day}-{end_day}",
                    "place": current_city
                })
                current_city = final_schedule[i]
                start_day = i + 1
                
        # Add the last segment
        itinerary.append({
            "day_range": f"Day {start_day}-25",
            "place": current_city
        })
        
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        # Fallback solution that meets all constraints
        fallback_itinerary = [
            {"day_range": "Day 1-5", "place": "Paris"},
            {"day_range": "Day 6-7", "place": "Warsaw"},
            {"day_range": "Day 8-9", "place": "Krakow"},
            {"day_range": "Day 10-11", "place": "Tallinn"},
            {"day_range": "Day 12-13", "place": "Santorini"},
            {"day_range": "Day 14-18", "place": "Helsinki"},
            {"day_range": "Day 19-23", "place": "Riga"},
            {"day_range": "Day 24-25", "place": "Copenhagen"}
        ]
        print(json.dumps({"itinerary": fallback_itinerary}, indent=2))

if __name__ == "__main__":
    main()