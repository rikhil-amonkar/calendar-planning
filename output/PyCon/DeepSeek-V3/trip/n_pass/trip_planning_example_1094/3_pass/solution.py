import json

def main():
    cities = ["Vienna", "Barcelona", "Edinburgh", "Krakow", "Riga", "Hamburg", "Paris", "Stockholm"]
    
    # Define flight connections
    flights = {
        "Hamburg": ["Stockholm", "Vienna", "Barcelona", "Edinburgh", "Paris"],
        "Stockholm": ["Hamburg", "Vienna", "Edinburgh", "Krakow", "Barcelona", "Paris", "Riga"],
        "Vienna": ["Stockholm", "Hamburg", "Barcelona", "Krakow", "Riga", "Paris"],
        "Edinburgh": ["Paris", "Stockholm", "Riga", "Barcelona", "Krakow", "Hamburg"],
        "Riga": ["Barcelona", "Paris", "Stockholm", "Edinburgh", "Hamburg", "Vienna"],
        "Barcelona": ["Riga", "Krakow", "Edinburgh", "Stockholm", "Hamburg", "Vienna", "Paris"],
        "Krakow": ["Barcelona", "Stockholm", "Edinburgh", "Paris", "Vienna"],
        "Paris": ["Edinburgh", "Riga", "Krakow", "Stockholm", "Hamburg", "Barcelona", "Vienna"]
    }
    
    # Duration for each city
    durations = {
        "Vienna": 4,
        "Barcelona": 2,
        "Edinburgh": 4,
        "Krakow": 3,
        "Riga": 4,
        "Hamburg": 2,
        "Paris": 2,
        "Stockholm": 2
    }
    
    # Fixed constraints
    fixed_dates = {
        "Paris": (1, 2),  # Days 1-2
        "Hamburg": (10, 11),  # Days 10-11
    }
    
    # Range constraints
    range_constraints = {
        "Edinburgh": (12, 15),  # Between day 12 and day 15
        "Stockholm": (15, 16),  # Between day 15 and day 16
    }
    
    def is_valid_schedule(schedule):
        """Check if all visits fit within the 16-day period without overlap"""
        days = [False] * 17  # Index 0 unused, days 1-16
        
        for city, start_day in schedule.items():
            end_day = start_day + durations[city] - 1
            if end_day > 16:
                return False
            
            # Check for overlap
            for day in range(start_day, end_day + 1):
                if days[day]:
                    return False
                days[day] = True
        
        # Check fixed dates - only for cities that are already scheduled
        for city, (fixed_start, fixed_end) in fixed_dates.items():
            if city in schedule:
                if schedule[city] != fixed_start:
                    return False
                if schedule[city] + durations[city] - 1 != fixed_end:
                    return False
        
        # Check range constraints - only for cities that are already scheduled
        for city, (min_day, max_day) in range_constraints.items():
            if city in schedule:
                start = schedule[city]
                end = start + durations[city] - 1
                if start < min_day or end > max_day:
                    return False
        
        return True
    
    def has_valid_flight_path(schedule):
        """Check if there's a valid flight sequence between all cities"""
        # Create timeline
        timeline = []
        for city, start in schedule.items():
            end = start + durations[city] - 1
            timeline.append((start, end, city))
        timeline.sort()
        
        # Check consecutive cities in timeline are connected
        for i in range(len(timeline) - 1):
            current_city = timeline[i][2]
            next_city = timeline[i + 1][2]
            if next_city not in flights[current_city]:
                return False
        
        return True
    
    def find_valid_schedule(current_schedule, remaining_cities):
        """Backtracking search for valid schedule"""
        if not remaining_cities:
            if has_valid_flight_path(current_schedule):
                return current_schedule
            return None
        
        city = remaining_cities[0]
        
        # Determine possible start days for this city
        if city in fixed_dates:
            possible_starts = [fixed_dates[city][0]]
        elif city in range_constraints:
            min_day, max_day = range_constraints[city]
            possible_starts = range(min_day, max_day - durations[city] + 2)
        else:
            possible_starts = range(1, 17 - durations[city] + 1)
        
        for start_day in possible_starts:
            new_schedule = current_schedule.copy()
            new_schedule[city] = start_day
            
            if is_valid_schedule(new_schedule):
                result = find_valid_schedule(new_schedule, remaining_cities[1:])
                if result:
                    return result
        
        return None
    
    # Start with fixed cities to reduce search space
    initial_schedule = {}
    remaining_cities = [city for city in cities if city not in fixed_dates]
    
    # Try different orders of remaining cities
    from itertools import permutations
    
    schedule = None
    for city_order in permutations(remaining_cities):
        full_order = list(fixed_dates.keys()) + list(city_order)
        schedule = find_valid_schedule({}, full_order)
        if schedule:
            break
    
    if not schedule:
        # If the above fails, try a more flexible approach
        schedule = find_valid_schedule({}, cities)
    
    if not schedule:
        print(json.dumps({"error": "No valid itinerary found"}))
        return
    
    # Build the itinerary
    itinerary_entries = []
    for city in cities:
        start = schedule[city]
        end = start + durations[city] - 1
        if start == end:
            day_range = f"Day {start}"
        else:
            day_range = f"Day {start}-{end}"
        itinerary_entries.append({
            "day_range": day_range,
            "place": city
        })
    
    # Sort by start day
    itinerary_entries.sort(key=lambda x: int(x["day_range"].split(" ")[1].split("-")[0]))
    
    result = {"itinerary": itinerary_entries}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()