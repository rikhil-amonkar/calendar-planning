import json
from itertools import permutations

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
        "Edinburgh": (12, 15),  # Between day 12 and day 15 (inclusive start)
        "Stockholm": (15, 16),  # Between day 15 and day 16 (inclusive start)
    }
    
    def is_city_placement_valid(city, start_day, schedule):
        """Check if placing a city at start_day is valid given current schedule"""
        end_day = start_day + durations[city] - 1
        
        # Check if it fits within 16 days
        if end_day > 16:
            return False
        
        # Check for overlap with already scheduled cities
        for other_city, other_start in schedule.items():
            other_end = other_start + durations[other_city] - 1
            if not (end_day < other_start or start_day > other_end):
                return False
        
        # Check fixed dates
        if city in fixed_dates:
            fixed_start, fixed_end = fixed_dates[city]
            if start_day != fixed_start or end_day != fixed_end:
                return False
        
        # Check range constraints
        if city in range_constraints:
            min_day, max_day = range_constraints[city]
            if start_day < min_day or end_day > max_day:
                return False
        
        return True
    
    def has_valid_flight_sequence(schedule):
        """Check if there's a valid flight sequence between consecutive cities in the timeline"""
        if len(schedule) < 2:
            return True
            
        # Create timeline of visits with start and end days
        visits = []
        for city, start in schedule.items():
            end = start + durations[city] - 1
            visits.append((start, end, city))
        visits.sort()  # Sort by start day
        
        # Check flight connections between consecutive visits
        for i in range(len(visits) - 1):
            current_city = visits[i][2]
            current_end = visits[i][1]
            next_city = visits[i + 1][2]
            next_start = visits[i + 1][0]
            
            # There must be at least one travel day between visits
            if next_start <= current_end:
                return False
            
            # Check if there's a direct flight between these cities
            if next_city not in flights[current_city]:
                return False
        
        return True
    
    def find_schedule_backtrack(schedule, remaining_cities):
        """Backtracking search for valid schedule"""
        if not remaining_cities:
            if has_valid_flight_sequence(schedule):
                return schedule
            return None
        
        city = remaining_cities[0]
        
        # Determine possible start days for this city
        if city in fixed_dates:
            possible_starts = [fixed_dates[city][0]]
        elif city in range_constraints:
            min_day, max_day = range_constraints[city]
            possible_starts = list(range(min_day, max_day - durations[city] + 2))
        else:
            # For other cities, consider all possible start days
            possible_starts = list(range(1, 17 - durations[city] + 1))
        
        for start_day in possible_starts:
            if is_city_placement_valid(city, start_day, schedule):
                new_schedule = schedule.copy()
                new_schedule[city] = start_day
                
                result = find_schedule_backtrack(new_schedule, remaining_cities[1:])
                if result:
                    return result
        
        return None
    
    # Try different orderings of cities to improve search efficiency
    remaining_cities = [city for city in cities if city not in fixed_dates]
    
    # Start with the fixed cities already placed
    initial_schedule = {}
    for city in fixed_dates:
        start_day = fixed_dates[city][0]
        initial_schedule[city] = start_day
    
    schedule = None
    # Try different permutations to find a valid schedule
    for city_order in permutations(remaining_cities):
        test_schedule = find_schedule_backtrack(initial_schedule.copy(), list(city_order))
        if test_schedule:
            schedule = test_schedule
            break
    
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