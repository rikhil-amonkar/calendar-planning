import json

def main():
    # Define the cities and their required days
    cities = {
        "Salzburg": 2,
        "Venice": 5,
        "Bucharest": 4,
        "Brussels": 2,
        "Hamburg": 4,
        "Copenhagen": 4,
        "Nice": 3,
        "Zurich": 5,
        "Naples": 4
    }
    
    # Define the direct flights as a graph
    flight_graph = {
        "Zurich": ["Brussels", "Nice", "Naples", "Copenhagen", "Venice", "Bucharest", "Hamburg"],
        "Brussels": ["Zurich", "Venice", "Bucharest", "Hamburg", "Nice", "Copenhagen", "Naples"],
        "Bucharest": ["Copenhagen", "Hamburg", "Brussels", "Naples", "Zurich"],
        "Venice": ["Brussels", "Naples", "Copenhagen", "Zurich", "Nice", "Hamburg"],
        "Nice": ["Zurich", "Hamburg", "Venice", "Brussels", "Naples", "Copenhagen"],
        "Hamburg": ["Nice", "Bucharest", "Brussels", "Zurich", "Copenhagen", "Venice", "Salzburg"],
        "Copenhagen": ["Bucharest", "Venice", "Zurich", "Hamburg", "Brussels", "Naples", "Nice"],
        "Naples": ["Zurich", "Venice", "Bucharest", "Brussels", "Copenhagen", "Nice"],
        "Salzburg": ["Hamburg"]
    }
    
    # Define the constraints (city, start_day, end_day)
    constraints = {
        "Brussels": (21, 22),
        "Copenhagen": (18, 21),
        "Nice": (9, 11),
        "Naples": (22, 25)
    }
    
    # Cities with constraints must be handled specially
    constrained_cities = set(constraints.keys())
    
    # Helper function to check if a placement is valid
    def is_valid_placement(itinerary, city, start_day):
        days_needed = cities[city]
        end_day = start_day + days_needed - 1
        
        # Check if it exceeds total days
        if end_day > 25:
            return False
        
        # Check constraints if this city has any
        if city in constraints:
            const_start, const_end = constraints[city]
            if not (start_day <= const_start and end_day >= const_end):
                return False
        
        # Check overlap with existing cities
        for entry in itinerary:
            existing_start = int(entry['day_range'].split('-')[0][4:])
            existing_end = int(entry['day_range'].split('-')[1])
            if not (end_day < existing_start or start_day > existing_end):
                return False
        
        # Check flight connection with previous city if not first city
        if itinerary:
            prev_city = itinerary[-1]['place']
            if city not in flight_graph.get(prev_city, []):
                return False
        
        return True
    
    # Backtracking function to find valid itinerary
    def backtrack(current_itinerary, remaining_cities, used_days):
        if not remaining_cities:
            if used_days == 25:
                return current_itinerary
            return None
        
        # Try cities in order, prioritizing constrained ones first
        for city in sorted(remaining_cities, key=lambda x: x in constrained_cities, reverse=True):
            # Try placing this city in all possible positions
            for start_day in range(1, 26 - cities[city] + 1):
                if is_valid_placement(current_itinerary, city, start_day):
                    end_day = start_day + cities[city] - 1
                    new_entry = {
                        "day_range": f"Day {start_day}-{end_day}",
                        "place": city
                    }
                    result = backtrack(
                        current_itinerary + [new_entry],
                        [c for c in remaining_cities if c != city],
                        max(used_days, end_day)
                    )
                    if result:
                        return result
        return None
    
    # Start with all cities
    all_cities = list(cities.keys())
    valid_itinerary = backtrack([], all_cities, 0)
    
    if valid_itinerary:
        print(json.dumps({"itinerary": valid_itinerary}))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()