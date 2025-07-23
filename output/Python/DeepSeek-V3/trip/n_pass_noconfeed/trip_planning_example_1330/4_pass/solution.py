import json
from collections import defaultdict

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
    
    # Fixed constraints (city: (start_day, end_day))
    constraints = {
        "Brussels": (21, 22),
        "Copenhagen": (18, 21),
        "Nice": (9, 11),
        "Naples": (22, 25)
    }
    
    # Initialize itinerary with constrained cities
    itinerary = []
    occupied_days = set()
    
    # Add constrained cities first
    for city, (start, end) in constraints.items():
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })
        occupied_days.update(range(start, end + 1))
    
    # Sort itinerary by day range
    itinerary.sort(key=lambda x: int(x['day_range'].split('-')[0][4:]))
    
    # Find all available days (1-25)
    all_days = set(range(1, 26))
    available_days = sorted(all_days - occupied_days)
    
    # Unconstrained cities to place
    unconstrained_cities = [city for city in cities if city not in constraints]
    
    # Sort cities by duration (longest first) to place harder ones first
    unconstrained_cities_sorted = sorted(unconstrained_cities, key=lambda x: -cities[x])
    
    # Try to place each unconstrained city
    for city in unconstrained_cities_sorted:
        days_needed = cities[city]
        placed = False
        
        # Try to place before first constrained city
        first_constrained_day = min(occupied_days)
        if first_constrained_day - 1 >= days_needed:
            start_day = first_constrained_day - days_needed
            end_day = start_day + days_needed - 1
            
            # Check if this block is available
            if all(day in available_days for day in range(start_day, end_day + 1)):
                # Check flight connection if not first city
                if itinerary:
                    prev_city = None
                    # Find the city that would be before this placement
                    for entry in itinerary:
                        entry_end = int(entry['day_range'].split('-')[1])
                        if entry_end < start_day:
                            prev_city = entry['place']
                    
                    if prev_city and city not in flight_graph.get(prev_city, []):
                        continue
                
                # Place the city
                itinerary.append({
                    "day_range": f"Day {start_day}-{end_day}",
                    "place": city
                })
                occupied_days.update(range(start_day, end_day + 1))
                placed = True
        
        if not placed:
            # Try to place between constrained cities
            for i in range(len(itinerary) - 1):
                current_end = int(itinerary[i]['day_range'].split('-')[1])
                next_start = int(itinerary[i+1]['day_range'].split('-')[0][4:])
                gap = next_start - current_end - 1
                
                if gap >= days_needed:
                    # Check flight connections
                    prev_city = itinerary[i]['place']
                    next_city = itinerary[i+1]['place']
                    
                    if (city in flight_graph.get(prev_city, []) and (next_city in flight_graph.get(city, [])):
                        start_day = current_end + 1
                        end_day = start_day + days_needed - 1
                        
                        itinerary.insert(i+1, {
                            "day_range": f"Day {start_day}-{end_day}",
                            "place": city
                        })
                        occupied_days.update(range(start_day, end_day + 1))
                        placed = True
                        break
        
        if not placed:
            # Try to place after last constrained city
            last_constrained_day = max(occupied_days)
            if 25 - last_constrained_day >= days_needed:
                start_day = last_constrained_day + 1
                end_day = start_day + days_needed - 1
                
                # Check flight connection
                if itinerary:
                    last_city = itinerary[-1]['place']
                    if city not in flight_graph.get(last_city, []):
                        continue
                
                itinerary.append({
                    "day_range": f"Day {start_day}-{end_day}",
                    "place": city
                })
                occupied_days.update(range(start_day, end_day + 1))
                placed = True
    
    # Final check if all cities are placed
    if len(itinerary) != len(cities):
        print(json.dumps({"itinerary": []}))
        return
    
    # Sort itinerary by day range
    itinerary.sort(key=lambda x: int(x['day_range'].split('-')[0][4:]))
    
    # Verify all flight connections
    for i in range(len(itinerary) - 1):
        current = itinerary[i]['place']
        next_city = itinerary[i+1]['place']
        if next_city not in flight_graph.get(current, []):
            print(json.dumps({"itinerary": []}))
            return
    
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()