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
    
    # First place constrained cities in their fixed positions
    itinerary = []
    occupied_days = set()
    
    # Add constrained cities to itinerary first
    for city, (start, end) in constraints.items():
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })
        occupied_days.update(range(start, end + 1))
    
    # Now handle unconstrained cities
    unconstrained_cities = [city for city in cities if city not in constraints]
    
    # Find available slots between constrained cities
    all_days = set(range(1, 26))
    available_days = sorted(all_days - occupied_days)
    
    # Group available days into continuous blocks
    day_blocks = []
    current_block = []
    
    for day in available_days:
        if not current_block or day == current_block[-1] + 1:
            current_block.append(day)
        else:
            day_blocks.append(current_block)
            current_block = [day]
    if current_block:
        day_blocks.append(current_block)
    
    # Assign unconstrained cities to available blocks
    remaining_cities = unconstrained_cities.copy()
    city_order = sorted(remaining_cities, key=lambda x: -cities[x])  # Start with longest stays
    
    for city in city_order:
        days_needed = cities[city]
        placed = False
        
        # Try to place in available blocks
        for block in day_blocks:
            if len(block) >= days_needed:
                start_day = block[0]
                end_day = start_day + days_needed - 1
                
                # Check flight connections
                if not itinerary:  # First city to place
                    # Can start anywhere
                    pass
                else:
                    # Need to find a connection from previous city
                    prev_city = itinerary[-1]['place']
                    if city not in flight_graph.get(prev_city, []):
                        continue
                
                # Place the city
                itinerary.append({
                    "day_range": f"Day {start_day}-{end_day}",
                    "place": city
                })
                
                # Update available days
                for d in range(start_day, end_day + 1):
                    if d in available_days:
                        available_days.remove(d)
                
                # Rebuild day blocks
                day_blocks = []
                current_block = []
                for day in available_days:
                    if not current_block or day == current_block[-1] + 1:
                        current_block.append(day)
                    else:
                        day_blocks.append(current_block)
                        current_block = [day]
                if current_block:
                    day_blocks.append(current_block)
                
                placed = True
                break
        
        if not placed:
            # Try to squeeze between existing cities
            for i in range(len(itinerary) - 1):
                prev_end = int(itinerary[i]['day_range'].split('-')[1])
                next_start = int(itinerary[i+1]['day_range'].split('-')[0][4:])
                available = next_start - prev_end - 1
                if available >= days_needed:
                    start_day = prev_end + 1
                    end_day = start_day + days_needed - 1
                    
                    # Check flight connections
                    prev_city = itinerary[i]['place']
                    if city not in flight_graph.get(prev_city, []):
                        continue
                    
                    # Check connection to next city
                    next_city = itinerary[i+1]['place']
                    if next_city not in flight_graph.get(city, []):
                        continue
                    
                    # Place the city
                    new_entry = {
                        "day_range": f"Day {start_day}-{end_day}",
                        "place": city
                    }
                    itinerary.insert(i+1, new_entry)
                    placed = True
                    break
            
            if not placed:
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
    
    # Verify all cities are included
    if len(itinerary) != len(cities):
        print(json.dumps({"itinerary": []}))
        return
    
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()