import json

def solve_itinerary():
    # Define the problem
    cities = {
        "Manchester": 3,
        "Istanbul": 7,
        "Venice": 7,
        "Krakow": 6,
        "Lyon": 2
    }
    
    total_days = 21
    
    # Direct flight connections
    connections = {
        "Manchester": ["Venice", "Istanbul", "Krakow"],
        "Venice": ["Manchester", "Istanbul", "Lyon"],
        "Istanbul": ["Manchester", "Venice", "Krakow", "Lyon"],
        "Krakow": ["Istanbul", "Manchester"],
        "Lyon": ["Venice", "Istanbul"]
    }
    
    def is_valid_day_assignment(day_assignments):
        """Check if day assignments are valid"""
        # Check all cities are assigned
        if len(day_assignments) != len(cities):
            return False
            
        # Check no overlapping days
        occupied_days = set()
        for city, (start_day, duration) in day_assignments.items():
            end_day = start_day + duration - 1
            for day in range(start_day, end_day + 1):
                if day in occupied_days:
                    return False
                occupied_days.add(day)
        
        # Check total days
        if max(occupied_days) > total_days:
            return False
            
        # Check Manchester constraint (days 1-3)
        if "Manchester" in day_assignments:
            man_start, man_duration = day_assignments["Manchester"]
            man_end = man_start + man_duration - 1
            if man_start < 1 or man_end > 3:
                return False
                
        # Check Venice constraint (days 3-9)
        if "Venice" in day_assignments:
            ven_start, ven_duration = day_assignments["Venice"]
            ven_end = ven_start + ven_duration - 1
            if ven_start < 3 or ven_end > 9:
                return False
                
        return True
    
    def find_valid_itinerary(path, day_assignments, used_days):
        """Recursively find valid day assignments for a given path"""
        if len(day_assignments) == len(path):
            # All cities assigned, check if valid
            if is_valid_day_assignment(day_assignments):
                # Build itinerary
                itinerary = []
                for city in path:
                    start_day, duration = day_assignments[city]
                    end_day = start_day + duration - 1
                    if start_day == end_day:
                        day_range = f"Day {start_day}"
                    else:
                        day_range = f"Day {start_day}-{end_day}"
                    itinerary.append({
                        "day_range": day_range,
                        "place": city
                    })
                return itinerary
            return None
            
        # Get next city to assign
        current_city = path[len(day_assignments)]
        duration = cities[current_city]
        
        # Try all possible start days
        for start_day in range(1, total_days - duration + 2):
            # Check if this day range is available
            end_day = start_day + duration - 1
            days_conflict = False
            for day in range(start_day, end_day + 1):
                if day in used_days:
                    days_conflict = True
                    break
                    
            if days_conflict:
                continue
                
            # Check constraints for specific cities
            if current_city == "Manchester":
                if start_day < 1 or end_day > 3:
                    continue
            elif current_city == "Venice":
                if start_day < 3 or end_day > 9:
                    continue
                    
            # Try this assignment
            day_assignments[current_city] = (start_day, duration)
            for day in range(start_day, end_day + 1):
                used_days.add(day)
                
            result = find_valid_itinerary(path, day_assignments, used_days)
            if result:
                return result
                
            # Backtrack
            del day_assignments[current_city]
            for day in range(start_day, end_day + 1):
                used_days.remove(day)
                
        return None
    
    # Generate all possible valid paths
    def generate_paths(current_path, remaining, all_paths):
        if not remaining:
            all_paths.append(current_path[:])
            return
            
        for city in remaining:
            if not current_path or city in connections[current_path[-1]]:
                new_remaining = [c for c in remaining if c != city]
                generate_paths(current_path + [city], new_remaining, all_paths)
    
    all_paths = []
    generate_paths([], list(cities.keys()), all_paths)
    
    # Try each path with different day assignments
    for path in all_paths:
        itinerary = find_valid_itinerary(path, {}, set())
        if itinerary:
            return {"itinerary": itinerary}
    
    return {"error": "No valid itinerary found"}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, indent=2))