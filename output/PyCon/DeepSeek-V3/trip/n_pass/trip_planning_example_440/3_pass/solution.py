import json

def main():
    # Cities and their required days
    cities = ["Split", "Helsinki", "Reykjavik", "Vilnius", "Geneva"]
    required_days = {
        "Split": 2,
        "Helsinki": 2, 
        "Reykjavik": 3,
        "Vilnius": 3,
        "Geneva": 6
    }
    
    # Direct flight connections (bidirectional)
    connections = {
        "Split": ["Helsinki", "Geneva", "Vilnius"],
        "Helsinki": ["Split", "Geneva", "Reykjavik", "Vilnius"],
        "Reykjavik": ["Helsinki"],
        "Vilnius": ["Helsinki", "Split"],
        "Geneva": ["Split", "Helsinki"]
    }
    
    def is_valid_itinerary(itinerary):
        """Check if itinerary meets all constraints"""
        total_days = 0
        city_days = {city: 0 for city in cities}
        
        # Track days spent in each city
        for segment in itinerary:
            place = segment["place"]
            day_range = segment["day_range"]
            
            # Parse day range
            if "-" in day_range:
                start, end = map(int, day_range.replace("Day ", "").split("-"))
                days = end - start + 1
            else:
                days = 1
            
            city_days[place] += days
            total_days += days
        
        # Check total days (should be 12)
        if total_days != 12:
            return False
        
        # Check required days for each city
        for city, required in required_days.items():
            if city_days[city] != required:
                return False
        
        # Check travel constraints between segments
        for i in range(len(itinerary) - 1):
            current_city = itinerary[i]["place"]
            next_city = itinerary[i+1]["place"]
            
            if next_city not in connections[current_city]:
                return False
        
        # Check wedding constraint (Reykjavik on days 10-12)
        wedding_days = []
        current_day = 1
        for segment in itinerary:
            place = segment["place"]
            day_range = segment["day_range"]
            
            if "-" in day_range:
                start, end = map(int, day_range.replace("Day ", "").split("-"))
                days = list(range(start, end + 1))
            else:
                days = [int(day_range.replace("Day ", ""))]
            
            if place == "Reykjavik":
                wedding_days.extend(days)
            
            current_day = end + 1 if "-" in day_range else current_day + 1
        
        wedding_met = any(day in wedding_days for day in [10, 11, 12])
        if not wedding_met:
            return False
        
        # Check relatives constraint (Vilnius on days 7-9)
        relatives_days = []
        current_day = 1
        for segment in itinerary:
            place = segment["place"]
            day_range = segment["day_range"]
            
            if "-" in day_range:
                start, end = map(int, day_range.replace("Day ", "").split("-"))
                days = list(range(start, end + 1))
            else:
                days = [int(day_range.replace("Day ", ""))]
            
            if place == "Vilnius":
                relatives_days.extend(days)
            
            current_day = end + 1 if "-" in day_range else current_day + 1
        
        relatives_met = any(day in relatives_days for day in [7, 8, 9])
        if not relatives_met:
            return False
        
        return True
    
    def generate_itinerary_segments(remaining_days, remaining_cities, current_city, path):
        """Generate possible itineraries using backtracking"""
        if remaining_days == 0 and not remaining_cities:
            # Found a complete itinerary
            if is_valid_itinerary(path):
                return path
            return None
        
        if remaining_days == 0 or not remaining_cities:
            return None
        
        # Try staying in current city for various durations
        for duration in range(1, min(remaining_days, max(remaining_cities.values())) + 1):
            if current_city in remaining_cities and duration <= remaining_cities[current_city]:
                new_remaining_cities = remaining_cities.copy()
                new_remaining_cities[current_city] -= duration
                if new_remaining_cities[current_city] == 0:
                    del new_remaining_cities[current_city]
                
                current_day = 13 - remaining_days + 1
                day_range = f"Day {current_day}" if duration == 1 else f"Day {current_day}-{current_day + duration - 1}"
                
                new_path = path + [{"day_range": day_range, "place": current_city}]
                
                # If we've used all days for this city, move to connected cities
                if current_city not in new_remaining_cities:
                    for next_city in connections[current_city]:
                        if next_city in new_remaining_cities:
                            result = generate_itinerary_segments(
                                remaining_days - duration, 
                                new_remaining_cities, 
                                next_city, 
                                new_path
                            )
                            if result:
                                return result
                else:
                    # Continue in same city
                    result = generate_itinerary_segments(
                        remaining_days - duration,
                        new_remaining_cities,
                        current_city,
                        new_path
                    )
                    if result:
                        return result
        
        return None
    
    # Try starting from each city
    for start_city in cities:
        result = generate_itinerary_segments(12, required_days.copy(), start_city, [])
        if result:
            print(json.dumps({"itinerary": result}, indent=2))
            return
    
    print(json.dumps({"error": "No valid itinerary found"}))

if __name__ == "__main__":
    main()