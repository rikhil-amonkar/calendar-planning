import json

def main():
    cities = ["Split", "Helsinki", "Reykjavik", "Vilnius", "Geneva"]
    durations = {
        "Split": 2,
        "Helsinki": 2,
        "Reykjavik": 3,
        "Vilnius": 3,
        "Geneva": 6
    }
    
    # Direct flight connections (bidirectional)
    connections = [
        ("Split", "Helsinki"),
        ("Geneva", "Split"),
        ("Geneva", "Helsinki"),
        ("Helsinki", "Reykjavik"),
        ("Vilnius", "Helsinki"),
        ("Split", "Vilnius")
    ]
    allowed_pairs = set()
    for a, b in connections:
        allowed_pairs.add((a, b))
        allowed_pairs.add((b, a))
    
    # Backtracking to find valid itinerary
    def backtrack(order, current_day, itinerary, used, last_city):
        if len(order) == 5:
            # Check if total days is 12
            if current_day - 1 == 12:  # current_day is next day after last
                # Check event constraints
                reykjavik_days = [day for city, days in itinerary for day in days if city == "Reykjavik"]
                vilnius_days = [day for city, days in itinerary for day in days if city == "Vilnius"]
                if any(10 <= day <= 12 for day in reykjavik_days) and any(7 <= day <= 9 for day in vilnius_days):
                    return itinerary
            return None
        
        for city in cities:
            if city in used and used[city]:
                continue
            # Check flight connection if not first city
            if last_city and (last_city, city) not in allowed_pairs:
                continue
                
            # Calculate stay days for this city
            stay_days = list(range(current_day, current_day + durations[city]))
            new_itinerary = itinerary + [(city, stay_days)]
            used[city] = True
            # Next city starts the day after this city's last day
            result = backtrack(order + [city], current_day + durations[city], new_itinerary, used, city)
            if result is not None:
                return result
            used[city] = False
            
        return None
    
    # Try starting from each city
    for start_city in cities:
        used = {city: False for city in cities}
        used[start_city] = True
        stay_days = list(range(1, 1 + durations[start_city]))
        result = backtrack([start_city], 1 + durations[start_city], [(start_city, stay_days)], used, start_city)
        if result is not None:
            # Format the itinerary
            formatted = []
            for city, days_list in result:
                for day in days_list:
                    formatted.append({"day": day, "place": city})
            print(json.dumps({"itinerary": formatted}, indent=2))
            return
    
    print("No solution found")

if __name__ == "__main__":
    main()