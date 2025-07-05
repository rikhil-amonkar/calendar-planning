import json

def solve_itinerary():
    cities = {
        "Vienna": 4,
        "Lyon": 3,
        "Edinburgh": 4,
        "Reykjavik": 5,
        "Stuttgart": 5,
        "Manchester": 2,
        "Split": 5,
        "Prague": 4
    }
    
    direct_flights = {
        "Reykjavik": ["Stuttgart", "Vienna", "Prague"],
        "Stuttgart": ["Reykjavik", "Split", "Vienna", "Edinburgh", "Manchester"],
        "Vienna": ["Stuttgart", "Prague", "Manchester", "Lyon", "Split", "Reykjavik"],
        "Prague": ["Manchester", "Edinburgh", "Vienna", "Split", "Lyon", "Reykjavik"],
        "Edinburgh": ["Prague", "Stuttgart"],
        "Manchester": ["Prague", "Vienna", "Split", "Stuttgart"],
        "Split": ["Stuttgart", "Manchester", "Prague", "Vienna", "Lyon"],
        "Lyon": ["Vienna", "Split", "Prague"]
    }
    
    total_days = 25
    itinerary = []
    city_days_used = {city: 0 for city in cities}
    
    # Fixed events
    # Edinburgh show from day 5 to 8
    for day in range(5, 9):
        itinerary.append({"day_range": f"Day {day}", "place": "Edinburgh"})
        city_days_used["Edinburgh"] += 1
    
    # Wedding in Split between day 19 and 23
    for day in range(19, 24):
        itinerary.append({"day_range": f"Day {day}", "place": "Split"})
        city_days_used["Split"] += 1
    
    # Remaining days to allocate
    allocated_days = set(range(5, 9)) | set(range(19, 24))
    remaining_days = [day for day in range(1, total_days + 1) if day not in allocated_days]
    
    # Current city (start with first available city)
    current_city = "Reykjavik"
    
    for day in remaining_days:
        # If we've used all days for current city, find next city
        if city_days_used[current_city] >= cities[current_city]:
            # Find cities we can fly to that still need days
            possible_destinations = [
                city for city in direct_flights[current_city]
                if city_days_used[city] < cities[city]
            ]
            
            if not possible_destinations:
                break  # no valid destinations left
            
            next_city = possible_destinations[0]
            
            # Add flight day (both departure and arrival)
            itinerary.append({"day_range": f"Day {day}", "place": current_city})
            itinerary.append({"day_range": f"Day {day}", "place": next_city})
            
            # Update days used (counts for both cities)
            city_days_used[current_city] += 1
            city_days_used[next_city] += 1
            
            current_city = next_city
        else:
            itinerary.append({"day_range": f"Day {day}", "place": current_city})
            city_days_used[current_city] += 1
    
    # Verify all city days are allocated correctly
    for city, required in cities.items():
        if city_days_used[city] != required:
            return {"error": f"Failed to allocate enough days for {city}"}
    
    # Verify total days
    if len(itinerary) != total_days + sum(cities.values()) - 25:  # account for flight days
        return {"error": "Incorrect total number of days"}
    
    return {"itinerary": itinerary}

result = solve_itinerary()
print(json.dumps(result, indent=2))