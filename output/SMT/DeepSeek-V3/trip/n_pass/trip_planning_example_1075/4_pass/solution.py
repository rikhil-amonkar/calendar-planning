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
    
    # Fixed events
    # Edinburgh show from day 5 to 8
    for day in range(5, 9):
        itinerary.append({"day_range": f"Day {day}", "place": "Edinburgh"})
    
    # Wedding in Split between day 19 and 23
    # Let's place Split from day 19 to 23
    for day in range(19, 24):
        itinerary.append({"day_range": f"Day {day}", "place": "Split"})
    
    # Remaining days to allocate
    allocated_days = set(range(5, 9)) | set(range(19, 24))
    remaining_days = [day for day in range(1, total_days + 1) if day not in allocated_days]
    
    # Cities to allocate (excluding Edinburgh and Split)
    cities_to_allocate = {city: days for city, days in cities.items() if city not in ["Edinburgh", "Split"]}
    
    # Current city (start with first available city)
    current_city = "Reykjavik"
    current_stay = 0
    
    for day in remaining_days:
        if current_stay >= cities_to_allocate[current_city]:
            # Need to fly to next city
            possible_destinations = [city for city in direct_flights[current_city] 
                                   if cities_to_allocate[city] > 0]
            if not possible_destinations:
                break  # no valid destinations left
            
            next_city = possible_destinations[0]
            itinerary.append({"day_range": f"Day {day}", "place": current_city})
            itinerary.append({"day_range": f"Day {day}", "place": next_city})
            current_city = next_city
            current_stay = 1
        else:
            itinerary.append({"day_range": f"Day {day}", "place": current_city})
            current_stay += 1
    
    # Verify all city days are allocated
    allocated = {}
    for entry in itinerary:
        day = int(entry["day_range"].split()[-1])
        city = entry["place"]
        allocated[city] = allocated.get(city, 0) + 1
    
    for city, days in cities.items():
        if allocated.get(city, 0) != days:
            return {"error": "Could not allocate all city days"}
    
    return {"itinerary": itinerary}

result = solve_itinerary()
print(json.dumps(result, indent=2))